//! 端到端测试：用 javac 编译小程序，在进程内跑调试适配器，按 DAP 请求驱动一次完整的调试。
//! 找不到带 javac 的 JDK 时跳过。

use std::{
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::{PoisonError, RwLock, RwLockReadGuard, RwLockWriteGuard},
    thread::JoinHandle,
    time::Duration,
};

use crossbeam_channel::{Receiver, Sender};
use serde_json::{json, Value};

const TIMEOUT: Duration = Duration::from_secs(60);

/// `bin` 下的可执行文件（Windows 上带 `.exe`）。
fn tool(jdk: &Path, name: &str) -> PathBuf {
    jdk.join("bin")
        .join(format!("{name}{}", std::env::consts::EXE_SUFFIX))
}

fn jdk_home() -> Option<PathBuf> {
    let has_javac = |home: &Path| tool(home, "javac").is_file();
    std::env::var_os("JAVA_HOME")
        .map(PathBuf::from)
        .filter(|home| has_javac(home))
        .or_else(|| {
            project_model::discover_jdk(None)
                .map(|jdk| jdk.home)
                .filter(|home| has_javac(home))
        })
}

macro_rules! require_jdk {
    () => {
        match jdk_home() {
            Some(home) => home,
            None => {
                eprintln!("没有找到带 javac 的 JDK，跳过");
                return;
            }
        }
    };
}

fn temp_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("ja-dap-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

fn javac(jdk: &Path, out: &Path, sources: &[&Path]) {
    // JDK 8 的 javac 不会自己创建输出目录
    std::fs::create_dir_all(out).unwrap();
    let status = Command::new(tool(jdk, "javac"))
        .args(["-encoding", "UTF-8"])
        .arg("-g")
        .arg("-d")
        .arg(out)
        .args(sources)
        .status()
        .expect("无法运行 javac");
    assert!(status.success(), "javac 失败");
}

fn java(jdk: &Path) -> String {
    tool(jdk, "java").to_string_lossy().into_owned()
}

/// 界面语言是进程级的设置，每个会话在 `initialize` 时改它：用英文（不声明 locale 或 `en`）的会话
/// 可以同时跑，用中文的会话独占。
static LANG_LOCK: RwLock<()> = RwLock::new(());

/// 进程内的调试适配器加一个简单的 DAP 客户端。
struct Client {
    tx: Option<Sender<Value>>,
    rx: Receiver<Value>,
    seq: i64,
    backlog: Vec<Value>,
    output: String,
    /// 收到的全部消息
    transcript: Vec<Value>,
    thread: Option<JoinHandle<()>>,
    _shared_lang: Option<RwLockReadGuard<'static, ()>>,
    _exclusive_lang: Option<RwLockWriteGuard<'static, ()>>,
}

impl Client {
    fn start() -> Client {
        Client::start_with_locale(None)
    }

    /// `locale`：`initialize` 里客户端声明的界面语言。
    fn start_with_locale(locale: Option<&str>) -> Client {
        let english = locale.is_none_or(|locale| !locale.starts_with("zh"));
        let (shared_lang, exclusive_lang) = if english {
            let guard = LANG_LOCK.read().unwrap_or_else(PoisonError::into_inner);
            (Some(guard), None)
        } else {
            let guard = LANG_LOCK.write().unwrap_or_else(PoisonError::into_inner);
            (None, Some(guard))
        };
        let (tx, requests) = crossbeam_channel::unbounded();
        let (out_tx, rx) = crossbeam_channel::unbounded();
        let thread = std::thread::spawn(move || {
            dap::serve(requests, move |message: &Value| {
                let _ = out_tx.send(message.clone());
            })
        });
        let mut client = Client {
            tx: Some(tx),
            rx,
            seq: 0,
            backlog: Vec::new(),
            output: String::new(),
            transcript: Vec::new(),
            thread: Some(thread),
            _shared_lang: shared_lang,
            _exclusive_lang: exclusive_lang,
        };
        let caps = client.request(
            "initialize",
            json!({
                "adapterID": "java",
                "linesStartAt1": true,
                "columnsStartAt1": true,
                "locale": locale,
            }),
        );
        assert_eq!(caps["supportsConfigurationDoneRequest"], json!(true));
        assert_eq!(caps["supportsCompletionsRequest"], json!(true));
        assert_eq!(caps["completionTriggerCharacters"], json!(["."]));
        client
    }

    fn next(&mut self) -> Value {
        let message = self.rx.recv_timeout(TIMEOUT).unwrap_or_else(|_| {
            panic!(
                "等待调试适配器的消息超时。已收到但未处理的消息: {:#?}\n输出: {}",
                self.backlog, self.output
            )
        });
        if message["event"] == "output" {
            self.output
                .push_str(message["body"]["output"].as_str().unwrap_or_default());
        }
        self.transcript.push(message.clone());
        message
    }

    fn send(&mut self, command: &str, arguments: Value) -> i64 {
        self.seq += 1;
        let message =
            json!({"seq": self.seq, "type": "request", "command": command, "arguments": arguments});
        self.tx.as_ref().unwrap().send(message).unwrap();
        self.seq
    }

    fn response(&mut self, command: &str, arguments: Value) -> Value {
        let seq = self.send(command, arguments);
        loop {
            let message = self.next();
            if message["type"] == "response" && message["request_seq"] == json!(seq) {
                return message;
            }
            self.backlog.push(message);
        }
    }

    fn request(&mut self, command: &str, arguments: Value) -> Value {
        let response = self.response(command, arguments);
        assert_eq!(
            response["success"],
            json!(true),
            "{command} 失败: {response}\n输出: {}",
            self.output
        );
        response.get("body").cloned().unwrap_or(Value::Null)
    }

    fn wait_event(&mut self, event: &str) -> Value {
        if let Some(i) = self.backlog.iter().position(|m| m["event"] == event) {
            return self.backlog.remove(i)["body"].clone();
        }
        loop {
            let message = self.next();
            if message["event"] == event {
                return message["body"].clone();
            }
            self.backlog.push(message);
        }
    }

    /// 等到程序输出里出现 `text`。
    fn wait_output(&mut self, text: &str) {
        while !self.output.contains(text) {
            let message = self.next();
            if message["event"] != "output" {
                self.backlog.push(message);
            }
        }
    }

    fn wait_stopped(&mut self, reason: &str) -> i64 {
        let body = self.wait_event("stopped");
        assert_eq!(
            body["reason"],
            json!(reason),
            "{body}\n输出: {}",
            self.output
        );
        body["threadId"].as_i64().unwrap()
    }

    /// 栈顶帧：(帧 ID, 名字, 行, 源文件路径)
    fn top_frame(&mut self, thread: i64) -> (i64, String, i64, String) {
        let body = self.request("stackTrace", json!({"threadId": thread}));
        let frame = &body["stackFrames"][0];
        (
            frame["id"].as_i64().unwrap(),
            frame["name"].as_str().unwrap().to_owned(),
            frame["line"].as_i64().unwrap(),
            frame["source"]["path"]
                .as_str()
                .unwrap_or_default()
                .to_owned(),
        )
    }

    fn variables(&mut self, reference: i64) -> Vec<(String, String, i64)> {
        let body = self.request("variables", json!({"variablesReference": reference}));
        body["variables"]
            .as_array()
            .unwrap()
            .iter()
            .map(|v| {
                (
                    v["name"].as_str().unwrap().to_owned(),
                    v["value"].as_str().unwrap().to_owned(),
                    v["variablesReference"].as_i64().unwrap(),
                )
            })
            .collect()
    }

    fn locals(&mut self, frame: i64) -> Vec<(String, String, i64)> {
        let scopes = self.request("scopes", json!({"frameId": frame}));
        assert_eq!(scopes["scopes"][0]["name"], json!("Locals"));
        let reference = scopes["scopes"][0]["variablesReference"].as_i64().unwrap();
        self.variables(reference)
    }

    fn evaluate(&mut self, frame: i64, expression: &str) -> String {
        let body = self.request(
            "evaluate",
            json!({"expression": expression, "frameId": frame, "context": "watch"}),
        );
        body["result"].as_str().unwrap().to_owned()
    }

    /// `completions` 请求，光标在 `text` 末尾（单行）。
    fn complete(&mut self, frame: i64, text: &str) -> Vec<Value> {
        let column = text.encode_utf16().count() + 1;
        self.complete_with(json!({"frameId": frame, "text": text, "column": column}))
    }

    fn complete_with(&mut self, arguments: Value) -> Vec<Value> {
        let body = self.request("completions", arguments);
        body["targets"].as_array().unwrap().clone()
    }

    fn finish(mut self) {
        let _ = self.response("disconnect", json!({}));
        self.tx.take();
        if let Some(thread) = self.thread.take() {
            thread.join().unwrap();
        }
    }
}

fn value_of<'a>(vars: &'a [(String, String, i64)], name: &str) -> &'a (String, String, i64) {
    vars.iter()
        .find(|(n, _, _)| n == name)
        .unwrap_or_else(|| panic!("没有变量 {name}: {vars:?}"))
}

const MAIN_JAVA: &str = r#"package demo;

public class Main {
    private int counter = 7;
    private String label = "hello";

    public static void main(String[] args) {
        Main m = new Main();
        int total = 0;
        for (int i = 0; i < 3; i++) {
            total += m.step(i);
        }
        System.out.println("total=" + total);
        m.fail();
    }

    int step(int i) {
        String text = "value" + i;
        int doubled = i * 2;
        return doubled + counter + text.length();
    }

    void fail() {
        throw new IllegalStateException("boom");
    }
}
"#;

#[test]
fn launch_breakpoints_stepping_variables_and_exceptions() {
    let jdk = require_jdk!();
    let dir = temp_dir("launch");
    let source = dir.join("src/demo/Main.java");
    write(&source, MAIN_JAVA);
    let out = dir.join("out");
    javac(&jdk, &out, &[&source]);

    let mut client = Client::start();
    client.request(
        "launch",
        json!({
            "mainClass": "demo.Main",
            "projectRoot": dir,
            "classPaths": [out],
            "javaExec": java(&jdk),
        }),
    );
    client.wait_event("initialized");
    let set = client.request(
        "setBreakpoints",
        json!({"source": {"path": source}, "breakpoints": [{"line": 11}]}),
    );
    // 类还没有加载：先报告未生效
    assert_eq!(set["breakpoints"][0]["verified"], json!(false));
    let bp_id = set["breakpoints"][0]["id"].as_i64().unwrap();
    client.request("setExceptionBreakpoints", json!({"filters": ["uncaught"]}));
    client.request("configurationDone", json!({}));

    // 类加载后断点生效
    let changed = client.wait_event("breakpoint");
    assert_eq!(changed["breakpoint"]["id"], json!(bp_id));
    assert_eq!(changed["breakpoint"]["verified"], json!(true));

    let thread = client.wait_stopped("breakpoint");
    let threads = client.request("threads", json!({}));
    assert!(threads["threads"]
        .as_array()
        .unwrap()
        .iter()
        .any(|t| t["id"] == json!(thread) && t["name"] == "main"));
    let (frame, name, line, path) = client.top_frame(thread);
    assert_eq!((name.as_str(), line), ("Main.main", 11));
    assert!(Path::new(&path).ends_with("demo/Main.java"), "{path}");

    let locals = client.locals(frame);
    let names: Vec<&str> = locals.iter().map(|(n, _, _)| n.as_str()).collect();
    assert_eq!(names, ["args", "m", "total", "i"]);
    assert_eq!(value_of(&locals, "total").1, "0");
    assert_eq!(value_of(&locals, "i").1, "0");
    assert!(
        value_of(&locals, "args").1.starts_with("String[0]"),
        "{locals:?}"
    );
    let m = value_of(&locals, "m");
    assert!(m.1.starts_with("Main@"), "{m:?}");
    let fields = client.variables(m.2);
    assert_eq!(value_of(&fields, "counter").1, "7");
    assert_eq!(value_of(&fields, "label").1, "\"hello\"");

    assert_eq!(client.evaluate(frame, "m.counter"), "7");
    assert_eq!(client.evaluate(frame, "m.label"), "\"hello\"");
    assert_eq!(client.evaluate(frame, "args.length"), "0");
    assert_eq!(
        client.evaluate(frame, "i == 0 && m.label == \"hello\""),
        "true"
    );
    let error = client.response(
        "evaluate",
        json!({"expression": "nothing", "frameId": frame}),
    );
    assert_eq!(error["success"], json!(false));

    // 修改变量
    let set_var = client.request(
        "setVariable",
        json!({"variablesReference": m.2, "name": "counter", "value": "8"}),
    );
    assert_eq!(set_var["value"], json!("8"));
    assert_eq!(client.evaluate(frame, "m.counter"), "8");
    client.request(
        "setVariable",
        json!({"variablesReference": m.2, "name": "counter", "value": "7"}),
    );

    // 步入 step()
    client.request("stepIn", json!({"threadId": thread}));
    let thread = client.wait_stopped("step");
    let (_, name, line, _) = client.top_frame(thread);
    assert_eq!((name.as_str(), line), ("Main.step", 18));

    // 单步跳过
    client.request("next", json!({"threadId": thread}));
    let thread = client.wait_stopped("step");
    let (frame, name, line, _) = client.top_frame(thread);
    assert_eq!((name.as_str(), line), ("Main.step", 19));
    let locals = client.locals(frame);
    assert_eq!(value_of(&locals, "text").1, "\"value0\"");
    assert_eq!(value_of(&locals, "i").1, "0");
    let this = value_of(&locals, "this").2;
    let fields = client.variables(this);
    assert_eq!(value_of(&fields, "counter").1, "7");
    assert_eq!(client.evaluate(frame, "counter"), "7");
    assert_eq!(client.evaluate(frame, "this.label"), "\"hello\"");

    // 步出回到 main
    client.request("stepOut", json!({"threadId": thread}));
    let thread = client.wait_stopped("step");
    let (_, name, line, _) = client.top_frame(thread);
    assert_eq!((name.as_str(), line), ("Main.main", 11));

    // 条件断点：只在 i == 2 时停
    let set = client.request(
        "setBreakpoints",
        json!({"source": {"path": source}, "breakpoints": [{"line": 19, "condition": "i == 2"}]}),
    );
    assert_eq!(set["breakpoints"][0]["verified"], json!(true));
    client.request("continue", json!({"threadId": thread}));
    let thread = client.wait_stopped("breakpoint");
    let (frame, _, line, _) = client.top_frame(thread);
    assert_eq!(line, 19);
    assert_eq!(client.evaluate(frame, "i"), "2");

    // 去掉断点，停在未捕获的异常上
    client.request(
        "setBreakpoints",
        json!({"source": {"path": source}, "breakpoints": []}),
    );
    client.request("continue", json!({"threadId": thread}));
    let stopped = client.wait_event("stopped");
    assert_eq!(stopped["reason"], json!("exception"), "{stopped}");
    assert!(
        stopped["text"].as_str().unwrap().contains("boom"),
        "{stopped}"
    );
    let thread = stopped["threadId"].as_i64().unwrap();
    let info = client.request("exceptionInfo", json!({"threadId": thread}));
    assert_eq!(
        info["exceptionId"],
        json!("java.lang.IllegalStateException")
    );
    assert_eq!(info["breakMode"], json!("unhandled"));
    let (_, name, line, _) = client.top_frame(thread);
    assert_eq!((name.as_str(), line), ("Main.fail", 24));

    // 运行到结束
    client.request("continue", json!({"threadId": thread}));
    let exited = client.wait_event("exited");
    assert_eq!(exited["exitCode"], json!(1));
    client.wait_event("terminated");
    assert!(client.output.contains("total=45"), "{}", client.output);
    assert!(
        client.output.contains("IllegalStateException"),
        "{}",
        client.output
    );
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

const EVAL_JAVA: &str = r#"package demo;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Eval {
    static class Item {
        private final String name;
        Item(String name) { this.name = name; }
        String getName() { return name; }
    }

    static int boom() { throw new IllegalArgumentException("bad input"); }
    static int spin() { while (true) { } }
    static int sum(int... xs) { int s = 0; for (int x : xs) s += x; return s; }

    public static void main(String[] args) {
        List<String> list = new ArrayList<>(java.util.Arrays.asList("a", "b", "c"));
        Map<String, Integer> map = new HashMap<>();
        map.put("k", 42);
        String key = "k";
        int n = 5;
        int a = 3, b = 4;
        Item[] items = { new Item("alpha"), new Item("xray"), new Item("beta") };
        int found = 0;
        for (Item item : items) {
            found += item.getName().length();
        }
        System.out.println("found=" + found);
    }
}
"#;

fn evaluate_error(client: &mut Client, frame: i64, expression: &str) -> String {
    let response = client.response(
        "evaluate",
        json!({"expression": expression, "frameId": frame, "context": "watch"}),
    );
    assert_eq!(
        response["success"],
        json!(false),
        "{expression}: {response}"
    );
    response["message"].as_str().unwrap().to_owned()
}

#[test]
fn evaluate_method_calls_operators_and_conditions() {
    let jdk = require_jdk!();
    let dir = temp_dir("evaluate");
    let source = dir.join("src/demo/Eval.java");
    write(&source, EVAL_JAVA);
    let out = dir.join("out");
    javac(&jdk, &out, &[&source]);

    let mut client = Client::start();
    client.request(
        "launch",
        json!({
            "mainClass": "demo.Eval",
            "projectRoot": dir,
            "classPaths": [out],
            "javaExec": java(&jdk),
        }),
    );
    client.wait_event("initialized");
    client.request(
        "setBreakpoints",
        json!({"source": {"path": source}, "breakpoints": [
            {"line": 29, "condition": "item.getName().startsWith(\"x\")"},
            {"line": 31},
        ]}),
    );
    client.request("configurationDone", json!({}));

    // 条件里调用方法：只在 xray 那一次停
    let thread = client.wait_stopped("breakpoint");
    let (frame, _, line, _) = client.top_frame(thread);
    assert_eq!(line, 29);
    assert_eq!(client.evaluate(frame, "item.getName()"), "\"xray\"");

    // 方法调用、静态方法、运算符
    assert_eq!(client.evaluate(frame, "list.size()"), "3");
    assert_eq!(client.evaluate(frame, "map.get(key)"), "42");
    assert_eq!(client.evaluate(frame, "String.valueOf(n)"), "\"5\"");
    assert_eq!(client.evaluate(frame, "a + b * 2"), "11");
    assert_eq!(client.evaluate(frame, "map.get(\"k\") + 1"), "43");
    assert_eq!(client.evaluate(frame, "sum(1, 2, 3)"), "6");
    assert_eq!(client.evaluate(frame, "Math.max(a, b)"), "4");
    assert_eq!(
        client.evaluate(frame, "\"n=\" + n + list"),
        "\"n=5[a, b, c]\""
    );
    assert_eq!(
        client.evaluate(frame, "n > 3 ? \"big\" : \"small\""),
        "\"big\""
    );
    assert_eq!(client.evaluate(frame, "items[0].getName().length()"), "5");
    assert_eq!(
        client.evaluate(frame, "list.get(0) instanceof String"),
        "true"
    );
    assert_eq!(client.evaluate(frame, "(long) n << 40"), "5497558138880");
    assert_eq!(client.evaluate(frame, "7 / 2.0"), "3.5");
    assert_eq!(
        client.evaluate(frame, "new StringBuilder(\"ab\").reverse().toString()"),
        "\"ba\""
    );
    assert_eq!(client.evaluate(frame, "(new int[] {1, 2, 3}).length"), "3");
    assert_eq!(
        client.evaluate(frame, "!list.isEmpty() || list.get(9) == null"),
        "true"
    );
    assert!(evaluate_error(&mut client, frame, "n / 0").contains("ArithmeticException"));

    // 方法抛出异常：报错，会话照常
    let error = evaluate_error(&mut client, frame, "boom()");
    assert!(
        error.contains("IllegalArgumentException") && error.contains("bad input"),
        "{error}"
    );
    assert_eq!(client.evaluate(frame, "list.size()"), "3");

    // 死循环：超时后中止，会话照常
    let error = evaluate_error(&mut client, frame, "spin()");
    assert!(error.contains("timed out"), "{error}");
    if error.contains("could not be aborted") {
        // 有的 JDK（例如 11）的 JDWP 把 ThreadReference.Stop 推迟到断点事件处理完才投递，
        // 打断不了在事件里调用的方法，线程只能留在死循环里
        client.finish();
        std::fs::remove_dir_all(&dir).ok();
        return;
    }
    let (frame, _, line, _) = client.top_frame(thread);
    assert_eq!(line, 29);
    assert_eq!(client.evaluate(frame, "n"), "5");
    assert_eq!(client.evaluate(frame, "list.size()"), "3");

    // 悬停不调用方法
    let hover = client.response(
        "evaluate",
        json!({"expression": "list.size()", "frameId": frame, "context": "hover"}),
    );
    assert_eq!(hover["success"], json!(false), "{hover}");

    client.request("continue", json!({"threadId": thread}));
    let thread = client.wait_stopped("breakpoint");
    let (frame, _, line, _) = client.top_frame(thread);
    assert_eq!(line, 31);
    assert_eq!(client.evaluate(frame, "found"), "13");
    client.request("continue", json!({"threadId": thread}));
    client.wait_event("terminated");
    assert!(client.output.contains("found=13"), "{}", client.output);
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

const FIELDS_JAVA: &str = r#"package demo;

public class Fields {
    static class Base {
        int x = 1;
        static int S = 10;
        int seen() { return x; }
    }

    static class Derived extends Base {
        int x = 2;
        static int S = 20;
        int runtimeOnly = 78;
    }

    public static void main(String[] args) {
        Derived derived = new Derived();
        Base base = derived;
        System.out.println("stop");
        base.seen();
    }
}
"#;

/// 字段不按运行时类型分派：隐藏字段由表达式的静态类型决定，静态字段不读接收者。
#[test]
fn evaluate_fields_use_the_static_type() {
    let jdk = require_jdk!();
    let dir = temp_dir("fields");
    let source = dir.join("src/demo/Fields.java");
    write(&source, FIELDS_JAVA);
    let out = dir.join("out");
    javac(&jdk, &out, &[&source]);

    let mut client = Client::start();
    client.request(
        "launch",
        json!({
            "mainClass": "demo.Fields",
            "projectRoot": dir,
            "classPaths": [out],
            "javaExec": java(&jdk),
        }),
    );
    client.wait_event("initialized");
    client.request(
        "setBreakpoints",
        json!({"source": {"path": source}, "breakpoints": [{"line": 20}, {"line": 7}]}),
    );
    client.request("configurationDone", json!({}));
    let thread = client.wait_stopped("breakpoint");
    let (frame, _, line, _) = client.top_frame(thread);
    assert_eq!(line, 20);

    assert_eq!(client.evaluate(frame, "derived.x"), "2");
    assert_eq!(client.evaluate(frame, "base.x"), "1");
    assert_eq!(client.evaluate(frame, "((Base) derived).x"), "1");
    assert_eq!(client.evaluate(frame, "((Derived) base).x"), "2");
    assert_eq!(client.evaluate(frame, "derived.S"), "20");
    assert_eq!(client.evaluate(frame, "base.S"), "10");
    // 静态字段不读接收者，null 也行
    assert_eq!(client.evaluate(frame, "((Base) null).S"), "10");
    // 实例字段通过 null 仍然是 NullPointerException
    assert!(evaluate_error(&mut client, frame, "((Base) null).x").contains("NullPointerException"));

    // 父类方法里，简单名字 `x` 和 `this.x` 都是 `Base.x`，`this` 的运行时类型是 Derived 也一样
    client.request("continue", json!({"threadId": thread}));
    let thread = client.wait_stopped("breakpoint");
    let (frame, _, line, _) = client.top_frame(thread);
    assert_eq!(line, 7);
    assert_eq!(client.evaluate(frame, "x"), "1");
    assert_eq!(client.evaluate(frame, "this.x"), "1");
    assert_eq!(client.evaluate(frame, "S"), "10");
    // 词法上找不到的名字才退回运行时类型：子类才有的字段在监视里照样读得到
    assert_eq!(client.evaluate(frame, "runtimeOnly"), "78");

    client.request("continue", json!({"threadId": thread}));
    client.wait_event("terminated");
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

const LOADER_JAVA: &str = r#"package demo;

import java.io.File;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.List;

public class Loader {
    public static void main(String[] args) throws Exception {
        URL[] urls = {new File(args[0]).toURI().toURL()};
        // 两份 Plugin 先都载入，再依次调用
        List<Class<?>> plugins = new ArrayList<>();
        for (int value : new int[] {101, 202}) {
            Class<?> plugin = new URLClassLoader(urls).loadClass("separate.Plugin");
            plugin.getField("S").setInt(null, value);
            plugins.add(plugin);
        }
        for (Class<?> plugin : plugins) {
            plugin.getMethod("stop").invoke(plugin.getDeclaredConstructor().newInstance());
        }
    }
}
"#;

const PLUGIN_JAVA: &str = r#"package separate;
public class Plugin {
    public static int S;
    public void stop() {
        Plugin p = this;
        System.out.println(p.S);
    }
}
"#;

/// 同名的类由两个 ClassLoader 各载入一份：静态字段要读当前对象自己那份，不是 JVM 里同名的第一个。
#[test]
fn evaluate_static_fields_with_the_same_class_in_two_class_loaders() {
    let jdk = require_jdk!();
    let dir = temp_dir("loaders");
    let loader = dir.join("src/demo/Loader.java");
    let plugin = dir.join("src/separate/Plugin.java");
    write(&loader, LOADER_JAVA);
    write(&plugin, PLUGIN_JAVA);
    let out = dir.join("out");
    // Plugin 不在启动类路径上，只由 Loader 里的两个 URLClassLoader 载入
    let plugins = dir.join("plugins");
    javac(&jdk, &out, &[&loader]);
    javac(&jdk, &plugins, &[&plugin]);

    let mut client = Client::start();
    client.request(
        "launch",
        json!({
            "mainClass": "demo.Loader",
            "projectRoot": dir,
            "classPaths": [out],
            "args": [plugins],
            "javaExec": java(&jdk),
        }),
    );
    client.wait_event("initialized");
    client.request(
        "setBreakpoints",
        json!({"source": {"path": plugin}, "breakpoints": [{"line": 6}]}),
    );
    client.request("configurationDone", json!({}));
    for expected in ["101", "202"] {
        let thread = client.wait_stopped("breakpoint");
        let (frame, _, line, _) = client.top_frame(thread);
        assert_eq!(line, 6);
        for expression in ["p.S", "this.S", "S"] {
            assert_eq!(client.evaluate(frame, expression), expected, "{expression}");
        }
        client.request("continue", json!({"threadId": thread}));
    }
    client.wait_event("terminated");
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

const NULL_LOADER_JAVA: &str = r#"package demo;

import java.io.File;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.List;

public class NullLoader {
    public static void main(String[] args) throws Exception {
        URL plugins = new File(args[0]).toURI().toURL();
        URL callers = new File(args[1]).toURI().toURL();
        // 两个父 ClassLoader 各定义一份 separate.Plugin，Caller 由它们各自的子 ClassLoader 载入
        List<Class<?>> loaded = new ArrayList<>();
        for (int value : new int[] {101, 202}) {
            URLClassLoader parent = new URLClassLoader(new URL[] {plugins});
            parent.loadClass("separate.Plugin").getField("S").setInt(null, value);
            loaded.add(new URLClassLoader(new URL[] {callers}, parent).loadClass("caller.Caller"));
        }
        for (Class<?> caller : loaded) {
            caller.getMethod("stop").invoke(caller.getDeclaredConstructor().newInstance());
        }
    }
}
"#;

const CALLER_JAVA: &str = r#"package caller;

import separate.Plugin;

public class Caller {
    public void stop() {
        Plugin p = null;
        Plugin q = new Plugin();
        System.out.println(q.S);
    }
}
"#;

/// 接收者是 null、同名的类有两份时，不能读到另一份的静态字段：认不出是哪一份就报错。
#[test]
fn evaluate_static_field_through_null_with_two_classes_of_the_same_name() {
    let jdk = require_jdk!();
    let dir = temp_dir("null-loaders");
    let main = dir.join("src/demo/NullLoader.java");
    let plugin = dir.join("src/separate/Plugin.java");
    let caller = dir.join("src/caller/Caller.java");
    write(&main, NULL_LOADER_JAVA);
    write(&plugin, PLUGIN_JAVA);
    write(&caller, CALLER_JAVA);
    let out = dir.join("out");
    javac(&jdk, &out, &[&main]);
    // Plugin 和 Caller 一起编译，再拆到两个目录里：启动类路径上都没有它们
    let all = dir.join("all");
    javac(&jdk, &all, &[&plugin, &caller]);
    let (plugins, callers) = (dir.join("plugins"), dir.join("callers"));
    for (from, to, file) in [
        ("separate", &plugins, "Plugin.class"),
        ("caller", &callers, "Caller.class"),
    ] {
        std::fs::create_dir_all(to.join(from)).unwrap();
        std::fs::copy(all.join(from).join(file), to.join(from).join(file)).unwrap();
    }

    let mut client = Client::start();
    client.request(
        "launch",
        json!({
            "mainClass": "demo.NullLoader",
            "projectRoot": dir,
            "classPaths": [out],
            "args": [plugins, callers],
            "javaExec": java(&jdk),
        }),
    );
    client.wait_event("initialized");
    client.request(
        "setBreakpoints",
        json!({"source": {"path": caller}, "breakpoints": [{"line": 9}]}),
    );
    client.request("configurationDone", json!({}));
    for expected in ["101", "202"] {
        let thread = client.wait_stopped("breakpoint");
        let (frame, _, line, _) = client.top_frame(thread);
        assert_eq!(line, 9);
        // 非 null 的接收者认得出是哪一份
        assert_eq!(client.evaluate(frame, "q.S"), expected);
        // null 的认不出：报错可以，值必须不是另一份的
        let response = client.response(
            "evaluate",
            json!({"expression": "p.S", "frameId": frame, "context": "watch"}),
        );
        if response["success"] == json!(true) {
            assert_eq!(response["body"]["result"], json!(expected), "{response}");
        }
        client.request("continue", json!({"threadId": thread}));
    }
    client.wait_event("terminated");
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

const LAZY_JAVA: &str = r#"package demo;

public class Lazy {
    static boolean inited = false;

    static class Target {
        static int S = 17;
        int x = 3;

        static {
            Lazy.inited = true;
        }
    }

    public static void main(String[] args) {
        Target target = null;
        System.out.println("stop");
    }
}
"#;

/// 读 null 接收者的字段不能为了认出它的类型去载入、初始化还没载入的类：Java 里 `target.x` 只抛
/// NPE，不会运行静态初始化器。
#[test]
fn evaluate_field_through_null_does_not_initialize_the_class() {
    let jdk = require_jdk!();
    let dir = temp_dir("lazy");
    let source = dir.join("src/demo/Lazy.java");
    write(&source, LAZY_JAVA);
    let out = dir.join("out");
    javac(&jdk, &out, &[&source]);

    let mut client = Client::start();
    client.request(
        "launch",
        json!({
            "mainClass": "demo.Lazy",
            "projectRoot": dir,
            "classPaths": [out],
            "javaExec": java(&jdk),
        }),
    );
    client.wait_event("initialized");
    client.request(
        "setBreakpoints",
        json!({"source": {"path": source}, "breakpoints": [{"line": 17}]}),
    );
    client.request("configurationDone", json!({}));
    let thread = client.wait_stopped("breakpoint");
    let (frame, _, line, _) = client.top_frame(thread);
    assert_eq!(line, 17);
    assert_eq!(client.evaluate(frame, "inited"), "false");
    for expression in ["target.x", "target.S"] {
        let response = client.response(
            "evaluate",
            json!({"expression": expression, "frameId": frame, "context": "watch"}),
        );
        assert_eq!(
            response["success"],
            json!(false),
            "{expression}: {response}"
        );
        assert_eq!(client.evaluate(frame, "inited"), "false", "{expression}");
    }
    client.request("continue", json!({"threadId": thread}));
    client.wait_event("terminated");
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn launch_maven_project_without_class_paths() {
    let jdk = require_jdk!();
    let dir = temp_dir("maven");
    write(
        &dir.join("pom.xml"),
        r#"<?xml version="1.0" encoding="UTF-8"?>
<project xmlns="http://maven.apache.org/POM/4.0.0">
  <modelVersion>4.0.0</modelVersion>
  <groupId>demo</groupId>
  <artifactId>app</artifactId>
  <version>1.0</version>
</project>
"#,
    );
    let source = dir.join("src/main/java/demo/App.java");
    write(
        &source,
        r#"package demo;

public class App {
    public static void main(String[] args) {
        String greeting = "hi from maven";
        System.out.println(greeting);
    }
}
"#,
    );
    javac(&jdk, &dir.join("target/classes"), &[&source]);

    let mut client = Client::start();
    client.request(
        "launch",
        json!({"mainClass": "demo.App", "projectRoot": dir, "javaExec": java(&jdk)}),
    );
    client.wait_event("initialized");
    client.request(
        "setBreakpoints",
        json!({"source": {"path": source}, "breakpoints": [{"line": 6}]}),
    );
    client.request("configurationDone", json!({}));
    let thread = client.wait_stopped("breakpoint");
    let (frame, name, line, path) = client.top_frame(thread);
    assert_eq!((name.as_str(), line), ("App.main", 6));
    // 平台的分隔符，和编辑器里打开的路径逐字一致
    let expected = project_model::canonicalize(&dir)
        .unwrap()
        .join("src")
        .join("main")
        .join("java")
        .join("demo")
        .join("App.java");
    assert_eq!(path, expected.to_string_lossy(), "{path}");
    let locals = client.locals(frame);
    assert_eq!(value_of(&locals, "greeting").1, "\"hi from maven\"");
    client.request("continue", json!({"threadId": thread}));
    let exited = client.wait_event("exited");
    assert_eq!(exited["exitCode"], json!(0));
    client.wait_event("terminated");
    assert!(client.output.contains("hi from maven"), "{}", client.output);
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn launch_with_a_class_path_longer_than_the_command_line_allows() {
    let jdk = require_jdk!();
    let dir = temp_dir("long-cp");
    let source = dir.join("src/demo/Main.java");
    write(
        &source,
        r#"package demo;

public class Main {
    public static void main(String[] args) {
        String[] entries = System.getProperty("java.class.path").split(java.io.File.pathSeparator);
        System.out.println("class path entries: " + entries.length);
    }
}
"#,
    );
    let out = dir.join("out");
    javac(&jdk, &out, &[&source]);
    // 带空格的路径，合起来超过 Windows 整条命令行的 32767 个字符
    let mut class_paths = vec![out.to_string_lossy().into_owned()];
    class_paths.extend((0..1000).map(|i| {
        dir.join(format!("lib with space {i}.jar"))
            .to_string_lossy()
            .into_owned()
    }));

    let mut client = Client::start();
    client.request(
        "launch",
        json!({"mainClass": "demo.Main", "projectRoot": dir, "classPaths": class_paths, "javaExec": java(&jdk)}),
    );
    client.wait_event("initialized");
    client.request("configurationDone", json!({}));
    let exited = client.wait_event("exited");
    assert_eq!(exited["exitCode"], json!(0), "{}", client.output);
    client.wait_event("terminated");
    // JDK 9 起类路径在参数文件里，`java.class.path` 还是那 1001 项；更早的 JDK 用只有清单的
    // jar，`java.class.path` 只有这个 jar。两种情况主类都只能从长类路径里的 `out/` 找到
    assert!(
        client.output.contains("class path entries: 1001")
            || client.output.contains("class path entries: 1\n"),
        "{}",
        client.output
    );
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn launch_without_compiled_output_reports_an_error() {
    let _jdk = require_jdk!();
    let dir = temp_dir("uncompiled");
    write(
        &dir.join("pom.xml"),
        "<project><modelVersion>4.0.0</modelVersion><groupId>d</groupId><artifactId>x</artifactId><version>1</version></project>",
    );
    write(
        &dir.join("src/main/java/demo/X.java"),
        "package demo; class X { public static void main(String[] a) {} }",
    );
    let mut client = Client::start();
    let response = client.response("launch", json!({"mainClass": "demo.X", "projectRoot": dir}));
    assert_eq!(response["success"], json!(false));
    assert!(
        response["message"]
            .as_str()
            .unwrap()
            .contains(&format!("target{}classes", std::path::MAIN_SEPARATOR)),
        "{response}"
    );
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn launch_missing_main_class_exits() {
    let jdk = require_jdk!();
    let dir = temp_dir("missing");
    let mut client = Client::start();
    client.request(
        "launch",
        json!({"mainClass": "demo.Missing", "projectRoot": dir, "classPaths": [dir], "javaExec": java(&jdk)}),
    );
    client.wait_event("initialized");
    client.request("configurationDone", json!({}));
    let exited = client.wait_event("exited");
    assert_eq!(exited["exitCode"], json!(1));
    client.wait_event("terminated");
    assert!(client.output.contains("demo.Missing"), "{}", client.output);
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn attach_to_running_jvm() {
    let jdk = require_jdk!();
    let dir = temp_dir("attach");
    let source = dir.join("src/demo/Loop.java");
    write(
        &source,
        r#"package demo;

public class Loop {
    public static void main(String[] args) throws Exception {
        for (int n = 0; n < 2; n++) {
            Thread.sleep(10);
            System.out.println("tick " + n);
        }
    }
}
"#,
    );
    let out = dir.join("out");
    javac(&jdk, &out, &[&source]);
    let mut child = Command::new(tool(&jdk, "java"))
        .arg("-agentlib:jdwp=transport=dt_socket,server=y,suspend=y,address=127.0.0.1:0")
        .arg("-cp")
        .arg(&out)
        .arg("demo.Loop")
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    // JVM 先打印 `Listening for transport dt_socket at address: <端口>`
    let mut stdout = BufReader::new(child.stdout.take().unwrap());
    let mut line = String::new();
    stdout.read_line(&mut line).unwrap();
    let port: u16 = line
        .trim()
        .rsplit(':')
        .next()
        .and_then(|p| p.trim().parse().ok())
        .unwrap_or_else(|| panic!("无法从 `{line}` 读出端口"));

    let mut client = Client::start();
    client.request(
        "attach",
        json!({"hostName": "127.0.0.1", "port": port, "projectRoot": dir}),
    );
    client.wait_event("initialized");
    client.request(
        "setBreakpoints",
        json!({"source": {"path": source}, "breakpoints": [{"line": 7, "hitCondition": "2"}]}),
    );
    client.request("configurationDone", json!({}));
    let thread = client.wait_stopped("breakpoint");
    let (frame, name, line, path) = client.top_frame(thread);
    assert_eq!((name.as_str(), line), ("Loop.main", 7));
    assert!(Path::new(&path).ends_with("demo/Loop.java"), "{path}");
    // 命中次数条件：第 2 次才停
    assert_eq!(client.evaluate(frame, "n"), "1");
    client.request("continue", json!({"threadId": thread}));
    client.wait_event("terminated");
    let status = child.wait().unwrap();
    assert!(status.success());
    // 读完剩下的输出，确认程序跑完了
    let rest: Vec<String> = stdout.lines().map_while(Result::ok).collect();
    assert!(rest.iter().any(|l| l == "tick 1"), "{rest:?}");
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

fn hot_source(body: &str, extra: &str) -> String {
    format!(
        r#"package demo;

public class Hot {{
    public static void main(String[] args) throws Exception {{
        for (int n = 0; n < 3000; n++) {{
            System.out.println(value(n));
            Thread.sleep(20);
        }}
    }}

    static String value(int n) {{
        return {body};
    }}
{extra}}}
"#
    )
}

#[test]
fn redefine_changed_classes() {
    let jdk = require_jdk!();
    let dir = temp_dir("hotswap");
    let source = dir.join("src/demo/Hot.java");
    write(&source, &hot_source(r#""old " + n"#, ""));
    let out = dir.join("out");
    javac(&jdk, &out, &[&source]);

    let mut client = Client::start();
    client.request(
        "launch",
        json!({
            "mainClass": "demo.Hot",
            "projectRoot": dir,
            "classPaths": [out],
            "javaExec": java(&jdk),
        }),
    );
    client.wait_event("initialized");
    client.request(
        "setBreakpoints",
        json!({"source": {"path": source}, "breakpoints": [{"line": 12}]}),
    );
    client.request("configurationDone", json!({}));
    let thread = client.wait_stopped("breakpoint");
    assert_eq!(client.top_frame(thread).1, "Hot.value");
    // 断点在类加载时生效的事件已经发过了
    client.wait_event("breakpoint");

    // 只改方法体：替换成功，断点在新版本上继续命中
    std::thread::sleep(Duration::from_millis(50));
    write(&source, &hot_source(r#""new " + n"#, ""));
    javac(&jdk, &out, &[&source]);
    let result = client.request("redefineClasses", json!({}));
    let classes = result["classes"].as_array().unwrap();
    assert_eq!(classes.len(), 1, "{result}");
    assert_eq!(classes[0]["name"], json!("demo.Hot"));
    assert_eq!(classes[0]["status"], json!("redefined"), "{result}");
    let changed = client.wait_event("breakpoint");
    assert_eq!(changed["breakpoint"]["verified"], json!(true), "{changed}");
    assert_eq!(changed["breakpoint"]["line"], json!(12), "{changed}");

    client.request("continue", json!({"threadId": thread}));
    let thread = client.wait_stopped("breakpoint");
    let (frame, name, line, _) = client.top_frame(thread);
    assert_eq!((name.as_str(), line), ("Hot.value", 12));
    let n: i64 = client.evaluate(frame, "n").parse().unwrap();
    assert!(n >= 1, "{n}");
    client.request(
        "setBreakpoints",
        json!({"source": {"path": source}, "breakpoints": []}),
    );
    client.request("continue", json!({"threadId": thread}));
    client.wait_output(&format!("new {n}"));

    // 没有变化时什么也不做
    let result = client.request("redefineClasses", json!({}));
    assert_eq!(result["classes"], json!([]), "{result}");

    // 增加方法：JVM 拒绝，给出原因，会话继续
    std::thread::sleep(Duration::from_millis(50));
    write(
        &source,
        &hot_source(
            r#""newer " + n"#,
            "\n    static int extra() {\n        return 1;\n    }\n",
        ),
    );
    javac(&jdk, &out, &[&source]);
    let result = client.request("redefineClasses", json!({}));
    let classes = result["classes"].as_array().unwrap();
    assert_eq!(classes.len(), 1, "{result}");
    assert_eq!(classes[0]["status"], json!("failed"), "{result}");
    let message = classes[0]["message"].as_str().unwrap();
    assert!(message.contains("A method was added"), "{message}");
    client.wait_output("Hot swap of demo.Hot failed");
    let threads = client.request("threads", json!({}));
    assert!(!threads["threads"].as_array().unwrap().is_empty());
    let before = client.output.len();
    client.wait_output(&format!("new {}", n + 20));
    assert!(
        !client.output[before..].contains("newer"),
        "{}",
        client.output
    );

    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}

const GREET_JAVA: &str = r#"package demo;

public class Greet {
    public static void main(String[] args) {
        int n = args.length;
        System.out.println("n=" + n);
    }



    // 这几行没有代码
}
"#;

/// 文本里有没有中文（汉字和全角标点）。
fn has_chinese(text: &str) -> bool {
    text.chars().any(|c| {
        ('\u{4e00}'..='\u{9fff}').contains(&c)
            || ('\u{3000}'..='\u{303f}').contains(&c)
            || ('\u{ff00}'..='\u{ffef}').contains(&c)
    })
}

/// 声明 `locale` 跑一次会话，返回适配器的几条文案：`[表达式的语法错误, 找不到的名字,
/// 没有代码的行上的断点, 不支持的请求]`，以及会话里收到的全部消息。
fn localized_messages(jdk: &Path, locale: &str) -> ([String; 4], Vec<Value>) {
    let dir = temp_dir(&format!("locale-{locale}"));
    let source = dir.join("src/demo/Greet.java");
    write(&source, GREET_JAVA);
    let out = dir.join("out");
    javac(jdk, &out, &[&source]);

    let mut client = Client::start_with_locale(Some(locale));
    let unsupported = client.response("bogusRequest", json!({}));
    assert_eq!(unsupported["success"], json!(false), "{unsupported}");
    let unsupported = unsupported["message"].as_str().unwrap().to_owned();
    client.request(
        "launch",
        json!({
            "mainClass": "demo.Greet",
            "projectRoot": dir,
            "classPaths": [out],
            "javaExec": java(jdk),
        }),
    );
    client.wait_event("initialized");
    let breakpoints =
        json!({"source": {"path": source}, "breakpoints": [{"line": 5}, {"line": 10}]});
    client.request("setBreakpoints", breakpoints.clone());
    client.request("configurationDone", json!({}));
    let thread = client.wait_stopped("breakpoint");
    let (frame, _, line, _) = client.top_frame(thread);
    assert_eq!(line, 5);

    // 类已经加载，第 10 行还是没有代码
    let set = client.request("setBreakpoints", breakpoints);
    assert_eq!(set["breakpoints"][0]["verified"], json!(true), "{set}");
    assert_eq!(set["breakpoints"][1]["verified"], json!(false), "{set}");
    let blank_line = set["breakpoints"][1]["message"]
        .as_str()
        .unwrap()
        .to_owned();
    let syntax = evaluate_error(&mut client, frame, "args.wait(");
    let unknown = evaluate_error(&mut client, frame, "nothing");

    client.request("continue", json!({"threadId": thread}));
    client.wait_event("terminated");
    assert!(client.output.contains("n=0"), "{}", client.output);
    let transcript = client.transcript.clone();
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
    ([syntax, unknown, blank_line, unsupported], transcript)
}

#[test]
fn messages_follow_english_locale() {
    let jdk = require_jdk!();
    let ([syntax, unknown, blank_line, unsupported], transcript) = localized_messages(&jdk, "en");
    assert_eq!(
        syntax,
        "Syntax error in the expression: Expected an expression"
    );
    assert_eq!(unknown, "Cannot find name `nothing`");
    assert_eq!(
        blank_line,
        "The class is not loaded yet, or this line has no executable code"
    );
    assert_eq!(unsupported, "Unsupported request `bogusRequest`");
    for message in &transcript {
        assert!(!has_chinese(&message.to_string()), "{message}");
    }
}

#[test]
fn messages_follow_chinese_locale() {
    let jdk = require_jdk!();
    let ([syntax, unknown, blank_line, unsupported], _) = localized_messages(&jdk, "zh-CN");
    assert_eq!(syntax, "表达式有语法错误：此处应为表达式");
    assert_eq!(unknown, "找不到名字 `nothing`");
    assert_eq!(blank_line, "类还没有加载，或者这一行没有可执行的代码");
    assert_eq!(unsupported, "不支持的请求 `bogusRequest`");
}

const COMPLETE_JAVA: &str = r#"package demo;

import java.util.ArrayList;
import java.util.List;

public class Complete {
    static int calls = 0;
    private int count = 3;

    static class Box {
        String label = "box";
        Box self() { calls++; return this; }
    }

    Box box() { calls++; return new Box(); }

    public static void main(String[] args) {
        ArrayList<String> arrayList = new ArrayList<>();
        List<String> list = arrayList;
        Complete c = new Complete();
        Box box = new Box();
        list.add("a");
        System.out.println(list.size() + c.count + box.label);
        int later = 1;
        System.out.println("later=" + later);
    }
}
"#;

fn target<'a>(targets: &'a [Value], label: &str) -> &'a Value {
    targets
        .iter()
        .find(|t| t["label"] == label)
        .unwrap_or_else(|| panic!("没有补全项 {label}: {targets:#?}"))
}

fn has_target(targets: &[Value], label: &str) -> bool {
    targets.iter().any(|t| t["label"] == label)
}

#[test]
fn completions_in_debug_console() {
    let jdk = require_jdk!();
    let dir = temp_dir("completions");
    let source = dir.join("src/demo/Complete.java");
    write(&source, COMPLETE_JAVA);
    let out = dir.join("out");
    javac(&jdk, &out, &[&source]);

    let mut client = Client::start();
    client.request(
        "launch",
        json!({
            "mainClass": "demo.Complete",
            "projectRoot": dir,
            "classPaths": [out],
            "javaExec": java(&jdk),
        }),
    );
    client.wait_event("initialized");
    client.request(
        "setBreakpoints",
        json!({"source": {"path": source}, "breakpoints": [{"line": 23}]}),
    );
    client.request("configurationDone", json!({}));
    let thread = client.wait_stopped("breakpoint");
    let (frame, _, line, _) = client.top_frame(thread);
    assert_eq!(line, 23);

    // 局部变量：只有当前行之前声明的
    let targets = client.complete(frame, "ar");
    let args = target(&targets, "args");
    assert_eq!(args["type"], json!("variable"));
    assert_eq!(args["detail"], json!("String[]"));
    let array_list = target(&targets, "arrayList");
    assert_eq!(array_list["type"], json!("variable"));
    assert_eq!(array_list["detail"], json!("ArrayList"));
    assert_eq!(targets[0]["label"], json!("args"), "{targets:#?}");
    let targets = client.complete(frame, "l");
    assert!(has_target(&targets, "list"), "{targets:#?}");
    assert!(!has_target(&targets, "later"), "{targets:#?}");
    // 静态字段、方法、import 的类型、成员类、java.lang 的类型、关键字
    let targets = client.complete(frame, "");
    assert_eq!(target(&targets, "calls")["type"], json!("field"));
    assert_eq!(target(&targets, "main")["type"], json!("method"));
    assert_eq!(
        target(&targets, "ArrayList")["detail"],
        json!("java.util.ArrayList")
    );
    assert_eq!(target(&targets, "Box")["type"], json!("class"));
    assert_eq!(target(&targets, "String")["type"], json!("class"));
    assert_eq!(target(&targets, "null")["type"], json!("keyword"));
    assert!(!has_target(&targets, "this"), "静态方法里没有 this");

    // 值的运行时类型的成员
    let targets = client.complete(frame, "list.");
    for method in ["add", "size", "isEmpty", "hashCode"] {
        assert_eq!(
            target(&targets, method)["type"],
            json!("method"),
            "{method}"
        );
    }
    assert_eq!(target(&targets, "size")["text"], json!("size()"));
    assert_eq!(target(&targets, "add")["text"], json!("add("));
    assert!(!has_target(&targets, "elementData"), "别的包的非公开字段");
    let targets = client.complete(frame, "args.");
    assert_eq!(target(&targets, "length")["detail"], json!("int"));
    let targets = client.complete(frame, "c.");
    assert_eq!(target(&targets, "count")["type"], json!("field"));
    assert_eq!(target(&targets, "box")["type"], json!("method"));
    let targets = client.complete(frame, "list.size() + c.co");
    assert_eq!(targets[0]["label"], json!("count"), "{targets:#?}");

    // 类型名：静态成员和成员类；包名：子包和类型
    let targets = client.complete(frame, "System.");
    assert_eq!(target(&targets, "out")["type"], json!("field"));
    assert_eq!(
        target(&targets, "currentTimeMillis")["type"],
        json!("method")
    );
    assert!(!has_target(&targets, "getClass"), "不列实例方法");
    let targets = client.complete(frame, "Complete.");
    assert!(has_target(&targets, "calls") && has_target(&targets, "Box"));
    let targets = client.complete(frame, "java.util.");
    assert_eq!(target(&targets, "ArrayList")["type"], json!("class"));
    assert_eq!(target(&targets, "concurrent")["type"], json!("module"));

    // 要调用方法才算得出来的接收者：用返回类型，不真的调用
    let targets = client.complete(frame, "c.box().");
    assert!(has_target(&targets, "label") && has_target(&targets, "self"));
    let targets = client.complete(frame, "c.box().self().la");
    assert_eq!(targets[0]["label"], json!("label"), "{targets:#?}");

    // 多行文本；不带 frameId 时用停下的线程
    let targets = client.complete_with(json!({
        "frameId": frame, "text": "1 +\nlist.si", "line": 2, "column": 8,
    }));
    assert!(has_target(&targets, "size"), "{targets:#?}");
    let targets = client.complete_with(json!({"text": "ar", "column": 3}));
    assert!(has_target(&targets, "args"), "{targets:#?}");

    // 目标 JVM 没有变化：还停在原处，方法没有被调用过
    let (frame, _, line, _) = client.top_frame(thread);
    assert_eq!(line, 23);
    assert_eq!(client.evaluate(frame, "calls"), "0");
    assert_eq!(client.evaluate(frame, "list.size()"), "1");

    client.request("continue", json!({"threadId": thread}));
    client.wait_event("terminated");
    // 程序没有停下：空列表，不报错
    assert!(client.complete(frame, "ar").is_empty());
    assert!(client.output.contains("later=1"), "{}", client.output);
    client.finish();
    std::fs::remove_dir_all(&dir).ok();
}
