# 配置

## 服务器选项

通过 `initializationOptions` 或 `workspace/didChangeConfiguration` 传入。
可以直接给出下面的对象，也可以包在 `"java-analyzer"` 键下。

| 键 | 默认值 | 说明 |
|---|---|---|
| `jdkHome` | 自动发现 | JDK 的安装目录。未设置时按工程的语言级别自动挑选，见 [JDK 的选择](#jdk-的选择) |
| `maven.useCli` | `true` | 本地仓库缺少依赖或 POM 时，是否调用 `mvn`（优先 `./mvnw`）把缺的构件下载进本地仓库（多模块工程不需要先 `mvn install` 各个模块），仍然解析不了的话再在整个 reactor 上运行一次 `mvn` 导出各模块的 classpath。本地仓库里构件齐全时不会调用 `mvn`；同一次运行里下载过却没下载到的构件，重新导入时不再为它们调用 `mvn` |
| `maven.localRepository` | 自动 | Maven 本地仓库的目录。不设置时和 Maven 一样依次看 `MAVEN_OPTS` 里的 `-Dmaven.repo.local`、用户级设置文件（`maven.settings`，没有设置时是 `~/.m2/settings.xml`）的 `<localRepository>`、Maven 安装目录（`MAVEN_HOME` / `M2_HOME`，或 `PATH` 上的 `mvn`）下 `conf/settings.xml` 的 `<localRepository>`，都没有时是 `~/.m2/repository`；其中可以用 `${user.home}` 和 `${env.NAME}`。调用 `mvn` 时以 `-Dmaven.repo.local` 传入，下载的构件放进同一个仓库 |
| `maven.settings` | 无 | 代替 `~/.m2/settings.xml` 的 Maven 设置文件，相当于 `mvn -s`：从中读取 `<localRepository>` 和镜像，调用 `mvn` 时以 `-s` 传入。设置文件位于某个 Maven 安装的 `conf/` 下时，其中的 `${maven.home}` 指那个安装 |
| `gradle.enabled` | `true` | 是否允许运行 Gradle 导入工程。关闭后只使用上一次导入的缓存 |
| `completion.autoImport` | `true` | 选中未导入的类型时自动添加 import；关闭后插入全限定名 |
| `completion.unimportedTypes` | `true` | 是否在候选里包含未导入的类型 |
| `completion.postfix` | `true` | 是否提供 `.var` / `.if` / `.for` / `.nn` 等后缀模板 |
| `completion.limit` | `400` | 一次返回的候选上限 |
| `codeLens.references` | `true` | 在声明上方显示引用数；客户端自己会显示用法提示时可以关掉 |
| `codeLens.implementations` | `true` | 在类型 / 方法上方显示实现数 |
| `codeLens.command` | 自动 | 点击 code lens 时执行的客户端命令，参数是 `[uri, position, locations]`；不设置时 VS Code 用 `editor.action.showReferences`，其它客户端只显示数量 |
| `newFileTemplate` | `true` | 打开新建的空 `.java` 文件时，填上按源码目录算出的 package 声明和与文件同名的类（`package-info.java` 只填 package；需要客户端支持 `workspace/applyEdit`） |
| `downloadSources` | `true` | 跳转到没有源码包的依赖库类时，在后台用 `mvn dependency:get` 下载它的 sources jar（沿用 Maven 的镜像和认证设置，存进 Maven 本地仓库）；下载完成后打开着的桩代码就地换成源码，悬停文档和参数名也随之更新。`mvn` 不可用时用 `curl` 从 `settings.xml`（用户级优先，其次是 Maven 安装目录下的）里镜像了 `central` 的仓库（没有配置时是 Maven Central）直接下载；Gradle 缓存里的库同样按坐标下载 |
| `decompiler` | `true` | 跳转到既没有源码包、也没能下载到源码的依赖库类时，打开的桩代码里的方法体从字节码反编译出来（反编译不了的方法留空并注明原因）；关闭后桩代码只有签名 |
| `diagnostics.semantic` | `true` | 是否报告语义诊断（无法解析的符号、类型不匹配等）；关闭后只有语法错误 |
| `diagnostics.unusedImports` | `true` | 是否提示未使用的 import |
| `diagnostics.unusedSymbols` | `true` | 是否提示未使用的局部变量和私有成员 |
| `diagnostics.workspace` | 自动 | 是否计算整个工程的诊断（`workspace/diagnostic`，客户端的问题列表用），只含错误和警告；不设置时，源文件不超过 3000 个才计算 |
| `diagnostics.inspections` | `true` | 是否做流分析（不可达语句、缺少 `return`、未初始化的局部变量、未处理的受检异常）和表达式检查（`==` 比较字符串、自我赋值、自我比较） |

修改 `jdkHome`、`maven.*`、`gradle.*` 会触发重新导入工程。

## 工程配置：`java-analyzer.toml`

放在工作区根目录。用于没有 Maven / Gradle 的工程，或覆盖自动发现的 JDK。

```toml
[jdk]
home = "/Library/Java/JavaVirtualMachines/temurin-21.jdk/Contents/Home"

[maven]
settings = "/opt/apache-maven-3.8.4/conf/settings.xml"   # 同 maven.settings
local_repository = "/opt/apache-maven-3.8.4/repository"  # 同 maven.localRepository

[[module]]
name = "app"
root = "."                       # 相对工作区根目录，默认就是根目录
sources = ["src"]
test_sources = ["test"]
classpath = ["lib/*.jar", "/opt/libs/guava.jar"]
language_level = 21
preview = false                  # 是否开启预览特性（相当于 javac --enable-preview）
output = "out/classes"           # 编译输出目录，调试器（java-analyzer dap）拼运行时类路径时用
test_output = "out/test-classes" # 不写时按 target/classes、build/classes/java/main、bin 等约定找
```

只要存在 `[[module]]`，就不再尝试 Maven / Gradle 导入。只写 `[jdk]` 或 `[maven]` 时构建系统照常导入。

`[maven]` 的两项优先于编辑器配置里的 `maven.settings` / `maven.localRepository`（逐项比较，没写的项用编辑器配置的），
相对路径相对工作区根目录。多根工作区取第一个写了 `[maven]` 的根。

### JDK 的选择

显式配置的 JDK 总是优先：先看 `java-analyzer.toml` 的 `[jdk] home`，再看服务器选项 `jdkHome`。
路径有效就直接用，不管它的版本。

都没有配置时自动挑选：

1. 先算工程要求的版本：Maven 的 `maven-toolchains-plugin` 写了
   `<toolchains><jdk><version>` 就用它（区间如 `[1.8,9)` 取下界），否则取所有模块语言级别
   （含测试代码的级别）里最高的。一个工作区只用一个 JDK，取最高的级别是因为低于某个模块
   语言级别的 JDK 编译不了、也运行不了它的类，而高版本的 JDK 能按低级别编译。
2. 在 `JAVA_HOME` 和下面这些位置找到的 JDK 里，取版本恰好等于它的；没有就取不低于它的
   最低版本。版本相同时 `JAVA_HOME` 优先，完整的 JDK 优先于 JRE。
   - macOS：`/usr/libexec/java_home`、`/Library/Java/JavaVirtualMachines`
   - Windows：`Program Files` 下的 `Java`、`Eclipse Adoptium`、`Eclipse Foundation`、
     `AdoptOpenJDK`、`Microsoft`、`Zulu`、`Amazon Corretto`、`BellSoft`、`Semeru`
   - Linux：`/usr/lib/jvm`
   - 用户目录：SDKMAN（`~/.sdkman/candidates/java`）、`~/.jdks`、Gradle toolchain
     （`~/.gradle/jdks`）、mise、asdf
3. 没有要求的版本（模块都没写语言级别），或者找到的 JDK 都比它低时：用 `JAVA_HOME`，
   没有设置时用找到的最高版本。

JDK 的版本从它的 `release` 文件读（JDK 6 没有这个文件，读 `rt.jar` 清单里的版本）。
最终选中的 JDK 低于某个模块的语言级别时会记一条警告日志（`JA_LOG`），
`java-analyzer/projectClasspath` 的结果里也会带上 `jdkWarning`。
Maven 的 `<activation><jdk>` 按 `JAVA_HOME`（没有设置时按找到的最高版本）判断，
和用 `JAVA_HOME` 运行 Maven 时一样。

### 语言级别和预览特性

每个模块的语言级别决定哪些语法可以用：比如语言级别 8 的模块里写 record、`var`、文本块
会报 `feature-not-available`。语言级别来自：

- Maven：`maven-compiler-plugin` 的 `<release>` / `<source>`，或 `maven.compiler.release` /
  `maven.compiler.source` / `java.version` 属性；
- Gradle：`java.sourceCompatibility`；
- `java-analyzer.toml`：`language_level`。

都没有时按 JDK 的版本算。预览特性（例如模式里的基本类型）只有在模块开启了预览、并且语言级别
等于 JDK 版本时才能用，和 javac 的要求一致。开启预览的方式：

- Maven：`maven-compiler-plugin` 的 `<enablePreview>true</enablePreview>`，或 `<compilerArgs>`
  里有 `--enable-preview`，或属性 `maven.compiler.enablePreview=true`；
- Gradle：`JavaCompile` 任务的 `options.compilerArgs` 里有 `--enable-preview`；
- `java-analyzer.toml`：`preview = true`。

## 工程导入的行为

- **Maven**：直接读取 POM（父 POM、属性、dependencyManagement、BOM、scope、exclusion、
  多模块），依赖从本地仓库（见 `maven.localRepository`）解析，不联网。本地仓库缺构件时才调用 `mvn`
  （见 `maven.useCli`）。每次调用 `mvn` 都记日志：原因、完整命令行和用时，失败时是警告；
  用 `JA_LOG=project_model=info` 还能看到每次 Maven 导入的模块数、本地仓库、静态解析用时和缺的构件数。
- **Gradle**：通过 init script 让 `./gradlew`（没有 wrapper 时用 `gradle`）导出各 source set
  的源码目录和编译 classpath，以及工程的 `group` / `name`（每个子工程一个导出任务 `javaAnalyzerModel`，
  只解析依赖、不编译；Groovy 和 Kotlin DSL 都可以，已在 Gradle 9 上验证）。解析不到的依赖不影响
  其余的 classpath，会被记下来供多根工作区链接。结果按构建文件内容缓存，构建文件不变时
  启动不会运行 Gradle。
  - 组合构建：`includeBuild(...)` 引入的构建里的工程也作为模块导入，按坐标替换的依赖直接指向
    这些模块的源码；被包含构建的构建文件变化同样会触发重新导入。
  - `buildSrc`：作为一个单独的模块导入（带着 Gradle API 等依赖），其中的 Java 代码照常分析；
    它只给构建脚本用，其他模块看不到它的类。
- **都没有**：没有 `java-analyzer.toml` 时，在四层目录以内查找 Maven / Gradle 工程或手动配置，
  跳过隐藏目录、`target`、`build`、`node_modules` 和符号链接。找到工程根就不继续向下搜索，
  按多根工作区合并；没有找到时仍按目录约定找源码根（`src/main/java`、`src/test/java`、`src`）。
- `pom.xml`、`*.gradle(.kts)`、`gradle.properties`、`libs.versions.toml`、`java-analyzer.toml`
  变化后自动重新导入。
- `target/generated-sources/*`、`build/generated/sources/*` 下的代码作为源码参与分析。

## 多根工作区

客户端传入多个 workspace folder 时，每个文件夹按上面的规则各自导入，再合并：模块全部保留，
同一个 jar 只索引一次。JDK 取第一个在 `java-analyzer.toml` 里写了 `[jdk]` 的文件夹；都没写时，
设置了 `jdkHome` 就用它，否则按所有文件夹里要求的最高版本挑选（规则同上）。一个文件夹里的模块按坐标依赖另一个文件夹里的模块时，会改成直接依赖那个模块的源码，
而不是仓库里的 jar；依赖没有发布、解析不到时也一样，被依赖模块自己的依赖跟着传递过来。
模块的坐标：Maven 模块是 `groupId:artifactId`，Gradle 工程是 `group:name`（没有设置 `group` 的不参与），
Maven 和 Gradle 之间也能互相链接。
运行中增删文件夹（`workspace/didChangeWorkspaceFolders`）会触发重新导入。

## 微服务之间的 HTTP 调用

Spring Cloud OpenFeign 的 `@FeignClient` 接口和 Spring 6 的 HTTP 接口（`@HttpExchange`、`@GetExchange` …）
里的方法按 HTTP 方法和路径（类上的前缀、`@FeignClient` 的 `path` 和 `url` 里的路径、方法上的路径；
`{id}`、`{id:\d+}` 这样的路径变量当作通配）和工作区里的服务端端点（Spring MVC、JAX-RS）对应：

- 在客户端方法的名字或映射注解的路径上跳转到定义 / 实现，到达对应的控制器方法；
- 在控制器方法上查找引用，结果里包括对应的客户端方法；
- 悬停客户端方法时列出对应的端点，悬停控制器方法时显示它的路由。

`@FeignClient` 的 `name` / `value`（支持 `${key:default}`）和某个模块 `application*.yml` /
`.properties` 里的 `spring.application.name` 相同时，只看这个模块和它依赖的模块里的端点；
服务端配置了 `server.servlet.context-path` 时，带着这个前缀的客户端路径也能对上。
只看注解的写法，Spring 的类不需要在类路径上。

## Spring Bean 注入

工作区里的这些定义算作 Bean：

- 带 `@Component`、`@Service`、`@Repository`、`@Controller`、`@RestController`、`@Configuration`
  （以及 `@ControllerAdvice`、`@SpringBootApplication`、JSR-330 的 `@Named` 等）的具体类，带着
  工作区里被这些注解标注过的自定义注解（如 `@Service` 标注的 `@DomainService`）的类也算；
  Bean 名取注解的 `value`，没写时是首字母小写的类名；
- `@Bean` 方法：Bean 名取 `@Bean` 的 `name` / `value`，没写时是方法名，类型是返回类型；
- 继承 Spring Data `Repository` 的接口，以及 `@FeignClient`、`@Mapper` 接口。

注入点：带 `@Autowired` / `@Inject` / `@Resource` 的字段；带 `@Autowired` / `@Inject` 的方法
（setter 等）的形参；Bean 类的构造器形参（只有一个构造器时就是它，否则是带 `@Autowired` 的那个；
没有写构造器时，Lombok `@RequiredArgsConstructor` / `@AllArgsConstructor` 生成的构造器对应的
字段）；构造器把这些形参赋给的字段（`this.repo = repo`）；`@Bean` 方法的形参。带 `@Value` 的形参不算。

候选按类型找（泛型实参也比较，`Repository<Owner>` 不会收到 `Repository<Pet>` 的实现），再依次按
`@Qualifier` / `@Named`（对上 Bean 的 `@Qualifier` 或 Bean 名）、`@Resource(name = ...)`（没写
`name` 时先按字段名找）、`@Primary`、字段或形参名收窄；`List<Foo>`、`Set<Foo>`、`Map<String, Foo>`、
`Foo[]` 收到全部候选，`Optional<Foo>`、`ObjectProvider<Foo>` 按 `Foo` 找。只看注入点所在模块和它
依赖的模块里的 Bean，测试代码里的 Bean 只对测试代码可见。

- 在注入点（声明处或使用处的字段名、形参名）上跳转到实现，列出它收到的 Bean 定义；
- 悬停注入点时列出收到的 Bean，悬停 Bean 类或 `@Bean` 方法时显示 Bean 名；
- 在 Bean 类或 `@Bean` 方法上查找引用，结果里包括收到它的注入点（构造器形参，不重复列出被赋值的字段）。

依赖库里的自动配置等提供的 Bean 看不到，所以不报"找不到 Bean"或"Bean 不唯一"之类的诊断；
`@Profile`、`@Conditional…`、自定义的限定注解，以及 XML 或代码里注册的 Bean 不在考虑之内。

## Lombok

工作区里的 `lombok.config`（各模块根目录以及往上直到仓库根目录，还有源码目录里各层的）会被读取，
影响生成的成员：`lombok.accessors.chain` / `fluent` / `prefix`、`lombok.getter.noIsPrefix`、
`lombok.log.fieldName`。

和 Lombok 一样按目录生效：一个 `lombok.config` 作用于它所在目录及其下的源文件。从源文件所在的目录
往上，所有找到的文件由外往里叠加，里层的覆盖外层的；`+=`、`-=` 在外层的值上增删，`clear` 清掉外层
的设置。某个文件写了 `config.stopBubbling = true` 时，再往上的文件不再生效。修改一个 `lombok.config`
只影响它管辖的目录。

## import 的分组顺序：`.editorconfig`

整理 import 和自动添加 import 按 `.editorconfig` 里对 `*.java` 生效的 `ij_java_imports_layout`
分组排序，例如：

```ini
[*.java]
ij_java_imports_layout = *,|,javax.**,java.**,|,$*
```

- `java.**`：这个包和它的子包；`java.*`：只有这个包；`*`：其余的 import；
- 前面带 `$` 的是静态 import（`$*` 是全部静态 import）；
- `|`：组之间空一行；一条 import 归到包名最长的那个匹配的组，组内按全名排序。

读取各模块根目录以及往上直到仓库根目录的 `.editorconfig`，还有源码目录里各层的。按目录生效：一个文件
适用的是它所在目录和上面各级目录里的 `.editorconfig`，里层目录的覆盖外层的。
没有配置时：普通 import 一组，空一行，静态 import 一组。
`ij_java_class_count_to_use_import_on_demand = N` 时，整理 import 把同一个包里用到的类达到 N 个的
单独 import 合并成 `包.*`，用到的类不到 N 个的 `包.*` 展开成单独的 import（例如设成 999 就是
不用通配符 import）。合并和展开都不会改变名字解析到的类：同包里、`java.lang` 里或别的通配符包里
也有同名类时，这个名字保留单独的 import。没有配置时不合并也不展开。
`ij_java_names_count_to_use_static_import_on_demand = N` 对静态 import 做同样的事：同一个类里用到的
静态成员达到 N 个时合并成 `import static 类.*;`，不到 N 个时展开；合并后带进来的名字和别的
`import static 其它类.*;` 里的重名、或者展开的名字别的类里也有时，保持原样。

## 代码风格：`.editorconfig`

格式化（整个文件、选中范围、输入时）按 `.editorconfig` 里对 `*.java` 生效的设置排版。读取的文件和
import 布局相同，也按目录生效：源文件所在目录和上面各级目录里的，里层目录的覆盖外层的，同一文件里后面的节
覆盖前面的，`root = true` 之前的文件不再生效，值为 `unset` 表示取消外层的设置。
`.editorconfig` 没有设置的缩进项用编辑器传来的 tabSize / insertSpaces。

```ini
[*.java]
indent_style = space
indent_size = 4
ij_continuation_indent_size = 8
ij_java_keep_blank_lines_in_code = 1
ij_java_blank_lines_around_method = 1
ij_java_space_before_if_parentheses = true
ij_java_brace_style = end_of_line
```

缩进与文件：

| 键 | 默认 | 说明 |
| --- | --- | --- |
| `indent_style` | 编辑器设置 | `space` / `tab`；用制表符时凑不满一个制表符的零头用空格 |
| `indent_size` | 编辑器设置 | 一级缩进的列数，`tab` 表示等于 `tab_width` |
| `tab_width` | 同 `indent_size` | 一个制表符占的列数 |
| `ij_continuation_indent_size`（或 `ij_java_continuation_indent_size`） | 两级缩进（8） | 续行缩进的列数 |
| `ij_java_indent_case_from_switch` | `true` | `case` 比 `switch` 多缩进一级 |
| `ij_java_do_not_indent_top_level_class_members` | `false` | 顶层类的成员不缩进 |
| `trim_trailing_whitespace` | `true` | 去掉代码行末尾的空白（空行里的空白总是去掉） |
| `insert_final_newline` | `false` | 文件末尾没有换行时补一个（编辑器要求时也补） |
| `max_line_length` | 不折行 | 右边界：设置之后，更长的代码行在格式化时折开（见下）；不设置或 `off` 表示不折行 |
| `ij_java_binary_operation_sign_on_next_line` | `false` | 在二元运算符处折行时，运算符放到下一行开头 |

空行。`keep_*` 是最多保留几个连续空行，多出来的删掉；`blank_lines_*` 是类的成员之间至少几个空行，
不够时在成员（连同它前面的注释、注解）之前补上，不会删除空行，也不会拆开写在同一行上的成员。
输入时的格式化不补空行。

| 键 | 默认 |
| --- | --- |
| `ij_java_keep_blank_lines_in_code`（方法体等代码里） | 2 |
| `ij_java_keep_blank_lines_in_declarations`（类体里、文件顶层） | 2 |
| `ij_java_keep_blank_lines_before_right_brace`（`}` 之前） | 2 |
| `ij_java_blank_lines_after_class_header`（类头之后第一个成员之前） | 0 |
| `ij_java_blank_lines_around_class`（嵌套类） | 1 |
| `ij_java_blank_lines_around_field` / `_around_field_in_interface` | 0 / 0 |
| `ij_java_blank_lines_around_method` / `_around_method_in_interface` | 1 / 1 |
| `ij_java_blank_lines_around_initializer` | 1 |

两个相邻成员之间取两者要求的较大值；枚举常量之后的第一个成员不做要求。

空格（值为 `true` / `false`，默认是常见的 Java 写法）：

- 括号之前：`ij_java_space_before_method_call_parentheses`（`false`）、
  `ij_java_space_before_method_parentheses`（`false`）、
  `ij_java_space_before_annotation_parameter_list`（`false`）、
  `ij_java_space_before_{if,for,while,switch,try,catch,synchronized}_parentheses`（`true`）；
- 括号之内：`ij_java_space_within_parentheses`（表达式外的括号）、
  `ij_java_space_within_method_call_parentheses`、`ij_java_space_within_empty_method_call_parentheses`、
  `ij_java_space_within_method_parentheses`、`ij_java_space_within_empty_method_parentheses`、
  `ij_java_space_within_{if,for,while,switch,try,catch,synchronized}_parentheses`、
  `ij_java_space_within_cast_parentheses`、`ij_java_space_within_annotation_parentheses`、
  `ij_java_space_within_brackets`（下标和数组维度），都默认 `false`；
- 运算符两边：`ij_java_space_around_{assignment,logical,equality,relational,bitwise,additive,multiplicative,shift}_operators`、
  `ij_java_space_around_lambda_arrow`、`ij_java_space_around_annotation_eq`（`true`）、
  `ij_java_space_around_unary_operator`、`ij_java_space_around_method_ref_dbl_colon`（`false`）；
- 三目运算符：`ij_java_space_before_quest` / `_after_quest` / `_before_colon` / `_after_colon`（`true`），
  增强 `for` 的 `:` 之前：`ij_java_space_before_colon_in_foreach`（`true`）；
- 逗号、分号、强制转换：`ij_java_space_before_comma`（`false`）、`ij_java_space_after_comma`（`true`）、
  `ij_java_space_before_semicolon`（`false`）/ `ij_java_space_after_semicolon`（`true`，`for (;;)` 里）、
  `ij_java_space_after_type_cast`（`true`）；
- `{` 之前：`ij_java_space_before_{class,method,if,else,for,while,do,switch,try,catch,finally,synchronized}_left_brace`（`true`）；
- `}` 之后的关键字之前：`ij_java_space_before_{else,catch,finally,while}_keyword`（`true`）。

花括号的位置：`ij_java_class_brace_style`（类、接口、枚举、记录）、`ij_java_method_brace_style`
（方法、构造器）、`ij_java_brace_style`（`if` / `for` / `while` / `try` / `switch` 等语句和静态
初始化块），值为 `end_of_line`（放在行尾）、`next_line`（单独一行，与声明或语句的起始行对齐）或
`next_line_if_wrapped`（声明或语句头折了行时单独一行）。没有设置时 `{` 保持原样；lambda、匿名类、
数组初始化器的 `{` 以及 `{` 和前面之间隔着注释的不挪动。输入时的格式化不挪动 `{`。

折行：整个文件或选中范围格式化时，代码部分超过 `max_line_length` 的行会被断开（只断不并，已经
手工折好的行保持原样，行尾注释超出不算；输入时的格式化不折行）。先在括号嵌套最浅的位置断：
实参 / 形参 / 注解参数表的 `(` 和 `,` 之后、链式调用 `)` 之后的 `.` 之前、类型声明的
`extends` / `implements` / `permits` 和方法的 `throws` 之前（以及这些列表的 `,` 之后）、三目运算符的
`?` / `:` 之前、二元运算符处（`||` 先于 `&&` 先于其他运算符）；没有这些位置时才在赋值的 `=` 之后断。
同一组位置里每行尽量填满，断出来的行用续行缩进；还超长的再往里一层断。字符串字面量等本身放不下的
内容不会被拆开。

## 缓存

都在系统缓存目录的 `java-analyzer/` 下（Linux：`~/.cache`，macOS：`~/Library/Caches`）：

- `index/`：类路径索引；
- `gradle/`：Gradle 导入结果；
- `sources/`：依赖库的源码 / 签名桩。

缓存可以随时删除，下次启动会重建。

## 界面语言

诊断、提示等面向用户的文字在语言以 `zh` 开头时用中文，否则用英文：语言服务器跟随客户端
`initialize` 里的 `locale`，命令行工具看 `LC_ALL` / `LC_MESSAGES` / `LANG`。
