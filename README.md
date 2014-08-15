ExKanren
========

Relational programming in Elixir, providing implementations of both µKanren (as described in *[μKanren: A Minimal Functional Core
for Relational Programming](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf)*), and miniKanren (mostly as described in *[Relational Programming in miniKanren: Techniques, Applications, and Implementations](https://scholarworks.iu.edu/dspace/bitstream/handle/2022/8777/Byrd_indiana_0093A_10344.pdf)*).

## Usage

`MicroKanren` provides an implementation of µKanren that uses `HashDicts` instead of lists to store substitutions.

`MicroKanren.Reference` is a direct translation of the implementation in *[μKanren: A Minimal Functional Core
for Relational Programming](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf)*, and is included for completeness.

`MiniKanren.Core` defines the basic operators of core miniKanren, and `MiniKanren.Core.Functions` implements some of the common relations used in core miniKanren. `use(MiniKanren, :core)` will import both `Core` and `Core.Functions`.

`MiniKanren.Impure` defines the impure operators `conda`, `condu`, and `project`. `MiniKanren.Impure.Functions` implements `onceo` and `copy_term`, as well as a few impure functions borrowed from  [core.logic](https://github.com/clojure/core.logic). `use(MiniKanren, :impure)` will import both core miniKanren and the impure extensions.

```elixir
use(MiniKanren, :core)
run_all([out, x, y]) do
  eq(out, {x, y})
  membero(x, [:a, :b, :c])
  conde do
    [eq("Foo", y)]
    [eq(x, :b), eq(y, "Bar")]
  end
end
# [a: "Foo", b: "Foo", b: "Bar", c: "Foo"]
```

## Todo

*   Document internal functions in miniKanren, docs and tests for µKanren
*   Non-trivial examples
*   Disequality constraints for miniKanren
*   cKanren, αKanren
