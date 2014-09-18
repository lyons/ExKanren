ExKanren
========

Relational programming in Elixir based on miniKanren.

## What's new
* 2014-17-2014: Constraints over finite domains of integers now impelemented
* 2014-09-2014: Working through the cKanren paper, CLP(Tree) is now implemented

## TODO
* Urgently need more thorough documentation
* Nominal logic

## Usage
`MiniKanren` defines the pure and impure operators of miniKanren, and `MiniKanren.Functions` implements some of the common relations. `use MiniKanren` will import both `MiniKanren` and `MiniKanren.Functions`.

`MiniKanren.CLP.Tree` provides the tree disequality operator `neq`, and the runtime hooks needed to use disequality constraints. `use MiniKanren.CLP.Tree` will import the operator and some common relations that rely on it and will set the process dictionary with the hooks needed to run CLP(Tree).

`MiniKanren.CLP.FD` provides operators for finite domains of integers, and the runtime hooks needed to use them. `use MiniKanren.CLP.FD` will import the operator and some common relations that rely on it and will set the process dictionary with the hooks needed to run CLP(FD). 

```elixir
use MiniKanren
use MiniKanren.CLP.Tree
run_all([out, x]) do
  eq(x, [:good_night, :kittens, :good_night, :mittens,
         :good_night, :clocks, :good_night, :socks])
  rembero(:good_night, x, out)
end
# [:kittens, :mittens, :clocks, :socks]
```

## References
This code is based on reading and figuring out a bunch of papers &c:

* [cKanren: miniKanren with Constraints](http://scheme2011.ucombinator.org/papers/Alvis2011.pdf)
* [μKanren: A Minimal Functional Core for Relational Programming](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf)
* [Relational Programming in miniKanren: Techniques, Applications, and Implementations](https://scholarworks.iu.edu/dspace/bitstream/handle/2022/8777/Byrd_indiana_0093A_10344.pdf)
* [core.logic](https://github.com/clojure/core.logic)