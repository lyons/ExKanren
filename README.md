ExKanren
========

Relational programming in Elixir based on miniKanren.

## What's new
* 2015-06-30: Overhauled `CLP_Tree` module, added `symbolo`, `numbero`, `booleano`, `absento` operators. Fixed erros in the stream operators. Tidied up core. Made bigger mess in `CLP_FD`.
* 2015-03-10: The constraint solver being used is now passed as an optional parameter to the `run` interface rather than being set in the process dictionary. This makes ExKanren purely functional and enables experimenting with running goals in parallel.
* 2014-09-17: Constraints over finite domains of integers now implemented
* 2014-09-09: Working through the cKanren paper, CLP(Tree) is now implemented

## TODO
* Urgently need more thorough documentation
* Nominal logic

## Usage
`MiniKanren` defines the relational and non-relational operators of miniKanren, and `MiniKanren.Functions` implements some of the common relations. `use MiniKanren` will import both `MiniKanren` and `MiniKanren.Functions`.

`MiniKanren.CLP.Tree` provides the tree disequality operator `neq`. `use MiniKanren.CLP.Tree` will import the operator and some common relations that rely on it, and for convenience will alias `MiniKanren.CLP.Tree` to `CLP_Tree`.

`MiniKanren.CLP.FD` provides operators for operations on finite domains of integers. `use MiniKanren.CLP.FD` will import the operator and some common relations that rely on it, and for convenience will alias `MiniKanren.CLP.FD` to `CLP_FD`. 

```elixir
use MiniKanren
use MiniKanren.CLP.Tree
run_all(CLP_Tree, [out, x]) do
  eq(x, [:good_night, :kittens, :good_night, :mittens,
         :good_night, :clocks, :good_night, :socks])
  rembero(:good_night, x, out)
end
# [:kittens, :mittens, :clocks, :socks]
```

## References
This code is based on reading and figuring out a bunch of papers &c:

* [miniKanren Live and Untagged: Quine Generation via Relational Interpreters](http://webyrd.net/quines/quines.pdf)
* [cKanren: miniKanren with Constraints](http://scheme2011.ucombinator.org/papers/Alvis2011.pdf)
* [μKanren: A Minimal Functional Core for Relational Programming](http://webyrd.net/scheme-2013/papers/HemannMuKanren2013.pdf)
* [Relational Programming in miniKanren: Techniques, Applications, and Implementations](https://scholarworks.iu.edu/dspace/bitstream/handle/2022/8777/Byrd_indiana_0093A_10344.pdf)
* [core.logic](https://github.com/clojure/core.logic)
