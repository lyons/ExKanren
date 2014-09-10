defmodule DocTest do
  use ExUnit.Case
  
  doctest MicroKanren
  
  doctest MiniKanren
  doctest MiniKanren.Functions
  doctest MiniKanren.CLP.Tree
end