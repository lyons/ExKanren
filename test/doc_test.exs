defmodule DocTest do
  use ExUnit.Case
  
  doctest MicroKanren
  
  doctest MiniKanren.Core
  doctest MiniKanren.Core.Functions
  doctest MiniKanren.Impure
  doctest MiniKanren.Impure.Functions
end