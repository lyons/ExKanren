defmodule DocTest do
  use ExUnit.Case
  
  doctest MicroKanren
  
  doctest MiniKanren
  doctest MiniKanren.Functions
end