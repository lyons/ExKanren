defmodule MKImpureTest do
  use ExUnit.Case
  use MiniKanren
  
  test "conda ignores clauses after first success" do
    result = run_all([x]) do
      conda do
        [eq(1, 2)]
        [eq(x, "First success")]
        [eq(x, "Second succeed")]
      end
    end
    
    assert(result == ["First success"])
  end
  
  test "condu ignores clauses after first success" do
    result = run_all([x]) do
      condu do
        [eq(1, 2)]
        [membero(x, [4, 5, 6])]
        [membero(x, [1, 2, 3])]
      end
    end
    
    assert(result == [4])
  end
  
  test "onceo succeeds at most once" do
    result = run_all([x]) do
      onceo(membero(x, [1, 2, 3, 4, 5]))
    end
    
    assert(result == [1])
  end
  
  test "copy_term always makes fresh copies" do
    [{y, z}] = run_all([out, a, b, x, y, z]) do
      eq(x, [a, 2, b])
      copy_term(x, y)
      copy_term(x, z)
      eq(out, {y, z})
    end
    
    assert(y != z)
  end
end