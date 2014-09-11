defmodule CLPFDTest do
  use ExUnit.Case
  use MiniKanren
  import MiniKanren.CLP.FD
  
  # Test cases get run in their own process, so we need to ensure each test case adds the correct
  # hooks to its process dictionary.
  
  test "dom assigns a domain" do
    use MiniKanren.CLP.FD, :hooks
    
    x = run_all([out]) do
      dom(out, 1..5)
    end
    
    y = run_all([out]) do
      dom(out, [-1, 0, 1, 2, 3])
    end
    
    assert(x == [1, 2, 3, 4, 5])
    assert(y == [-1, 0, 1, 2, 3])
  end
  
  test "in_fd assigns a domain to multiple variables" do
    use MiniKanren.CLP.FD, :hooks
    
    x = run_all([out, x, y]) do
      eq(out, [x, y])
      in_fd([x, y], 2..4)
    end |> Enum.sort
    
    assert(x == [[2, 2], [2, 3], [2, 4], [3, 2], [3, 3], [3, 4], [4, 2], [4, 3], [4, 4]])
  end
  
  test "force_answer doesn't force irrelevant variables" do
    use MiniKanren.CLP.FD, :hooks
    
    x = run_all([out, x, y]) do
      eq(out, x)
      in_fd([x, y], 2..4)
    end
    
    assert(x == [2, 3, 4])
  end
  
  test "lt_fd" do
    use MiniKanren.CLP.FD, :hooks
    
    x = run_all([out, x, y]) do
      eq(out, x)
      dom(x, 1..5)
      dom(y, 1..5)
      lt_fd(x, y)
    end
    
    y = run_all([out, x, y]) do
      eq(out, x)
      dom(x, 1..5)
      dom(y, 1..6)
      lt_fd(x, y)
    end
    
    assert(x == [1, 2, 3, 4])
    assert(y == [1, 2, 3, 4, 5])
  end
  
  test "lte_fd" do
    use MiniKanren.CLP.FD, :hooks
    
    x = run_all([out, x, y]) do
      eq(out, x)
      dom(x, -5..-1)
      dom(y, -3..-1)
      lte_fd(x, y)
    end
    
    assert(x == [-5, -4, -3, -2, -1])
  end
  
  test "gt_fd" do
    use MiniKanren.CLP.FD, :hooks
    
    x = run_all([out, x, y]) do
      eq(out, x)
      dom(x, 1..10)
      dom(y, [5])
      gt_fd(x, y)
    end
    
    y = run_all([out, x, y]) do
      eq(out, x)
      dom(x, 5..10)
      dom(y, [4])
      gt_fd(x, y)
    end
    
    assert(x == [6, 7, 8, 9, 10])
    assert(y == [5, 6, 7, 8, 9, 10])
  end
  
  test "gte_fd" do
    use MiniKanren.CLP.FD, :hooks
    
    x = run_all([out, x, y]) do
      eq(out, x)
      dom(x, 1..10)
      dom(y, [5])
      gte_fd(x, y)
    end
    
    assert(x == [5, 6, 7, 8, 9, 10])
  end
  
  test "sum_fd" do
    use MiniKanren.CLP.FD, :hooks
    
    x = run_all([out, x, y, z]) do
      eq(out, x)
      sum_fd(x, y, z)
      dom(x, 1..10)
      dom(y, -3..-1)
      dom(z, -2..2)
    end
    
    y = run_all([out, x, y, z]) do
      eq(out, y)
      sum_fd(x, y, z)
      dom(x, 1..3)
      dom(y, -10..-1)
      dom(z, -2..2)
    end
    
    z = run_all([out, x, y, z]) do
      eq(out, z)
      sum_fd(x, y, z)
      dom(x, 1..3)
      dom(y, -3..-1)
      dom(z, -10..10)
    end
    
    assert(x == [1, 2, 3, 4, 5])
    assert(y == [-5, -4, -3, -2, -1])
    assert(z == [-2, -1, 0, 1, 2])
  end
    
#  test "product_fd" do
#    use MiniKanren.CLP.FD, :hooks
#    
#    assert(1 == 1)
#  end
  
  test "neq_fd" do
    use MiniKanren.CLP.FD, :hooks
    
    x = run_all([out, x, y]) do
      eq(out, [x, y])
      neq_fd(x, y)
      in_fd([x, y], 1..3)
    end |> Enum.sort
    
    assert(x == [[1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [3, 2]])
  end
  
  test "distinct_fd" do
    use MiniKanren.CLP.FD, :hooks
    
    x = run_all([out, x, y]) do
      eq(out, [x, y])
      distinct_fd([x, y])
      in_fd([x, y], 1..3)
    end |> Enum.sort
    
    y = run_all([out, x, y]) do
      eq(out, [x, y])
      distinct_fd([x, y, 3])
      in_fd([x, y], 1..3)
    end |> Enum.sort
    
    z = run_all([out, x, y, z]) do
      eq(out, [x, y, z])
      distinct_fd([x, y, z])
      in_fd([x, y, z], 1..3)
    end |> Enum.sort
    
    assert(x == [[1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [3, 2]])
    assert(y == [[1, 2], [2, 1]])
    assert(z == [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]])
  end
  
  test "multiply range" do
    assert(multiply_range(1, 4, 2, 5)     == range(2, 20))
    assert(multiply_range(1, 4, -2, 5)    == range(-8, 20))
    assert(multiply_range(1, 4, -5, -2)   == range(-20, -2))
    assert(multiply_range(-1, 4, 2, 5)    == range(-5, 20))
    assert(multiply_range(-1, 4, -2, 5)   == range(-8, 20))
    assert(multiply_range(-4, 1, -5, 2)   == range(-8, 20))
    assert(multiply_range(-1, 4, -5, -2)  == range(-20, 5))
    assert(multiply_range(-4, -1, 2, 5)   == range(-20, -2))
    assert(multiply_range(-4, -1, -2, 5)  == range(-20, 8))
    assert(multiply_range(-4, -1, -5, -2) == range(2, 20))
  end
  
  test "divide range" do
    assert(divide_range(1, 20, 2, 5)  == range(1, 10))
    assert(divide_range(3, 20, 2, 5)  == range(1, 10))
    assert(divide_range(6, 20, 2, 5)  == range(2, 10))
    assert(divide_range(11, 30, 2, 5) == range(3, 15))
    assert(divide_range(11, 31, 3, 7) == range(2, 10))
    
    assert(divide_range(1, 10, -5, 5) == range(-10, 10))
    assert(divide_range(8, 10, -5, 5) == range(-10, 10))
    assert(divide_range(8, 10, -7, 5) == range(-10, 10))
    assert(divide_range(8, 10, -7, 7) == range(-10, 10))
    
    assert(divide_range(2, 20, -5, -3) == range(-6, -1))
    assert(divide_range(4, 20, -5, -3) == range(-6, -2))
    assert(divide_range(4, 25, -5, -3) == range(-8, -2))
    assert(divide_range(4, 27, -5, -3) == range(-9, -2))
    assert(divide_range(2, 20, -7, -4) == range(-5, -1))
    
    assert(divide_range(-10, 10, 2, 5) == range(-5, 5))
    assert(divide_range(-10, 10, 3, 5) == range(-3, 3))
    assert(divide_range(-10, 6, 3, 50) == range(-3, 2))
    assert(divide_range(-11, 6, 3, 50) == range(-3, 2))
    
    assert(divide_range(-10, 2, -4, 8)   == range(-10, 10))
    assert(divide_range(-10, 20, -4, 8)  == range(-20, 20))
    assert(divide_range(-10, 20, -50, 2) == range(-20, 20))
    assert(divide_range(-10, 2, -50, 60) == range(-10, 10))
    
    assert(divide_range(-10, 10, -5, -2)  == range(-5, 5))
    assert(divide_range(-10, 10, -40, -2) == range(-5, 5))
    assert(divide_range(-10, 10, -40, -3) == range(-3, 3))
    assert(divide_range(-10, 5, -40, -3)  == range(-1, 3))
    assert(divide_range(-10, 6, -40, -3)  == range(-2, 3))
    
    assert(divide_range(-20, -8, 2, 5)  == range(-10, -2))
    assert(divide_range(-20, -8, 3, 5)  == range(-6, -2))
    assert(divide_range(-32, -13, 3, 7) == range(-10, -2))
    
    assert(divide_range(-20, -8, -5, 5)   == range(-20, 20))
    assert(divide_range(-30, -1, -50, 50) == range(-30, 30))
    
    assert(divide_range(-20, -12, -4, -2) == range(3, 10))
    assert(divide_range(-20, -15, -5, -2) == range(3, 10))
    assert(divide_range(-20, -16, -5, -2) == range(4, 10))
    assert(divide_range(-20, -12, -4, -3) == range(3, 6))
    assert(divide_range(-21, -12, -5, -3) == range(3, 7))
    assert(divide_range(-22, -12, -5, -3) == range(3, 7))
  end
end