defmodule MKCoreTest do
  use ExUnit.Case
  
  require MiniKanren.Core
  import  MiniKanren.Core
  import  MiniKanren.Core.Functions
  
  defp empty_substitution, do: HashDict.new
    
  test "vars are vars" do
    assert(var?(var(0)))
  end
  
  test "occurs-check works on lists" do
    result = run_all([x, y, z]) do
      eq(x, [1, 2, y])
      eq(y, [1, 2, z])
      eq(z, x)
    end
    
    assert(result == [])
  end
  
  test "occurs-check works on 2-tuples" do
    result = run_all([x, y, z]) do
      eq(x, {1, y})
      eq(y, {1, z})
      eq(z, x)
    end
    
    assert(result == [])
  end
  
  test "occurs-check works on 3-tuples" do
    result = run_all([x, y, z]) do
      eq(x, {1, y, z})
      eq(y, {1, 2, z})
      eq(z, x)
    end
    
    assert(result == [])
  end
  
  test "unifying var with itself" do
    assert(unify(var(0), var(0), empty_substitution) == empty_substitution)
  end
  
  test "unifying two distinct vars" do
    result = HashDict.new([{var(0), var(1)}])
    assert(unify(var(0), var(1), empty_substitution) == result)
    
    assert(unify(var(1), var(0), unify(var(0), var(1), empty_substitution)) ==
           result)
  end
  
  test "unifying lists" do
    result = HashDict.new([{var(0), 2}, {var(1), 1}])
    assert(unify([1, var(0)], [var(1), 2], empty_substitution) == result)
    assert(unify([1, var(0)], [2, 3],      empty_substitution) == nil)
    assert(unify([1, var(0)], [1, 2, 3],   empty_substitution) == nil)
  end
  
  test "unifying 2-tuples" do
    result = HashDict.new([{var(0), 2}, {var(1), 1}])
    assert(unify({1, var(0)}, {var(1), 2}, empty_substitution) == result)
    assert(unify({1, var(0)}, {2, 2},      empty_substitution) == nil)
  end
  
  test "unifying 3-tuples" do
    result = HashDict.new([{var(0), 2}, {var(1), 1}])
    assert(unify({var(0), :foo, 1}, {2, :foo, var(1)}, empty_substitution) == result)
    assert(unify({var(0), :foo, 1}, {2, :bar, var(1)}, empty_substitution) == nil)
  end
end
