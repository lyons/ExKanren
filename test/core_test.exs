defmodule MKCoreTest do
  use ExUnit.Case
  
  require MiniKanren
  import  MiniKanren
  import  MiniKanren.Functions
  
  defp empty_substitution, do: HashDict.new
  defp just_subs({subs, _}), do: subs
  defp just_subs(nil), do: nil
    
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
    assert(unify(var(0), var(0), empty_substitution) ==
           {empty_substitution, []})
  end
  
  test "unifying two distinct vars" do
    ls = [{var(0), var(1)}]
    result = Enum.into(ls, HashDict.new)
    assert(unify(var(0), var(1), empty_substitution) |> just_subs |> Enum.sort == result |> Enum.sort)
    
    assert(unify(var(1), var(0), unify(var(0), var(1), empty_substitution)) |> just_subs |> Enum.sort == result |> Enum.sort)
  end
  
  test "unifying lists" do
    result = Enum.into([{var(0), 2}, {var(1), 1}], HashDict.new)
    assert(unify([1, var(0)], [var(1), 2], empty_substitution) |> just_subs |> Enum.sort == result |> Enum.sort)
    assert(unify([1, var(0)], [2, 3],      empty_substitution) |> just_subs == nil)
    assert(unify([1, var(0)], [1, 2, 3],   empty_substitution) |> just_subs == nil)
  end
  
  test "unifying 2-tuples" do
    result = Enum.into([{var(0), 2}, {var(1), 1}], HashDict.new)
    assert(unify({1, var(0)}, {var(1), 2}, empty_substitution) |> just_subs |> Enum.sort == result |> Enum.sort)
    assert(unify({1, var(0)}, {2, 2},      empty_substitution) |> just_subs == nil)
  end
  
  test "unifying 3-tuples" do
    result = Enum.into([{var(0), 2}, {var(1), 1}], HashDict.new)
    assert(unify({var(0), :foo, 1}, {2, :foo, var(1)}, empty_substitution) |> just_subs |> Enum.sort == result |> Enum.sort)
    assert(unify({var(0), :foo, 1}, {2, :bar, var(1)}, empty_substitution) |> just_subs == nil)
  end
  
  test "unify returns log of new substitutions" do
    {x_s, x_l} = unify(var(0), var(1), empty_substitution)
    {y_s, y_l} = unify([var(2), var(3)], [:foo, var(1)], x_s)
    
    assert(x_l == [{var(0), var(1)}])
    assert(Enum.sort(y_l) == Enum.sort([{var(2), :foo}, {var(3), var(1)}]))
    assert(y_s |> Enum.sort == Enum.into([{var(2), :foo}, {var(3), var(1)}, {var(0), var(1)}], HashDict.new) |> Enum.sort)
  end
  
  test "allow for single-case conde" do
    assert [_]  = ( run_all [],  do: ( conde do: [succeed] ) )
    assert []  == ( run_all [],  do: ( conde do: [fail]    ) )
    assert [1] == ( run_all [q], do: ( conde do: [eq(q,1)] ) )
  end
end
