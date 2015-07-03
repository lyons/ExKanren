defmodule CLP_Tree_Test do
  use ExUnit.Case
  
  use MiniKanren
  use MiniKanren.CLP.Tree
  
  test "Disequality constraints seem to work" do
    x = run_all(CLP_Tree, [out]) do
      neq(out, 2)
      conde do
        [eq(out, 1)]
        [eq(out, 2)]
        [eq(out, 3)]
      end
    end
    
    y = run_all(CLP_Tree, [out]) do
      conde do
        [eq(out, 1)]
        [eq(out, 2)]
        [eq(out, 3)]
      end
      neq(out, 2)
    end
    
    z = run_all(CLP_Tree, [out]) do
      neq(out, 2)
    end
    
    assert(x == [1, 3])
    assert(y == [1, 3])
    assert(z == [[:_0 | {:neq, [[{:_0, 2}]]}]])
  end
  
  test "Disequality constraints seem to work on complex terms" do
    x = run_all(CLP_Tree, [out, x, y]) do
      eq(out, [x, y])
      neq([x, y], [1, 2])
    end
    
    y = run_all(CLP_Tree, [out, x, y]) do
      eq(out, [x, y])
      neq([x, y], [1, 2])
      eq(x, 1)
    end
    
    z = run_all(CLP_Tree, [out, x, y]) do
      eq(out, [x, y])
      neq([x, y], [1, 2])
      eq(x, 3)
    end
    
    assert(x == [[[:_0, :_1] | {:neq, [[{:_0, 1}, {:_1, 2}]]}]])
    assert(y == [[[1, :_0]   | {:neq, [[{:_0, 2}]]}]])
    assert(z == [[3, :_0]])
  end
  
  test "Type constraints seem to work" do
    u = run_all(CLP_Tree, [out]) do
     symbolo(out)
    end
    
    v = run_all(CLP_Tree, [out]) do
      symbolo(out)
      eq(out, :owl)
    end
    
    w = run_all(CLP_Tree, [out]) do
      eq(out, :owl)
      symbolo(out)
    end
    
    x = run_all(CLP_Tree, [out]) do
      symbolo(out)
      eq(out, 5)
    end
    
    y = run_all(CLP_Tree, [out]) do
      eq(out, 5)
      symbolo(out)
    end
    
    z = run_all(CLP_Tree, [out]) do
      symbolo(out)
      numbero(out)
    end 
    
    assert(u == [[:_0, {:sym, [:_0]}]])
    assert(v == [:owl])
    assert(w == [:owl])
    assert(x == [])
    assert(y == [])
    assert(z == [])
  end
  
  test "Absento constraints seem to work" do
    w = run_all(CLP_Tree, [out, x, y, z]) do
      eq(out, [x, [y, z]])
      absento(:closure, out)
    end
    
    x = run_all(CLP_Tree, [out, x, y, z]) do
      absento(:closure, out)
      eq(out, [x, [y, z]])
    end
    
    y = run_all(CLP_Tree, [out, x, y, z]) do
      eq(out, [x, [y, z]])
      absento(:closure, out)
      eq(z, :closure)
    end
    
    z = run_all(CLP_Tree, [out, x, y, z]) do
      eq(z, :closure)
      eq(out, [x, [y, z]])
      absento(:closure, out)
    end
    
    assert(w == [[[:_0, [:_1, :_2]], {:absent, :closure, :_0},
                                     {:absent, :closure, :_1},
                                     {:absent, :closure, :_2}]])
    assert(x == [[[:_0, [:_1, :_2]], {:absent, :closure, :_0},
                                     {:absent, :closure, :_1},
                                     {:absent, :closure, :_2}]])
    assert(y == [])
    assert(z == [])
  end
  
  test "Absento constraints are properly subsumed by type constraints" do
    y = run_all(CLP_Tree, [out, x, y, z]) do
      eq(out, [x, [y, z]])
      absento(:closure, out)
      symbolo(x)
      numbero(z)
    end
    
    z = run_all(CLP_Tree, [out, x, y, z]) do
      symbolo(x)
      numbero(z)
      absento(:closure, out)
      eq(out, [x, [y, z]])
    end
    
    assert(y == [[[:_0, [:_1, :_2]], {:neq, [[{:_0, :closure}]]},
                                     {:absent, :closure, :_1},
                                     {:num, [:_2]},
                                     {:sym, [:_0]}]])
    assert(z == [[[:_0, [:_1, :_2]], {:neq, [[{:_0, :closure}]]},
                                     {:absent, :closure, :_1},
                                     {:num, [:_2]},
                                     {:sym, [:_0]}]])
  end
  
  test "Absento constraints are subsumed by unification" do
    z = run_all(CLP_Tree, [out, x, y]) do
      eq(out, [x, y])
      absento(:closure, out)
      eq(x, 2)
    end
    
    assert(z == [[[2, :_0], {:absent, :closure, :_0}]])
  end
  
  test "Absento constraints are created properly" do
    y = run_all(CLP_Tree, [out, x, y]) do
      eq(x, :owl)
      eq(out, [x, y])
      absento(:closure, out)
    end
    
    z = run_all(CLP_Tree, [out, x, y]) do
      eq(x, 2)
      eq(out, [x, y])
      absento(:closure, out)
    end
    
    assert(y == [[[:owl, :_0], {:absent, :closure, :_0}]])
    assert(z == [[[2, :_0],    {:absent, :closure, :_0}]])
  end
  
  test "Disequality constraints are subsumed by type constraints" do
    x = run_all(CLP_Tree, [out]) do
     neq(out, 5)
     symbolo(out)
    end
    
    y = run_all(CLP_Tree, [out]) do
      neq(out, :owl)
      numbero(out)
    end
    
    z = run_all(CLP_Tree, [out, x, y]) do
      eq(out, [x, y])
      neq([x, y], [1, 2])
      symbolo(x)
    end
    
    assert(x == [[:_0, {:sym, [:_0]}]])
    assert(y == [[:_0, {:num, [:_0]}]])
    assert(z == [[[:_0, :_1], {:sym, [:_0]}]])
  end
  
  test "Disequality constraints are subsumed by absento constraints" do
    x = run_all(CLP_Tree, [out]) do
      neq(out, :closure)
      absento(:closure, out)
    end
    
    y = run_all(CLP_Tree, [out]) do
      neq(out, 5)
      absento(:closure, out)
    end
    
    z = run_all(CLP_Tree, [out]) do
      absento(:closure, out)
      neq(out, :closure)
    end
    
    assert(x == [[:_0, {:absent, :closure, :_0}]])
    assert(y == [[:_0, {:neq, [[{:_0, 5}]]}, {:absent, :closure, :_0}]])
    assert(z == [[:_0, {:absent, :closure, :_0}]])
  end
end