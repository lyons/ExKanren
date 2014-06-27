defmodule PrimerTest do
  # exercising/translating examples from
  # http://github.com/clojure/core.logic/wiki/A-Core.logic-Primer

  use ExUnit.Case
  
  use MiniKanren, :core

  test "section: Constraints" do
    assert ( run_all [q] do
      membero q, [1,2,3]
      membero q, [2,3,4]
    end ) == [2,3]
  end

  test "section: unification of a single lvar with a literal" do
    assert ( run_all [q], do: ( eq q,1 ) ) == [1]
    assert ( run_all [q], do: ( eq q, [a: 1, b: 2] ) ) == [[a: 1, b: 2]]
    assert ( run_all [q], do: ( eq [a: q, b: 2], [a: 1, b: 2] ) ) == [1]
    assert ( run_all [q], do: ( eq [a: q, b: 2], [a: 1, b: 3] ) ) == []
    assert ( run_all [q], do: ( eq [a: q, b: 2], [a: 1, b: q] ) ) == []
    assert ( run_all [q], do: ( eq 1,q ) ) == [1]
    assert ( run_all [q], do: ( eq q,[1,2,3] ) ) == [[1,2,3]]
    assert ( run_all [q], do: ( eq q,1; eq q,2 ) ) == []
  end

  test "section: unification of two lvars" do
    assert ( run_all [q], do: ( membero q, [1] ) ) == [1]
    assert ( run_all [q], do: ( membero q, [1,2,3] ) ) == [1,2,3]
    assert ( run_all [q], do: ( membero q, [1,2]; membero q, [1] ) ) == [1]

    assert ( run_all [q] do
      membero q, [1,2,3]
      membero q, [3,4,5]
    end ) == [3]
    
    assert ( run_all [q] do
      fresh [a] do
        membero q, [1,2,3]
        membero a, [3,4,5]
        eq a,q
      end
    end ) == [3]
  end

  test "section: Core.logic is declarative" do
    assert ( run_all [q] do
      fresh [a] do
        membero q, [1,2,3]
        membero a, [3,4,5]
        eq q,a
      end
    end ) == [3]
    
    assert ( run_all [q] do
      fresh [a] do
        membero a, [3,4,5]
        eq q,a
        membero q, [1,2,3]
      end
    end ) == [3]

    assert ( run_all [q] do
      fresh [a] do
        eq q,a
        membero a, [3,4,5]
        membero q, [1,2,3]
      end
    end ) == [3]
  end

  test "*off article* succeed & fail" do
    assert [_] = ( run_all [_q], do: succeed )
    assert ( run_all [_q], do: fail ) == []
    assert ( run_all [_q], do: ( fail; succeed ) ) == []
    assert ( run_all [_q], do: ( succeed; fail ) ) == []
  end

  test "section: The final operator, conde" do
    assert [_] = ( run_all [_q] do
      conde do
        [succeed]
      end
    end )

    assert [_] = ( run_all [_q] do
      conde do
        [succeed, succeed, succeed, succeed]
      end
    end )

    assert [] == ( run_all [_q] do
      conde do
        [succeed, succeed, fail, succeed]
      end
    end )

    assert [_,_] = ( run_all [_q] do
      conde do
        [succeed]
        [succeed]
      end
    end )

    assert [_] = ( run_all [_q] do
      conde do
        [succeed]
        [fail]
      end
    end )

    assert ( run_all [q] do
      conde do
        [succeed, eq(q,1)]
      end
    end ) == [1]

    assert ( run_all [q] do
      conde do
        [eq(q,2), eq(q,1)]
      end
    end ) == []

    assert ( run_all [q] do
      conde do
        [eq(q,1)]
        [eq(q,2)]
      end
    end ) == [1,2]
  end

  test "section: Conso (the Magnificent)" do
    assert ( run_all [q], do: ( conso 1, [2,3], q ) ) == [[1,2,3]]
    assert ( run_all [q], do: ( conso 1, q, [1,2,3] ) ) == [[2,3]]
    assert ( run_all [q], do: ( conso q, [2,3], [1,2,3] ) ) == [1]
    assert ( run_all [q], do: ( conso 1, [2,q], [1,2,3] ) ) == [3]
  end

  test "section: Resto" do
    # in ExKanren Clojure's resto operator is called tailo
    assert ( run_all [q], do: ( tailo [1,2,3,4],q ) ) == [[2,3,4]]
  end

  test "section: Membero" do
    assert ( run_all [q], do: ( membero 7, [1,3,8,q] ) ) == [7]
  end

  # Here's the summary of miniKanren and what's been covered (*asterisk)
  # in this primer:
  #
  # - core operators:   *run_all,  run,  *eq, *conde, *fresh
  # - core functions:   *succeed, *fail,  heado, *tailo, *conso, 
  #                     *membero,  rembero,  appendo,  emptyo
  # - impure operators:  conda,  condu,  project
  # - impure functions:  onceo,  copy_term,  is,  fresho,  staleo
end
