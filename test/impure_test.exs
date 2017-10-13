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
  
  test "conda doesn't blow up when no clauses succeed" do
    run_all([_x]) do
      conda do
        [fail()]
      end
    end
  end

	test "conda checks all assertions of function clause" do
		bad_func = fn (_) ->
			succeed()
			conda do
				[fail()]
			end
		end

		result = run_all([x]) do
			conda do
				[bad_func.(x)]
				[eq(x, :success)]
			end
		end

		assert(result == [:success])
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
  
  test "condu doesn't blow up when no clauses succeed" do
    run_all([_x]) do
      condu do
        [fail()]
      end
    end
  end

	test "condu checks all assertions of function clause" do
		bad_func = fn (_) ->
			succeed()
			condu do
				[fail()]
			end
		end

		result = run_all([x]) do
			condu do
				[bad_func.(x)]
				[membero(x, [1,2,3])]
			end
		end

		assert(result == [1])
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
