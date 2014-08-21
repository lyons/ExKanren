defmodule MiniKanren do
  @moduledoc """
  Core miniKanren. Provides the operators `eq`, `conde`, `fresh`, and interface
  macros `run` and `run_all`.
  """
  
  alias MiniKanren, as: MK
  
  defmacro __using__(:no_functions) do
    # It is bad when MiniKanren.Functions tries to import itself
    quote do
      require MiniKanren
      import  MiniKanren, only: [eq: 2, conde: 1, run_all: 2, run: 3, fresh: 2,
                                 conda: 1, condu: 1, project: 2]
    end
  end
  defmacro __using__(_) do
    quote do
      require MiniKanren
      import  MiniKanren, only: [eq: 2, conde: 1, run_all: 2, run: 3, fresh: 2,
                                 conda: 1, condu: 1, project: 2]
      import  MiniKanren.Functions
    end
  end
  
  # Typespecs
  @type package :: {map(), non_neg_integer}
  @type goal_stream :: :mzero | package | (() -> goal_stream) | nonempty_improper_list(package, (() -> goal_stream))
  @type goal :: (package -> goal_stream)
  @type logic_variable :: {non_neg_integer}
  @type substitution :: Map.t
  @type logic_value :: any # Should be all types allowed in substitution
  
  # miniKanren operators
  @doc """
  `eq` is the basic goal constructor: it succeeds if its arguments unify, fails
  otherwise.
  
  ## Examples:
  
      iex> use MiniKanren
      iex> run_all([q]) do
      ...>   eq(q, 1)
      ...> end
      [1]
      
      iex> use MiniKanren
      iex> run_all([x, y]) do
      ...>   eq(x, [1, y])
      ...>   eq(y, 2)
      ...> end
      [[1, 2]]
      
      iex> use MiniKanren
      iex> run_all([x, y]) do
      ...>   eq(x, 1)
      ...>   eq(y, 2)
      ...>   eq(x, y)
      ...> end
      []
  """
  def eq(u, v) do
    fn {subs, counter} ->
      case unify(u, v, subs) do
        nil -> mzero
        s   -> unit({s, counter})
      end
    end
  end
  
  @doc """
  `conde` accepts two or more clauses made of lists of goals, and returns the
  logical disjunction of these clauses.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   conde do
      ...>     [eq(x, 1)]
      ...>     [eq(x, 2)]
      ...>     [eq(x, 3)]
      ...>   end
      ...> end
      [1, 2, 3]
      
      iex> use MiniKanren
      iex> run_all([out, x, y]) do
      ...>   conde do
      ...>     [eq(x, 1), eq(y, 2), eq(out, {"First clause", x, y})]
      ...>     [eq(x, 1), eq(1, 2), eq(out, {"Second clause", x, y})]
      ...>     [eq(x, y), eq(x, 3), eq(out, {"Third clause", x, y})]
      ...>   end
      ...> end
      [{"First clause", 1, 2}, {"Third clause", 3, 3}]
  """
  defmacro conde([do: {:__block__, _, cases}]) do
    seqs = Enum.map(cases, fn seq -> quote do: MK.bind_many([pkg, unquote_splicing(seq)]) end)
    quote do: fn pkg -> MK.mplus_many(unquote(seqs)) end
  end
  defmacro conde([do: single_case]) do
    call = {:__block__, [], [single_case]}
    quote do: MK.conde(do: unquote(call))
  end

  @doc """
  `fresh` accepts a list of one or more logic variables, and a block containing
  one or more goals. The logic variables are bound into the lexical scope of the
  block, and the logical conjuction of the goals is performed. 
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([out]) do
      ...>   fresh([x, y]) do
      ...>     eq(x, "One")
      ...>     eq(y, :two)
      ...>     eq(out, {x, y})
      ...>   end
      ...> end
      [{"One", :two}]
      
      iex> use MiniKanren
      iex> run_all([out, a, b]) do
      ...>   fresh([x, y]) do
      ...>     eq(x, "One")
      ...>     eq(y, :two)
      ...>     fresh([x, y]) do
      ...>       eq(x, "Three")
      ...>       eq(y, :four)
      ...>       eq(b, [x, y])
      ...>     end
      ...>     eq(a, [x, y])
      ...>   end
      ...>   eq(out, {a, b})
      ...> end
      [{["One", :two], ["Three", :four]}]
  """
  defmacro fresh(vars, [do: do_block]) when is_list(vars) do
    func = MK.expand_fresh(vars, do_block)
    quote do: unquote(func)
  end
  
  # miniKanren interface
  @doc """
  `run` is similar to `run_all`, but returns at most `n` results.
  
    ## Examples
  
      iex> use MiniKanren
      iex> run(3, [out, x, y]) do
      ...>   appendo(x, y, [1, 2, 3, 4, 5])
      ...>   eq(out, {x, y})
      ...> end
      [{[], [1, 2, 3, 4, 5]}, {[1], [2, 3, 4, 5]}, {[1, 2], [3, 4, 5]}]
  """
  defmacro run(n, vars, [do: do_block]) do
    quote do
      s = fresh(unquote(vars), [do: unquote(do_block)])
      |> MK.call_empty_package
      MK.take(unquote(n), s)
      |> MK.reify
    end
  end
    
  @doc """
  `run_all` accepts a list of one or more logic variables and a block containing
  one or more goals. The logic variables are bound into the lexical scope of the
  block, and the logical conjunction of the goals is performed. All results of the
  conjunction are evaluated, and are returned in terms of the first logic variable
  given.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([out, x, y]) do
      ...>   appendo(x, y, [1, 2, 3, 4, 5])
      ...>   eq(out, {x, y})
      ...> end
      [{[], [1, 2, 3, 4, 5]}, {[1], [2, 3, 4, 5]}, {[1, 2], [3, 4, 5]},
      {[1, 2, 3], [4, 5]}, {[1, 2, 3, 4], [5]}, {[1, 2, 3, 4, 5], []}]
  """
  defmacro run_all(vars, [do: do_block]) do
    quote do
      fresh(unquote(vars), [do: unquote(do_block)])
      |> MK.call_empty_package
      |> MK.take_all
      |> MK.reify
    end
  end
  
  # Impure operators
  @doc """     
  `conda` accepts lists of goal clauses similar to `conde`, but returns the result
  of at most one clause: the first clause to have its first goal succeed.
  
  ## Examples:
  
      iex> use MiniKanren
      iex> run_all([out, x, y]) do
      ...>   conda do
      ...>     [eq(1, 2), eq(out, "First clause")]
      ...>     [appendo(x, y, [1, 2, 3]), eq(out, {x, "Second clause"})]
      ...>     [eq(x, y), eq(x, 1), eq(out, {{x, y}, "Third clause"})]
      ...>   end
      ...> end  
      [{[], "Second clause"}, {[1], "Second clause"}, {[1, 2], "Second clause"},
       {[1, 2, 3], "Second clause"}]
  """
  defmacro conda([do: {:__block__, _, clauses}]) do
    seqs = Enum.map(clauses, fn
      [h | []] -> quote do: {unquote(h), &MK.unit/1}
      [h | t]  -> quote do: {unquote(h), MK.bind_many(unquote(t))}
    end)

    quote do: fn pkg -> MK._conda(unquote(seqs), pkg) end
  end
  defmacro conda([do: single_clause]) do
    call = {:__block__, [], [single_clause]}
    quote do: MK.conda(do: unquote(call))
  end
  
  @doc """     
  `condu` is similar to `conda`, but takes only a single result from the first
  goal of the first successful clause.
  
  ## Examples:
  
      iex> use MiniKanren
      iex> run_all([out, x, y]) do
      ...>   condu do
      ...>     [eq(1, 2), eq(out, "First clause")]
      ...>     [appendo(x, y, [1, 2, 3]), eq(out, {x, "Second clause"})]
      ...>     [eq(x, y), eq(x, 1), eq(out, {{x, y}, "Third clause"})]
      ...>   end
      ...> end  
      [{[], "Second clause"}]
  """
  defmacro condu([do: {:__block__, _, clauses}]) do
    seqs = Enum.map(clauses, fn
      [h | []] -> quote do: {unquote(h), &MK.unit/1}
      [h | t]  -> quote do: {unquote(h), MK.bind_many(unquote(t))}
    end)

    quote do: fn pkg -> MK._condu(unquote(seqs), pkg) end
  end
  defmacro condu([do: single_clause]) do
    call = {:__block__, [], [single_clause]}
    quote do: MK.condu(do: unquote(call))
  end

  @doc """
  `project` binds the associated value (if any) of one or more logic variables
  into lexical scope and allows them to be operated on.
  
  ## Examples:
  
      iex> use MiniKanren
      iex> run_all([out, x, y]) do
      ...>   eq(x, 3)
      ...>   eq(y, 7)
      ...>   project([x, y]) do
      ...>     eq(x + y, out)
      ...>   end
      ...> end
      [10]
      
      iex> use MiniKanren
      iex> run_all([out, x]) do
      ...>   project([x]) do
      ...>     eq(x + x, out)
      ...>   end
      ...>   eq(x, 3)
      ...> end
      ** (ArithmeticError) bad argument in arithmetic expression
      :erlang.+({1}, {1})
  """
  defmacro project([], [do: _]), do: raise("No variables given to project")
  defmacro project(vars, [do: do_block]) do
    bindings = Enum.map(vars, fn var ->
      quote do: unquote(var) = MK.walk_all(unquote(var), subs)
    end)
    
    quote do
      fn pkg = {subs, _} ->
        unquote_splicing(bindings)
        MK.fresh([], [do: unquote(do_block)]).(pkg)
      end
    end
  end
  
  # Wiring
  @spec _conda(list({goal, goal}), package) :: goal_stream
  def _conda([], _), do: []
  def _conda([{h, seq} | t], pkg) do
    case h.(pkg) do
      :mzero -> _conda(t, pkg)
      a      -> bind(a, seq)
    end
  end
  
  @spec _condu(list({goal, goal}), package) :: goal_stream
  def _condu([], _), do: []
  def _condu([{h, seq} | t], pkg) do
    case h.(pkg) do
      :mzero   -> _condu(t, pkg)
      [a | _f] -> bind(unit(a), seq)
      a        -> bind(a, seq)
    end
  end
  
  # Internal wiring
  @spec var(non_neg_integer | reference) :: logic_variable
  @doc """
  Creates a new logic variable. Logic variables are represented as 1-tuples.
  """
  def var(c),  do: {c}
  
  @spec vars(non_neg_integer, pos_integer) :: nonempty_list(logic_variable)
  def vars(c, n), do: Enum.map(c..(c + n - 1), &var/1)
  
  @spec var?(any) :: boolean
  @doc """
  Checks if the given argument is a logic variable.
  """
  def var?({_}), do: true
  def var?(_),   do: false
  
  @spec unit(package) :: package
  @doc """
  """
  def unit(pkg), do: pkg
  
  @spec mzero() :: :mzero
  @doc """
  """
  def mzero, do: :mzero
  
  @spec mplus(goal_stream, (() -> goal_stream)) :: goal_stream
  @doc """
  """
  def mplus(:mzero, s), do: s
  def mplus(s1, s2) when is_function(s1) do
    fn -> mplus(s1.(), s2) end
  end
  def mplus(s1, s2) when is_tuple(s1), do: [s1 | s2]
  def mplus([h | t], s) do
    [h | fn -> mplus(s.(), t) end]
  end
  
  @spec bind(goal_stream, goal) :: goal_stream
  @doc """
  """
  def bind(:mzero, _), do: mzero
  def bind(thunk, goal) when is_function(thunk) do
    fn -> bind(thunk.(), goal) end
  end
  def bind(pkg, goal) when is_tuple(pkg), do: goal.(pkg)
  def bind([pkg | thunk], goal) do
    mplus(goal.(pkg), fn -> bind(thunk.(), goal) end)
  end
  
  @spec walk(logic_value, substitution) :: logic_value
  @doc """
  """
  def walk(x, subs) do
    case var?(x) and Dict.get(subs, x, false) do
      false -> x
      val   -> walk(val, subs)
    end
  end
  
  @spec walk_all(logic_value, substitution) :: logic_value
  @doc """
  """
  def walk_all(v, subs) do
    case walk(v, subs) do
      [h | t]   -> [walk_all(h, subs) | walk_all(t, subs)]
      {a, b}    -> {walk_all(a, subs), walk_all(b, subs)}
      {a, b, c} -> {walk_all(a, subs), walk_all(b, subs), walk_all(c, subs)}
      val       -> val
    end
  end
  
  @spec extend_substitution(logic_value, logic_value, substitution) :: substitution | nil
  @doc """
  Extends the substitution `s` by relating the logic variable `x` with `v`,
  unless doing so creates a circular relation.
  """
  def extend_substitution(x, v, s) do
    if occurs_check(x, v, s) do
      nil
    else
      Dict.put(s, x, v)
    end
  end
  
  @spec occurs_check(logic_value, logic_value, substitution) :: boolean
  @doc """
  Ensures relating `x` and `v` will not introduce a circular relation to the
  substitution `s`.
  """
  def occurs_check(x, v, subs) do
    v = walk(v, subs)
    var_v? = var?(v)
    occurs_check(x, v, var_v?, subs)
  end
  
  @spec occurs_check(logic_value, logic_value, boolean, substitution) :: boolean
  defp occurs_check(v, v, true, _), do: true
  defp occurs_check(_, _, true, _), do: false
  defp occurs_check(x, [h | t], _, s) do
    occurs_check(x, h, s) or occurs_check(x, t, s)
  end
  defp occurs_check(x, {a, b}, _, s) do
    occurs_check(x, a, s) or occurs_check(x, b, s)
  end
  defp occurs_check(x, {a, b, c}, _, s) do
    occurs_check(x, a, s) or occurs_check(x, b, s) or occurs_check(x, c, s)
  end
  defp occurs_check(_, _, _, _), do: false
  
  @spec unify(logic_value, logic_value, substitution) :: substitution | nil
  @doc """
  """
  def unify(t1, t2, subs) do
    t1 = walk(t1, subs)
    t2 = walk(t2, subs)
    var_t1? = var?(t1)
    var_t2? = var?(t2)
    unify(t1, var_t1?, t2, var_t2?, subs)
  end
  
  @spec unify(logic_value, boolean, logic_value, boolean, substitution) :: substitution | nil
  defp unify(t, _, t, _, subs), do: subs
  defp unify(t1, true, t2, _, subs), do: extend_substitution(t1, t2, subs)
  defp unify(t1, _, t2, true, subs), do: extend_substitution(t2, t1, subs)
  defp unify([h1 | t1], _, [h2 | t2], _, subs) do
    case unify(h1, h2, subs) do
      nil -> nil
      x   -> unify(t1, t2, x)
    end
  end
  defp unify({a1, b1}, _, {a2, b2}, _, subs) do
    case unify(a1, a2, subs) do
      nil -> nil
      x   -> unify(b1, b2, x)
    end
  end
  defp unify({a1, b1, c1}, _, {a2, b2, c2}, _, subs) do
    case unify(a1, a2, subs) do
      nil -> nil
      x   -> case unify(b1, b2, x) do
               nil -> nil
               y   -> unify(c1, c2, y)
             end
    end
  end
  defp unify(_, _, _, _, _), do: nil
  
  # Goal constructor helpers
  @doc """
  """
  def expand_fresh(ls = [_ | _], do_block) do
    length = Enum.count(ls)
    seq = case do_block do
      {:__block__, _, goals} -> goals
      goal -> [goal]
    end
    
    quote do
      fn {subs, counter} ->
        fn unquote(ls) ->
          MK.bind_many([{subs, counter + unquote(length)}, unquote_splicing(seq)])
        end.(MK.vars(counter, unquote(length)))
      end
    end
  end
  def expand_fresh([], do_block) do
    seq = case do_block do
      {:__block__, _, goals} -> goals
      goal -> [goal]
    end
    
    quote do
      fn pkg ->
        MK.bind_many([pkg, unquote_splicing(seq)])
      end
    end
  end
    
  defmacro mplus_many([fun | []]) do
    quote do: unquote(fun)
  end
  defmacro mplus_many([fun | t]) do
    quote do: MK.mplus(unquote(fun), fn -> MK.mplus_many(unquote(t)) end)
  end
  
  defmacro bind_many([fun | []]) do
    quote do: unquote(fun)
  end
  defmacro bind_many([fun1, fun2]) do
    quote do: MK.bind(unquote(fun1), unquote(fun2))
  end
  defmacro bind_many([fun1, fun2 | t]) do
    quote do: MK.bind_many([MK.bind(unquote(fun1), unquote(fun2)), unquote_splicing(t)])
  end
  
  # Interface helpers
  @spec empty_package() :: package
  def empty_package, do: {Map.new, 0}
  
  @spec call_empty_package(goal) :: goal_stream
  def call_empty_package(g), do: g.(empty_package)
  
  @spec take_all(goal_stream) :: list(package)
  def take_all(s) do
    case s do
      :mzero  -> []
      pkg when is_tuple(pkg)  -> [pkg]
      f   when is_function(f) -> f.() |> take_all
      [h | t] -> [h | take_all(t)]
    end
  end
  
  @spec take(non_neg_integer, goal_stream) :: list(package)
  def take(0, _), do: []
  def take(n, s) do
    case s do
      :mzero  -> []
      pkg when is_tuple(pkg)  -> [pkg]
      f   when is_function(f) -> take(n, f.())
      [h | t] -> [h | take(n - 1, t)]
    end
  end
  
  def reify(l_states) do
    Enum.map(l_states, &reify_state/1)
  end
  
  def reify_state({s, _}) do
    v = walk_all(var(0), s)
    walk_all(v, reify_s(v, Map.new))
  end
  
  def reify_s(v, s) do
    v = walk(v, s)
    var_v = var?(v)
    reify_s(v, var_v, s)
  end
  
  defp reify_s(v, true, s) do
    n = reify_name(Dict.size(s))
    Dict.put(s, v, n)
  end
  defp reify_s([h | t], _, s), do: reify_s(t, reify_s(h, s))
  defp reify_s({a, b}, _, s),  do: reify_s(b, reify_s(a, s))
  defp reify_s({a, b, c}, _, s) do
    reify_s(c, reify_s(b, reify_s(a, s)))
  end
  defp reify_s(_, _, s), do: s
  
  def reify_name(n), do: :"_#{n}"
end

defmodule MiniKanren.Functions do
  #@moduledoc """
  #Some common relations used in miniKanren.
  #"""
  
  use   MiniKanren, :no_functions
  alias MiniKanren, as: MK
  
  @doc """
  `succeed` is a goal that always succeeds.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   eq(x, 1)
      ...>   succeed
      ...> end
      [1]
  """
  def succeed, do: fn pkg -> MK.unit(pkg) end
  
  @doc """
  `succeed` is a goal that ignores its argument and always succeeds.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   eq(x, 1)
      ...>   succeed(fail)
      ...> end
      [1]
  """
  def succeed(_), do: fn pkg -> MK.unit(pkg) end
  
  @doc """
  `fail` is a goal that always fails.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   eq(x, 1)
      ...>   fail
      ...> end
      []
  """
  def fail, do: fn _ -> MK.mzero end
  
  @doc """
  `fail` is a goal that ignores its argument and always fails.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   eq(x, 1)
      ...>   fail(succeed)
      ...> end
      []
  """
  def fail(_), do: fn _ -> MK.mzero end

  @doc """
  `heado` relates `h` as the head of list `ls`.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   heado([1, 2, 3], x)
      ...> end
      [1]
      
      iex> use MiniKanren
      iex> run_all([out, x]) do
      ...>   heado(out, x)
      ...>   eq(x, "foo")
      ...> end
      [["foo" | :_0]]
  """
  def heado(ls, h) do
    fresh([t]) do
      eq([h | t], ls)
    end
  end
  
  @doc """
  `tailo` relates `t` as the tail of list `ls`.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   tailo([1, 2, 3], x)
      ...> end
      [[2, 3]]
      
      iex> use MiniKanren
      iex> run_all([out, x]) do
      ...>   tailo(out, x)
      ...>   eq(x, ["foo", "bar"])
      ...> end
      [[:_0, "foo", "bar"]]
  """
  def tailo(ls, t) do
    fresh([h]) do
      eq([h | t], ls)
    end
  end

  @doc """
  `conso` relates `h` and `t` as the head and tail of list `ls`.
  
  Equivalent to `eq([h | t], ls)`.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([out, x, y]) do
      ...>   eq(x, 1)
      ...>   eq(y, [2, 3])
      ...>   conso(x, y, out)
      ...> end
      [[1, 2, 3]]
      
      iex> use MiniKanren
      iex> run_all([out, x, y]) do
      ...>   conso(x, y, [1, 2, 3])
      ...>   eq(out, {x, y})
      ...> end
      [{1, [2, 3]}]
  """
  def conso(h, t, ls), do: eq([h | t], ls)
  
  @doc """
  `membero` relates `a` as being a member of the list `ls`.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([out, x, y]) do
      ...>   membero(x, [1, 2, 3])
      ...>   membero(y, [4, 5, 6])
      ...>   eq(out, {x, y})
      ...> end |> Enum.sort
      [{1, 4}, {1, 5}, {1, 6}, {2, 4}, {2, 5}, {2, 6}, {3, 4}, {3, 5}, {3, 6}]
      
      iex> use MiniKanren
      iex> run(3, [x]) do
      ...>   membero("foo", x)
      ...> end
      [["foo" | :_0], [:_0, "foo" | :_1], [:_0, :_1, "foo" | :_2]]
  """
  def membero(a, ls) do
    fresh([h, t]) do
      eq([h | t], ls)
      conde do
        [eq(a, h)]
        [membero(a, t)]
      end
    end
  end
  
  @doc """
  `rembero` associates `out` as the list `ls` with value `x` removed.
  
  The lack of disequality constrains in core miniKanren means `rembero` may
  produce dubious results.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([out]) do
      ...>   rembero(5, [1, 2, 3, 4, 5], out)
      ...> end
      [[1, 2, 3, 4], [1, 2, 3, 4, 5]]
      
      iex> use MiniKanren
      iex> run_all([out, x]) do
      ...>   rembero(x, [1, 2, x, 4, 5], out)
      ...> end
      [[2, 1, 4, 5], [1, 2, 4, 5], [1, 2, 4, 5], [1, 2, 4, 5], [1, 2, 5, 4],
      [1, 2, :_0, 4, 5]]
  """
  def rembero(x, ls, out) do
    conde do
      [eq(ls, []),   eq(out, [])]
      [heado(ls, x), tailo(ls, out)]
      [fresh([h, t, res]) do
         eq([h | t], ls)
         rembero(x, t, res)
         eq([h | res], out)
       end]
    end
  end
  
  @doc """
  `appendo` relates the list `ls` as the result of appending lists `l1` and `l2`.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([out, x, y]) do
      ...>   appendo(x, y, [1, 2, 3])
      ...>   eq(out, {x, y})
      ...> end
      [{[], [1, 2, 3]}, {[1], [2, 3]}, {[1, 2], [3]}, {[1, 2, 3], []}]
      
      iex> use MiniKanren
      iex> run(5, [x]) do
      ...>   appendo(x, [], x)
      ...> end
      [[], [:_0], [:_0, :_1], [:_0, :_1, :_2], [:_0, :_1, :_2, :_3]]
  """
  def appendo(l1, l2, ls) do
    conde do
      [eq(l1, []), eq(l2, ls)]
      [fresh([h, t, res]) do
         eq([h | t], l1)
         eq([h | res], ls)
         appendo(t, l2, res)
       end]
    end
  end
  
  @doc """
  `emptyo` relates `a` to the empty list.
  
  Equivalent to `eq(a, [])`.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   emptyo(x)
      ...> end
      [[]]
  """
  def emptyo(a), do: eq(a, [])
  
  # Non-relational functions
  
  @doc """
  `onceo` accepts a goal function, and allows it to succeed at most once.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([out, x, y]) do
      ...>   onceo(appendo(x, y, [1, 2, 3, 4, 5]))
      ...>   eq(out, {x, y})
      ...> end
      [{[], [1, 2, 3, 4, 5]}]
  """
  def onceo(g) do
    condu do
      [g]
    end
  end
  
  @doc """
  `copy_term` copies the term associated with `x` to `y`, replacing any fresh
  logic variables in `x` with distinct fresh variables in `y`.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([out, x, y, a, b]) do
      ...>   eq(x, [a, b])
      ...>   copy_term(x, y)
      ...>   eq(out, {x, y})
      ...> end
      [{[:_0, :_1], [:_2, :_3]}]
      
      iex> use MiniKanren
      iex> run_all([out, x, y, a, b]) do
      ...>   eq(x, [a, b])
      ...>   eq(b, "Bee")
      ...>   copy_term(x, y)
      ...>   eq(out, {x, y})
      ...> end
      [{[:_0, "Bee"], [:_1, "Bee"]}]
  """
  def copy_term(u, v) do
    project([u]) do
      eq(MK.walk_all(u, build_subs(u, Map.new)), v)
    end
  end
  
  defp build_subs(u, subs) do
    case MK.var?(u) or u do
      true    -> Dict.put_new(subs, u, MK.var(make_ref))
      [h | t] -> build_subs(t, build_subs(h, subs))
      _       -> subs
    end
  end
  
  @doc """
  `is` projects its argument `b`, and associates `a` with the result of the unary
  operation `f.(b)`
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([x, y]) do
      ...>   eq(y, 5)
      ...>   is(x, y, &:math.log/1)
      ...> end
      [1.6094379124341003]
  """
  def is(a, b, f) do
    project([b]) do
      eq(a, f.(b))
    end
  end
  
  @doc """
  `fresho` succeeds if its argument is a fresh logic variable, fails otherwise.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   fresho(x)
      ...>   eq(x, 1)
      ...> end
      [1]
      
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   eq(x, 1)
      ...>   fresho(x)
      ...> end
      []
  """
  def fresho(v) do
    fn pkg = {subs, _} ->
      case MK.var?(MK.walk(v, subs)) do
        false -> MK.mzero
        _     -> MK.unit(pkg)
      end
    end
  end
  
  @doc """
  `staleo` fails if its argument is a fresh logic variable, succeeds otherwise.
  
  ## Examples
  
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   eq(x, 1)
      ...>   staleo(x)
      ...> end
      [1]
      
      iex> use MiniKanren
      iex> run_all([x]) do
      ...>   staleo(x)
      ...>   eq(x, 1)
      ...> end
      []
  """
  def staleo(v) do
    fn pkg = {subs, _} ->
      case MK.var?(MK.walk(v, subs)) do
        false -> MK.unit(pkg)
        _     -> MK.mzero
      end
    end
  end
end
