defmodule MiniKanren.Core do
  @moduledoc """
  Core miniKanren. Provides the operators `eq`, `conde`, `fresh`, and interface
  macros `run` and `run_all`.
  """
  
  alias MiniKanren.Core, as: MK
  
  defmacro __using__(_) do
    quote do
      require MiniKanren.Core
      import  MiniKanren.Core, only: [eq: 2, conde: 1, run_all: 2, run: 3, fresh: 2]
    end
  end
  
  # miniKanren operators
  @doc """
  `eq` is the basic goal constructor: it succeeds if its arguments unify, fails
  otherwise.
  
  ## Examples:
  
      iex> use(MiniKanren, :core)
      iex> run_all([q]) do
      ...>   eq(q, 1)
      ...> end
      [1]
      
      iex> use(MiniKanren, :core)
      iex> run_all([x, y]) do
      ...>   eq(x, [1, y])
      ...>   eq(y, 2)
      ...> end
      [[1, 2]]
      
      iex> use(MiniKanren, :core)
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
  `conde` something something something.
  
  ## Examples
  
      iex> use(MiniKanren, :core)
      iex> run_all([x]) do
      ...>   conde do
      ...>     [eq(x, 1)]
      ...>     [eq(x, 2)]
      ...>     [eq(x, 3)]
      ...>   end
      ...> end
      [1, 2, 3]
      
      iex> use(MiniKanren, :core)
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
    seqs = Enum.map(cases, fn seq -> quote do: MK.conj_many(unquote(seq)) end)
    quote do: MK.disj_many(unquote(seqs))
  end
  
  @doc """
  `fresh` accepts a list of one or more logic variables, and a block containing
  one or more goals. The logic variables are bound into the lexical scope of the
  block, and the logical conjuction of the goals is performed. 
  
  ## Examples
  
      iex> use(MiniKanren, :core)
      iex> run_all([out]) do
      ...>   fresh([x, y]) do
      ...>     eq(x, "One")
      ...>     eq(y, :two)
      ...>     eq(out, {x, y})
      ...>   end
      ...> end
      [{"One", :two}]
      
      iex> use(MiniKanren, :core)
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
  defmacro fresh([], [do: do_block]) do
    seq = case do_block do
      {:__block__, _, goals} -> goals
      goal -> [goal]
    end
    quote do: MK.conj_many(unquote(seq))
  end
  defmacro fresh([var | t], [do: do_block]) do
    quote do
      MK.call_fresh(fn (unquote var) ->
        fresh(unquote(t), [do: unquote(do_block)])
      end)
    end
  end
  
  # miniKanren interface
  @doc """
  `run` is similar to `run_all`, but returns at most `n` results.
  
    ## Examples
  
      iex> use(MiniKanren, :core)
      iex> run(3, [out, x, y]) do
      ...>   appendo(x, y, [1, 2, 3, 4, 5])
      ...>   eq(out, {x, y})
      ...> end
      [{[], [1, 2, 3, 4, 5]}, {[1], [2, 3, 4, 5]}, {[1, 2], [3, 4, 5]}]
  """
  defmacro run(n, vars, [do: do_block]) do
    quote do
      s = fresh(unquote(vars), [do: unquote(do_block)])
      |> MK.call_empty_state
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
  
      iex> use(MiniKanren, :core)
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
      |> MK.call_empty_state
      |> MK.take_all
      |> MK.reify
    end
  end
    
  # Internal wiring
  @doc """
  Creates a new logic variable. Logic variables are represented as 1-tuples.
  """
  def var(c),  do: {c}
  
  @doc """
  Checks if the given argument is a logic variable.
  """
  def var?({_}), do: true
  def var?(_),   do: false
  
  @doc """
  """
  def unit(s_c), do: [s_c]
  
  @doc """
  """
  def mzero, do: []
  
  @doc """
  """
  def mplus([], s), do: s
  def mplus(s1, s2) when is_function(s1) do
    fn -> mplus(s2, s1.()) end
  end
  def mplus([h | t], s2) do
    [h | mplus(s2, t)]
  end
  
  @doc """
  """
  def bind([], _), do: mzero
  def bind(s, g) when is_function(s) do
    fn -> bind(s.(), g) end
  end
  def bind([h | t], g) do
    mplus(g.(h), bind(t, g))
  end
  
  @doc """
  """
  def walk(u, s) do
    case var?(u) and HashDict.get(s, u, false) do
      false -> u
      val   -> walk(val, s)
    end
  end
  
  @doc """
  """
  def walk_all(v, s) do
    case walk(v, s) do
      [h | t]   -> [walk_all(h, s) | walk_all(t, s)]
      {a, b}    -> {walk_all(a, s), walk_all(b, s)}
      {a, b, c} -> {walk_all(a, s), walk_all(b, s), walk_all(c, s)}
      val       -> val
    end
  end
  
  @doc """
  Extends the substitution `s` by relating the logic variable `x` with `v`,
  unless doing so creates a circular relation.
  """
  def ext_s(x, v, s) do
    if occurs_check(x, v, s) do
      nil
    else
      HashDict.put(s, x, v)
    end
  end
  
  @doc """
  Ensures relating `x` and `v` will not introduce a circular relation to the
  substitution `s`.
  """
  def occurs_check(x, v, s) do
    v = walk(v, s)
    var_v = var?(v)
    occurs_check(x, v, var_v, s)
  end
  
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
  
  @doc """
  """
  def unify(t1, t2, s) do
    t1 = walk(t1, s)
    t2 = walk(t2, s)
    var_t1 = var?(t1)
    var_t2 = var?(t2)
    unify(t1, var_t1, t2, var_t2, s)
  end
  
  defp unify(t, _, t, _, s), do: s
  defp unify(t1, true, t2, _, s), do: ext_s(t1, t2, s)
  defp unify(t1, _, t2, true, s), do: ext_s(t2, t1, s)
  defp unify([h1 | t1], _, [h2 | t2], _, s) do
    case unify(h1, h2, s) do
      nil -> nil
      x   -> unify(t1, t2, x)
    end
  end
  defp unify({a1, b1}, _, {a2, b2}, _, s) do
    case unify(a1, a2, s) do
      nil -> nil
      x   -> unify(b1, b2, x)
    end
  end
  defp unify({a1, b1, c1}, _, {a2, b2, c2}, _, s) do
    case unify(a1, a2, s) do
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
  def call_fresh(f) do
    fn {s, counter} ->
      f.(var(counter)).({s, (counter + 1)})
    end
  end
  
  @doc """
  """
  def disj(g1, g2) do
    fn s_c -> mplus(g1.(s_c), g2.(s_c)) end
  end
  
  @doc """
  """
  def conj(g1, g2) do
    fn s_c -> bind(g1.(s_c), g2) end
  end
  
  @doc """
  Applies an inverse-η-delay to the given function call.
  """
  defmacro snooze(func) do
    quote do
      fn s_c ->
        fn -> unquote(func).(s_c) end
      end
    end
  end
  
  defmacro conj_many([fun | []]) do
    quote do: MK.snooze(unquote(fun))
  end
  defmacro conj_many([fun | t]) do
    quote do: MK.conj(MK.snooze(unquote(fun)), MK.conj_many(unquote(t)))
  end
  
  defmacro disj_many([fun | []]) do
    quote do: MK.snooze(unquote(fun))
  end
  defmacro disj_many([fun | t]) do
    quote do: MK.disj(MK.snooze(unquote(fun)), MK.disj_many(unquote(t)))
  end

  # Interface helpers
  def empty_state, do: {HashDict.new, 0}
  def call_empty_state(g), do: g.(empty_state)
  
  def pull(s) when is_function(s), do: pull(s.())
  def pull(s), do: s
  
  def take_all(s) do
    case pull(s) do
      [] -> []
      [h | t] -> [h | take_all(t)]
    end
  end
  
  def take(0, _), do: []
  def take(n, s) do
    case pull(s) do
      [] -> []
      [h | t] -> [h | take(n - 1, t)]
    end
  end
  
  def reify(l_states) do
    Enum.map(l_states, &reify_state/1)
  end
  
  def reify_state({s, _}) do
    v = walk_all(var(0), s)
    walk_all(v, reify_s(v, HashDict.new))
  end
  
  def reify_s(v, s) do
    v = walk(v, s)
    var_v = var?(v)
    reify_s(v, var_v, s)
  end
  
  defp reify_s(v, true, s) do
    n = reify_name(HashDict.size(s))
    HashDict.put(s, v, n)
  end
  defp reify_s([h | t], _, s), do: reify_s(t, reify_s(h, s))
  defp reify_s({a, b}, _, s),  do: reify_s(b, reify_s(a, s))
  defp reify_s({a, b, c}, _, s) do
    reify_s(c, reify_s(b, reify_s(a, s)))
  end
  defp reify_s(_, _, s), do: s
  
  def reify_name(n), do: :"_#{n}"
end


defmodule MiniKanren.Core.Functions do
  @moduledoc """
  Some common relations used in miniKanren.
  """
  
  use   MiniKanren.Core
  alias MiniKanren.Core, as: MK
  
  @doc """
  `succeed` is a goal that always succeeds.
  
  ## Examples
  
      iex> use(MiniKanren, :core)
      iex> run_all([x]) do
      ...>   eq(x, 1)
      ...>   succeed
      ...> end
      [1]
  """
  def succeed, do: fn s_c -> MK.unit(s_c) end
  
  @doc """
  `succeed` is a goal that ignores its argument and always succeeds.
  
  ## Examples
  
      iex> use(MiniKanren, :core)
      iex> run_all([x]) do
      ...>   eq(x, 1)
      ...>   succeed(fail)
      ...> end
      [1]
  """
  def succeed(_), do: fn s_c -> MK.unit(s_c) end
  
  @doc """
  `fail` is a goal that always fails.
  
  ## Examples
  
      iex> use(MiniKanren, :core)
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
  
      iex> use(MiniKanren, :core)
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
  
      iex> use(MiniKanren, :core)
      iex> run_all([x]) do
      ...>   heado([1, 2, 3], x)
      ...> end
      [1]
      
      iex> use(MiniKanren, :core)
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
  
      iex> use(MiniKanren, :core)
      iex> run_all([x]) do
      ...>   tailo([1, 2, 3], x)
      ...> end
      [[2, 3]]
      
      iex> use(MiniKanren, :core)
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
  
      iex> use(MiniKanren, :core)
      iex> run_all([out, x, y]) do
      ...>   eq(x, 1)
      ...>   eq(y, [2, 3])
      ...>   conso(x, y, out)
      ...> end
      [[1, 2, 3]]
      
      iex> use(MiniKanren, :core)
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
  
      iex> use(MiniKanren, :core)
      iex> run_all([out, x, y]) do
      ...>   membero(x, [1, 2, 3])
      ...>   membero(y, [4, 5, 6])
      ...>   eq(out, {x, y})
      ...> end
      [{1, 4}, {1, 5}, {2, 4}, {1, 6}, {3, 4}, {2, 5}, {3, 5}, {2, 6}, {3, 6}]
      
      iex> use(MiniKanren, :core)
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
  
      iex> use(MiniKanren, :core)
      iex> run_all([out]) do
      ...>   rembero(5, [1, 2, 3, 4, 5], out)
      ...> end
      [[1, 2, 3, 4], [1, 2, 3, 4, 5]]
      
      iex> use(MiniKanren, :core)
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
  
      iex> use(MiniKanren, :core)
      iex> run_all([out, x, y]) do
      ...>   appendo(x, y, [1, 2, 3])
      ...>   eq(out, {x, y})
      ...> end
      [{[], [1, 2, 3]}, {[1], [2, 3]}, {[1, 2], [3]}, {[1, 2, 3], []}]
      
      iex> use(MiniKanren, :core)
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
  
      iex> use(MiniKanren, :core)
      iex> run_all([x]) do
      ...>   emptyo(x)
      ...> end
      [[]]
  """
  def emptyo(a), do: eq(a, [])
end