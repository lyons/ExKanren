defmodule MiniKanren.Impure do
  @moduledoc """
  Impure operators for miniKanren: `conda`, `condu`, and `project`.
  """
  
  require MiniKanren.Core
  import  MiniKanren.Core
  alias   MiniKanren.Core,   as: MK
  alias   MiniKanren.Impure, as: Impure
  
  defmacro __using__(_) do
    quote do
      require MiniKanren.Impure
      import  MiniKanren.Impure, only: [conda: 1, condu: 1, project: 2]
    end
  end

  # Impure operators
  @doc """     
  `conda` accepts lists of goal clauses similar to `conde`, but returns the result
  of at most one clause: the first clause to have its first goal succeed.
  
  ## Examples:
  
      iex> use MiniKanren.Core
      iex> import MiniKanren.Core.Functions
      iex> use MiniKanren.Impure
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
      [h | t]  -> quote do: {unquote(h), MK.conj_many(unquote(t))}
    end)

    quote do: fn s_c -> Impure._conda(unquote(seqs), s_c) end
  end
  defmacro conda([do: single_clause]) do
    call = {:__block__, [], [single_clause]}
    quote do: Impure.conda(do: unquote(call))
  end
  
  @doc """     
  `condu` is similar to `conda`, but takes only a single result from the first
  goal of the first successful clause.
  
  ## Examples:
  
      iex> use MiniKanren.Core
      iex> import MiniKanren.Core.Functions
      iex> use MiniKanren.Impure
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
      [h | t]  -> quote do: {unquote(h), MK.conj_many(unquote(t))}
    end)

    quote do: fn s_c -> Impure._condu(unquote(seqs), s_c) end
  end
  defmacro condu([do: single_clause]) do
    call = {:__block__, [], [single_clause]}
    quote do: Impure.condu(do: unquote(call))
  end

  @doc """
  `project` binds the associated value (if any) of one or more logic variables
  into lexical scope and allows them to be operated on.
  
  ## Examples:
  
      iex> use MiniKanren.Core
      iex> use MiniKanren.Impure
      iex> run_all([out, x, y]) do
      ...>   eq(x, 3)
      ...>   eq(y, 7)
      ...>   project([x, y]) do
      ...>     eq(x + y, out)
      ...>   end
      ...> end
      [10]
      
      iex> use MiniKanren.Core
      iex> use MiniKanren.Impure
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
      fn s_c = {subs, _} ->
        unquote_splicing(bindings)
        MK.fresh([], [do: unquote(do_block)]).(s_c)
      end
    end
  end
  
  # Wiring
  def _conda([], _), do: []
  def _conda([{h, seq} | t], s_c) do
    case pull(h.(s_c)) do
      [] -> _conda(t, s_c)
      a  -> bind(a, seq)
    end
  end
  
  def _condu([], _), do: []
  def _condu([{h, seq} | t], s_c) do
    case pull(h.(s_c)) do
      []       -> _condu(t, s_c)
      [a | _f] -> bind(unit(a), seq)
      a        -> bind(a, seq)
    end
  end
end

defmodule MiniKanren.Impure.Functions do
  @moduledoc """
  Non-relational functions for miniKanren.
  """
  
  use   MiniKanren.Core
  alias MiniKanren.Core, as: MK
  use   MiniKanren.Impure
  
  @doc """
  `onceo` accepts a goal function, and allows it to succeed at most once.
  
  ## Examples
  
      iex> use(MiniKanren, :impure)
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
  
      iex> use(MiniKanren, :impure)
      iex> run_all([out, x, y, a, b]) do
      ...>   eq(x, [a, b])
      ...>   copy_term(x, y)
      ...>   eq(out, {x, y})
      ...> end
      [{[:_0, :_1], [:_2, :_3]}]
      
      iex> use(MiniKanren, :impure)
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
      eq(MK.walk_all(u, build_s(u, Map.new)), v)
    end
  end
  
  defp build_s(u, s) do
    case MK.var?(u) or u do
      true    -> Dict.put_new(s, u, MK.var(make_ref))
      [h | t] -> build_s(t, build_s(h, s))
      _       -> s
    end
  end
  
  @doc """
  `is` projects its argument `b`, and associates `a` with the result of the unary
  operation `f.(b)`
  
  ## Examples
  
      iex> use(MiniKanren, :impure)
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
  
      iex> use(MiniKanren, :impure)
      iex> run_all([x]) do
      ...>   fresho(x)
      ...>   eq(x, 1)
      ...> end
      [1]
      
      iex> use(MiniKanren, :impure)
      iex> run_all([x]) do
      ...>   eq(x, 1)
      ...>   fresho(x)
      ...> end
      []
  """
  def fresho(v) do
    fn s_c = {subs, _} ->
      case MK.var?(MK.walk(v, subs)) do
        false -> MK.mzero
        _     -> MK.unit(s_c)
      end
    end
  end
  
  @doc """
  `staleo` fails if its argument is a fresh logic variable, succeeds otherwise.
  
  ## Examples
  
      iex> use(MiniKanren, :impure)
      iex> run_all([x]) do
      ...>   eq(x, 1)
      ...>   staleo(x)
      ...> end
      [1]
      
      iex> use(MiniKanren, :impure)
      iex> run_all([x]) do
      ...>   staleo(x)
      ...>   eq(x, 1)
      ...> end
      []
  """
  def staleo(v) do
    fn s_c = {subs, _} ->
      case MK.var?(MK.walk(v, subs)) do
        false -> MK.unit(s_c)
        _     -> MK.mzero
      end
    end
  end
end
