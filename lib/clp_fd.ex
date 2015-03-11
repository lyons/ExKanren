defmodule MiniKanren.CLP.FD do
  @moduledoc """
  Tools for solving constraints over finite domains of integers.
  
  Provides the operators `dom`, `in_fd`, `lt_fd`, `lte_fd`, `gt_fd`, `gte_fd`, `sum_fd`,
  `product_fd`, `neq_fd`, `distinct_fd`.
  
  `use MiniKanren.CLP.FD` to import the operators and set the runtime hooks.
  `use MiniKanren.CLP.FD, :no_hooks` to just import the operators.
  `use MiniKanren.CLP.FD, :hooks` to just set the hooks.
  """
  
  ## TODO
  ## Domains use a list to represent an ordered set, use a better data structure for this
  ## sum_fd and product_fd should be able to force a domain on the third variable when two variables
  ##   have been bound to domains
  ## enforce_constraints should be able to force a domain on any variable that is constrained as both
  ##   the lhs and rhs of inequality constraints and is not bound to a domain
  ## better documentation and annotations
  
  # CONVENTIONS FOR SINGLE LETTER VARIABLES
  # x -> logic variable
  # u -> logic value
  # v -> logic value
  # c -> constraint
  # d -> domain
  # [h | t] -> head, tail
  # f -> function
  
  alias  MiniKanren, as: MK
  import MiniKanren, except: [process_log: 2, enforce_constraints: 1, reify_constraints: 2]
  import MiniKanren.Functions, only: [succeed: 0, onceo: 1]
  
  defmacro __using__(_) do
    quote do
      import MiniKanren.CLP.FD, only: [dom: 2, in_fd: 2, lt_fd: 2, lte_fd: 2, gt_fd: 2, gte_fd: 2,
                                       sum_fd: 3, product_fd: 3, neq_fd: 2, distinct_fd: 1]
      alias  MiniKanren.CLP.FD, as: CLP_FD
    end
  end
  
# Operators -----------------------------------------------------------------------------------------
  @spec dom(MK.logic_variable, MK.domain | Range.t) :: MK.goal
  @doc """
  Assigns a domain to a logic variable.
  
  ## Examples:
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.FD
    iex> run_all(CLP_FD, [x]) do
    ...>   dom(x, -3..1)
    ...> end
    [-3, -2, -1, 0, 1]
  """
  def dom(x, min..max), do: dom(x, range(min, max))
  def dom(x, n) when is_list(n) do
    fn pkg = {subs, _, _, _, _} ->
      process_d(walk(x, subs),
                make_d(n)).(pkg)
    end
  end
  
  @spec in_fd([MK.logic_variable], MK.domain | Range.t) :: MK.goal
  @doc """
  Assigns a domain to all members of a list of logic variables.
  
  ## Examples:
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.FD
    iex> run_all(CLP_FD, [out, x, y]) do
    ...>   eq(out, x)
    ...>   in_fd([x, y], 1..3)
    ...> end
    [1, 2, 3]
    
    iex> use MiniKanren
    iex> use MiniKanren.CLP.FD
    iex> run_all(CLP_FD, [out, x, y]) do
    ...>   eq(out, y)
    ...>   in_fd([x, y], 1..3)
    ...> end
    [1, 2, 3]
  """
  def in_fd(xs, min..max), do: in_fd(xs, range(min, max))
  def in_fd(xs, n) when is_list(xs) and is_list(n) do
    fn pkg = {subs, _, _, _, _} ->
      Enum.reduce(xs, fn id -> id end,
        fn (x, acc) ->
          compose_m(process_d(walk(x, subs), make_d(n)), acc)
        end).(pkg)
    end
  end
  
  @spec lt_fd(MK.logic_value, MK.logic_value) :: MK.goal
  @doc """
  Constrains `u` so it must always take on a value less than the value of `v`.
  """
  def lt_fd(u, v) do
    fn _pkg = {subs, cons, doms, counter, solver} ->
      u = walk(u, subs); v = walk(v, subs)
      u_d = if var?(u) do get_d(u, doms) else make_d([u]) end
      v_d = if var?(v) do get_d(v, doms) else make_d([v]) end
      cons = constraint(lt_fd(u, v), :lt_fd, [u, v])
             |> extend_constraints(cons)
      pkg = {subs, cons, doms, counter, solver}
      
      case Enum.all?([u_d, v_d]) do
        false -> pkg
        true  -> u_min = min_d(u_d)
                 v_max = max_d(v_d)
                 compose_m(process_d(u, copy_before(fn a -> v_max < a end, u_d)),
                           process_d(v, drop_before(fn a -> u_min < a end, v_d))).(pkg)
      end
    end
  end
  
  @spec lte_fd(MK.logic_value, MK.logic_value) :: MK.goal
  @doc """
  Constrains `u` so it must always take on a value less than of equal to the value of `v`.
  """
  def lte_fd(u, v) do
    fn _pkg = {subs, cons, doms, counter, solver} ->
      u = walk(u, subs); v = walk(v, subs)
      u_d = if var?(u) do get_d(u, doms) else make_d([u]) end
      v_d = if var?(v) do get_d(v, doms) else make_d([v]) end
      cons = constraint(lte_fd(u, v), :lte_fd, [u, v])
             |> extend_constraints(cons)
      pkg = {subs, cons, doms, counter, solver}
      
      case Enum.all?([u_d, v_d]) do
        false -> pkg
        true  -> u_min = min_d(u_d)
                 v_max = max_d(v_d)
                 compose_m(process_d(u, copy_before(fn a -> v_max < a end, u_d)),
                           process_d(v, drop_before(fn a -> u_min <= a end, v_d))).(pkg)
      end
    end
  end
  
  @spec gt_fd(MK.logic_value, MK.logic_value) :: MK.goal
  @doc """
  Constrains `u` so it must always take on a value greater than the value of `v`.
  """
  def gt_fd(u, v), do: lt_fd(v, u)
  
  @spec gte_fd(MK.logic_value, MK.logic_value) :: MK.goal
  @doc """
  Constrains `u` so it must always take on a value greater than or equal to the value of `v`.
  """
  def gte_fd(u, v), do: lte_fd(v, u)
  
  @spec sum_fd(MK.logic_value, MK.logic_value, MK.logic_value) :: MK.goal
  @doc """
  Constraint that ensures `u` + `v` = `w`.
  """
  def sum_fd(u, v, w) do
    fn _pkg = {subs, cons, doms, counter, solver} ->
      u = walk(u, subs); v = walk(v, subs); w = walk(w, subs)
      u_d = if var?(u) do get_d(u, doms) else make_d([u]) end
      v_d = if var?(v) do get_d(v, doms) else make_d([v]) end
      w_d = if var?(w) do get_d(w, doms) else make_d([w]) end
      cons = constraint(sum_fd(u, v, w), :sum_fd, [u, v, w])
             |> extend_constraints(cons)
      pkg = {subs, cons, doms, counter, solver}
      
      case Enum.all?([u_d, v_d, w_d]) do
        false -> pkg
        true  -> 
          u_min = min_d(u_d); u_max = max_d(u_d)
          v_min = min_d(v_d); v_max = max_d(v_d)
          w_min = min_d(w_d); w_max = max_d(w_d)
          
          w_range = range(u_min + v_min, u_max + v_max)
          u_range = range(w_min - v_max, w_max - v_min)
          v_range = range(w_min - u_max, w_max - u_min)
          
          compose_m(process_d(w, w_range),
                    compose_m(process_d(u, u_range),
                              process_d(v, v_range))).(pkg)
      end
    end
  end
  
  @spec product_fd(MK.logic_value, MK.logic_value, MK.logic_value) :: MK.goal
  @doc """
  Constraint that ensures `u` * `v` = `w`.
  """
  def product_fd(u, v, w) do
    fn _pkg = {subs, cons, doms, counter, solver} ->
      u = walk(u, subs); v = walk(v, subs); w = walk(w, subs)
      u_d = if var?(u) do get_d(u, doms) else make_d([u]) end
      v_d = if var?(v) do get_d(v, doms) else make_d([v]) end
      w_d = if var?(w) do get_d(w, doms) else make_d([w]) end
      cons = constraint(product_fd(u, v, w), :product_fd, [u, v, w])
             |> extend_constraints(cons)
      pkg = {subs, cons, doms, counter, solver}
      
      case Enum.all?([u_d, v_d, w_d]) do
        false ->
          pkg
        true  ->
          u_min = min_d(u_d); u_max = max_d(u_d)
          v_min = min_d(v_d); v_max = max_d(v_d)
          w_min = min_d(w_d); w_max = max_d(w_d)
          
          w_range = multiply_range(u_min, u_max, v_min, v_max)
          u_range = divide_range(w_min, w_max, v_min, v_max)
          v_range = divide_range(w_min, w_max, u_min, u_max)
          
          compose_m(process_d(w, w_range),
                    compose_m(process_d(u, u_range),
                              process_d(v, v_range))).(pkg)
      end
    end
  end
  
  @spec neq_fd(MK.logic_variable, MK.logic_variable) :: MK.goal
  @doc """
  Ensures two variables will never take on the same value.
  
  ## Examples:
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.FD
    iex> run_all(CLP_FD, [out, x, y]) do
    ...>   eq(out, [x, y])
    ...>   dom(x, 1..2)
    ...>   dom(y, 2..3)
    ...>   neq_fd(x, y)
    ...> end |> Enum.sort
    [[1, 2], [1, 3], [2, 3]]
  """
  def neq_fd(u, v) do
    fn pkg = {subs, cons, doms, counter, solver} ->
      u = walk(u, subs); v = walk(v, subs)
      u_d = if var?(u) do get_d(u, doms) else make_d([u]) end
      v_d = if var?(v) do get_d(v, doms) else make_d([v]) end
      cond do
        (u_d == false) or (v_d == false) ->
          cons = constraint(neq_fd(u, v), :neq_fd, [u, v])
          |> extend_constraints(cons)
          {subs, cons, doms, counter, solver}
        singleton_d?(u_d) and singleton_d?(v_d) and (u_d == v_d) ->
          mzero()
        disjoint_d?(u_d, v_d) ->
          pkg
        :else ->
          cons = constraint(neq_fd(u, v), :neq_fd, [u, v])
          |> extend_constraints(cons)
          pkg = {subs, cons, doms, counter, solver}
          cond do
            singleton_d?(u_d) -> process_d(v, diff_d(v_d, u_d)).(pkg)
            singleton_d?(v_d) -> process_d(u, diff_d(u_d, v_d)).(pkg)
            :else -> pkg
          end
      end
    end
  end
  
  @spec distinct_fd([MK.logic_value]) :: MK.goal
  @doc """
  Constrains the members of `vs` so they cannot take on any of the same values at the same time.
  
  ## Examples:
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.FD
    iex> run(5, CLP_FD, [out, x, y, z]) do
    ...>   eq(out, [x, y, z])
    ...>   in_fd([x, y], 1..3)
    ...>   dom(z, 2..4)
    ...>   distinct_fd([x, y, z])
    ...> end |> Enum.sort
    [[1, 2, 3], [1, 2, 4], [1, 3, 2], [2, 1, 3], [3, 1, 2]]
    
    iex> use MiniKanren
    iex> use MiniKanren.CLP.FD
    iex> run_all(CLP_FD, [out, x, y]) do
    ...>   eq(out, [x, y])
    ...>   in_fd([x, y], 1..3)
    ...>   distinct_fd([x, y, 2])
    ...> end |> Enum.sort
    [[1, 3], [3, 1]]
  """
  def distinct_fd(vs) do
    fn pkg = {subs, cons, doms, counter, solver} ->
      vs = walk(vs, subs)
      if var?(vs) do
        cons = constraint(distinct_fd(vs), :distinct_fd, [vs])
               |> extend_constraints(cons)
        {subs, cons, doms, counter, solver}
      else
        {xs, ns} = Enum.partition(vs, &MK.var?/1)
        ns = Enum.sort(ns)
        case strictly_ascending?(ns) do
          true  -> distinct_fd_c(xs, ns).(pkg)
          false -> mzero()
        end
      end
    end
  end
  
  @spec distinct_fd_c([MK.logic_variable], [integer]) :: MK.goal
  def distinct_fd_c(ys, ns) do
    fn pkg ->
      distinct_fd_c(ys, ns, [], pkg)
    end
  end
  
  @spec distinct_fd_c([MK.logic_variable], [integer], [MK.logic_variable], MK.package) :: MK.goal_stream
  def distinct_fd_c([h | t], ns, xs, pkg = {subs, _, _, _, _}) do
    y = walk(h, subs)
    cond do
      var?(y) ->
        distinct_fd_c(t, ns, [h | xs], pkg)
      member_d?(y, ns) ->
        mzero()
      :else ->
        ns = insert_in_sorted_list(y, ns)
        distinct_fd_c(t, ns, xs, pkg)
    end
  end
  
  def distinct_fd_c([], ns, xs, _pkg = {subs, cons, doms, counter, solver}) do
    cons = constraint(distinct_fd_c(xs, ns), :distinct_fd, [xs, ns])
           |> extend_constraints(cons)
    pkg = {subs, cons, doms, counter, solver}
    exclude_from_d(make_d(ns), doms, xs).(pkg)
  end
  
# CLP Hooks -----------------------------------------------------------------------------------------
  @spec process_log(MK.unification_log, MK.constraint_store) :: MK.goal
  def process_log([{x, v} | t], cons) do
    t = compose_m(run_constraints(Enum.into([x], HashSet.new), cons),
                  process_log(t, cons))
    fn pkg = {_, _, doms, _, _} ->
      case get_d(x, doms) do
        false -> t.(pkg)
        d     -> compose_m(process_d(v, d), t).(pkg)
      end
    end
  end
  def process_log([], _), do: fn pkg -> pkg end
    
  @spec enforce_constraints(MK.logic_variable) :: MK.goal
  def enforce_constraints(x) do
    fresh([]) do
      force_answer(x)
      fn pkg = {_, cons, doms, _, _} ->
        bound_vars = Enum.map(doms, fn {var, _} -> var end)
        verify_all_bound(cons, bound_vars)
        onceo(force_answer(bound_vars)).(pkg)
      end
    end
  end
  
  @spec force_answer([MK.logic_variable] | MK.logic_variable) :: MK.goal
  def force_answer(x) do
    fn pkg = {subs, _, doms, _, _} ->
      x = walk(x, subs)
      f = cond do
        d = var?(x) and get_d(x, doms) ->
          fn _ ->
            Enum.map(d, fn v -> bind(pkg, eq(v, x)) end)
            |> mplus_many()
          end
        is_list(x) and Enum.count(x) > 0 ->
          [h | t] = x
          fresh([]) do
            force_answer(h)
            force_answer(t)
          end
        :else ->
          succeed()
      end
      f.(pkg)
    end
  end
  
  # would be better if this found all unbound variables in error case
  @spec verify_all_bound(MK.constraint_store, [MK.logic_variable]) :: any
  def verify_all_bound(cons, bound_vars) do
    Enum.each(cons, fn c ->
      case constraint_operands(c)
           |> Enum.filter(&MK.var?/1)
           |> Enum.find(false, fn x -> (not Enum.member?(bound_vars, x)) end) do
        false -> :ok
        x     -> raise("Constrained variable #{IO.inspect(x)} without domain")
      end
    end)
  end
  
  @spec reify_constraints(MK.logic_value, MK.list_substitution) :: any
  @doc """
  If any variables remain constrained after `enforce_constraints` calls `force_answer`, something is
  wrong with your program.
  """
  def reify_constraints(_, _) do
    raise("Oops")
  end
  
# Wiring --------------------------------------------------------------------------------------------
  @spec process_d(MK.logic_value, MK.domain) :: MK.goal
  def process_d(v, d) do
    fn pkg ->
      cond do
        var?(v) ->
          update_var_d(v, d).(pkg)
        member_d?(v, d) ->
          pkg
        :else ->
          mzero()
      end
    end
  end
  
  @spec update_var_d(MK.logic_variable, MK.domain) :: MK.goal
  def update_var_d(x, d) do
    fn pkg = {_, _, doms, _, _} ->
      case get_d(x, doms) do
        false -> resolve_storable_d(d, x).(pkg)
        xd    -> case intersection_d(xd, d) do
                   [] -> mzero()
                   i  -> resolve_storable_d(i, x).(pkg)
                 end
      end
    end
  end
  
  @spec resolve_storable_d(MK.domain, MK.logic_variable) :: MK.goal
  def resolve_storable_d(d, x) do
    fn _pkg = {subs, cons, doms, counter, solver} ->
      case d do
        [n] -> var_set = Enum.into([x], HashSet.new())
               extended_pkg = {extend_substitution(x, n, subs), cons, doms, counter, solver}
               run_constraints(var_set, cons).(extended_pkg)
        _   -> {subs, cons, extend_domains(x, d, doms), counter, solver}
      end
    end
  end
  
  @spec exclude_from_d(MK.domain, MK.domain_store, [MK.logic_variable]) :: MK.goal
  def exclude_from_d(d, doms, [h | t]) do
    case get_d(h, doms) do
      false -> exclude_from_d(d, doms, t)
      d2    -> compose_m(process_d(h, diff_d(d2, d)),
                         exclude_from_d(d, doms, t))
    end
  end 
  def exclude_from_d(_, _, []), do: fn id -> id end
  
# Domain abstractions -----------------
  @spec get_d(MK.logic_variable, MK.domain_store) :: MK.domain | false
  @doc """
  Attempts to retrieve the domain associated with logic variable `x` from the domain store. Returns
  `false` if no domain is found.
  """
#  def get_d(x, [{x, d} | _]), do: d
#  def get_d(x, [{_, _} | t]), do: get_d(x, t)
#  def get_d(_, []), do: false
  def get_d(x, doms), do: HashDict.get(doms, x, false)
  
  @spec value_d?(MK.logic_value) :: boolean
  @doc """
  Determines whether `v` is a valid domain value.
  """ 
  def value_d?(v), do: is_integer(v)# and (v >= 0)
  
  @spec make_d([integer]) :: MK.domain
  @doc """
  Creates a domain from a sorted list of integers.
  """
  def make_d(n), do: Enum.sort(n)
  
  @spec singleton_d?(MK.domain) :: boolean
  @doc """
  Determines whether a domain has only one element.
  """
  def singleton_d?([_]), do: true
  def singleton_d?(_), do: false
  
  @spec min_d(MK.domain) :: integer
  @doc """
  Returns the smallest member of domain `d`.
  """
  def min_d(d), do: List.first(d)
  
  @spec max_d(MK.domain) :: integer
  @doc """
  Returns the largest member of domain `d`.
  """
  def max_d(d), do: List.last(d)
  
  @spec copy_before((integer -> boolean), MK.domain) :: MK.domain
  @doc """
  Returns all elements of the domain below the first value for which the predicate is true.
  """
  def copy_before(pred, [h | t]) do
    case pred.(h) do
      true  -> []
      false -> [h | copy_before(pred, t)]
    end
  end
  def copy_before(_, []), do: []
  
  @spec drop_before((integer -> boolean), MK.domain) :: MK.domain
  @doc """
  Returns all elements of the domain from the first value for which the predicate is true.
  """
  def drop_before(pred, d = [h | t]) do
    case pred.(h) do
      true  -> d
      false -> drop_before(pred, t)
    end
  end
  def drop_before(_, []), do: []
  
# Set operations ----------------------
  @spec member_d?(MK.logic_value, MK.domain) :: boolean
  @doc """
  Determines whether a value `v` is a member of domain `d`.
  """
  def member_d?(v, d), do: value_d?(v) and Enum.member?(d, v)
  
  @spec intersection_d(MK.domain, MK.domain) :: MK.domain
  @doc """
  Returns the intersection of two domains.
  """
  def intersection_d([], _), do: []
  def intersection_d(_, []), do: []
  def intersection_d([h | t1], [h | t2]), do: [h | intersection_d(t1, t2)]
  def intersection_d(d1 = [h1 | t1], d2 = [h2 | t2]) do
    if h1 > h2 do
      intersection_d(d1, t2)
    else
      intersection_d(t1, d2)
    end
  end
  
  @spec disjoint_d?(MK.domain, MK.domain) :: boolean
  @doc """
  Determines whether two domains are disjoint.
  """
  def disjoint_d?([], _), do: true
  def disjoint_d?(_, []), do: true
  def disjoint_d?([h | _], [h | _]), do: false
  def disjoint_d?(d1 = [h1 | t1], d2 = [h2 | t2]) do
    case h1 < h2 do
      true  -> disjoint_d?(t1, d2)
      false -> disjoint_d?(d1 ,t2)
    end
  end
  
  @spec diff_d(MK.domain, MK.domain) :: MK.domain
  @doc """
  Returns all elements of `d1` not present in `d2`.
  """
  def diff_d([], _), do: []
  def diff_d(d1, []), do: d1
  def diff_d([h | t1], [h | t2]), do: diff_d(t1, t2)
  def diff_d(d1 = [h1 | t1], d2 = [h2 | t2]) do
    case h1 < h2 do
      true  -> [h1 | diff_d(t1, d2)]
      false -> diff_d(d1, t2)
    end
  end
    
# Helpers -----------------------------  
  @spec range(integer, integer) :: [integer]
  @doc """
  Returns a list of integers from `min` to `max`.
  """
  def range(min, max) when min <= max do
    Enum.into(min..max, [])
  end
  
  @spec insert_in_sorted_list(integer, [integer]) :: [integer]
  @doc """
  Inserts an integer at the correct location in a sorted list of integers.
  """
  def insert_in_sorted_list(n, ls = [h | t]) do
    case n > h do
      true  -> [h | insert_in_sorted_list(n, t)]
      false -> [n | ls]
    end
  end
  def insert_in_sorted_list(n, []), do: [n]
  
  @spec strictly_ascending?([integer]) :: boolean
  @doc """
  Determines whether a list of integers is strictly ascending.
  """
  def strictly_ascending?([n1, n2 | t]) do
    case n1 < n2 do
      true  -> strictly_ascending?([n2 | t])
      false -> false
    end
  end
  def strictly_ascending?([_]), do: true
  def strictly_ascending?([]), do: true
  
  @spec multiply_range(integer, integer, integer, integer) :: [integer]
  @doc """
  Generates the range of possible values from multiplying the ranges `[u_min, u_max]` and
  `[v_min, v_max]`
  """
  def multiply_range(u_min, u_max, v_min, v_max) do
    case {u_min >= 0, u_max >= 0, v_min >= 0, v_max >= 0} do
      {true,  true,  true,  true}  -> range(u_min * v_min, u_max * v_max)
      {true,  true,  false, true}  -> range(u_max * v_min, u_max * v_max)
      {true,  true,  false, false} -> range(u_max * v_min, u_min * v_max)
      {false, true,  true,  true}  -> range(u_min * v_max, u_max * v_max)
      {false, true,  false, true}  -> range(min(u_min * v_max, u_max * v_min),
                                            max(u_max * v_max, u_min * v_min))
      {false, true,  false, false} -> range(u_max * v_min, u_min * v_min)
      {false, false, true,  true}  -> range(u_min * v_max, u_max * v_min)
      {false, false, false, true}  -> range(u_min * v_max, u_min * v_min)
      {false, false, false, false} -> range(u_max * v_max, u_min * v_min)
    end
  end
  
  @spec divide_range(integer, integer, integer, integer) :: [integer]
  @doc """
  Generates that range of possible values that could multiply against the range `[u_min, u_max]` to
  produce values in `[w_min, w_max]`
  """
  def divide_range(w_min, w_max, u_min, u_max) do
    lower = fn
      (dividend, 0) -> dividend
      (dividend, divisor) ->
        quotient = div(dividend, divisor)
        if rem(dividend, divisor) != 0 do
          case {divisor > 0, dividend >= 0} do
            {true, true}   -> quotient + 1
            {true, false}  -> quotient
            {false, true}  -> quotient
            {false, false} -> quotient + 1
          end
        else
          quotient
        end
    end
    upper = fn
      (dividend, 0) -> dividend
      (dividend, divisor) ->
      quotient = div(dividend, divisor)
        if rem(dividend, divisor) != 0 do
          case {divisor > 0, dividend >= 0} do
            {true, true}   -> quotient
            {true, false}  -> quotient - 1
            {false, true}  -> quotient - 1
            {false, false} -> quotient
          end
        else
          quotient
        end
    end
    case {w_min >= 0, w_max >= 0, u_min >= 0, u_max >= 0} do
      {true,  true,  true,  true}  -> range(lower.(w_min, u_max), upper.(w_max, u_min))
      {true,  true,  false, true}  -> range(lower.(w_max, -1),    upper.(w_max, 1))
      {true,  true,  false, false} -> range(lower.(w_max, u_max), upper.(w_min, u_max))
      {false, true,  true,  true}  -> range(lower.(w_min, u_min), upper.(w_max, u_min))
      {false, true,  false, true}  -> range(min(lower.(w_min, 1), lower.(w_max, -1)),
                                            max(upper.(w_max, 1), upper.(w_min, -1)))
      {false, true,  false, false} -> range(lower.(w_max, u_max), upper.(w_min, u_max))
      {false, false, true,  true}  -> range(lower.(w_min, u_min), upper.(w_max, u_max))
      {false, false, false, true}  -> range(lower.(w_min, 1),     upper.(w_min, -1))
      {false, false, false, false} -> range(lower.(w_max, u_min), upper.(w_min, u_max))
    end
  end
end