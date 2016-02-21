defmodule MiniKanren.CLP.Tree do
  @moduledoc """
  Provides the tree disequality operator `neq`, the type constraint operators `symbolo`, `numbero`,
  and `booleano`, and the term absence operator `absento`.
  
  `use MiniKanren.CLP.Tree` to import the operators.
  """
  
  # CONVENTIONS FOR SINGLE LETTER VARIABLES
  # x -> logic variable
  # u -> logic term
  # v -> logic term
  # d -> disequality constraint store
  # a -> type constraint store
  # t -> absento constraint store
  
  alias  MiniKanren, as: MK
  import MiniKanren, except: [post_unify: 2, enforce_constraints: 1, reify_constraints: 2,
                              empty_constraint_store: 0, empty_domain_store: 0]
  
  defmacro __using__(:no_functions) do
    quote do
      import MiniKanren.CLP.Tree, only: [neq: 2, symbolo: 1, numbero: 1, booleano: 1, absento: 2]
      alias  MiniKanren.CLP.Tree, as: CLP_Tree
    end
  end
  defmacro __using__(_) do
    quote do
      import MiniKanren.CLP.Tree, only: [neq: 2, symbolo: 1, numbero: 1, booleano: 1, absento: 2]
      alias  MiniKanren.CLP.Tree, as: CLP_Tree
      import MiniKanren.CLP.Tree.Functions
    end
  end
  
  @typep predicate :: ((any) -> boolean)
  @typep perhaps(t) :: t | false
  
  @typep disequality_constraint :: MK.list_substitution
  @typep disequality_store :: list(disequality_constraint)
  @typep type_constraint :: {atom, predicate}
  @typep type_store :: %{MK.logic_variable => type_constraint}
  @typep absento_constraint :: atom
  @typep absento_store :: %{MK.logic_variable => list(absento_constraint)}
  @typep constraint_store :: {disequality_store, type_store, absento_store}
  
## ---------------------------------------------------------------------------------------------------
## Operators
  
  @spec neq(MK.logic_term, MK.logic_term) :: MK.goal
  @doc """
  `neq` ensures two logic terms will never unify.
  
  ## Examples:
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out]) do
    ...>   neq(out, 1)
    ...>   membero(out, [1, 2, 3])
    ...>   neq(out, 3)
    ...> end
    [2]
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out]) do
    ...>   neq(out, 2)
    ...> end
    [[:_0 | {:neq, [[{:_0, 2}]]}]]
  """
  def neq(u, v) do
    fn pkg = {subs, _cons = {d, a, t}, doms, counter, solver} ->
      case unify(u, v, subs) do
        nil          -> unit(pkg)
        {^subs, []}  -> mzero
        {_, log}     ->
          d = post_unify_neq(log, d, a, t)
          unit({subs, {d, a, t}, doms, counter, solver})
      end
    end
  end
    
  @spec symbolo(MK.logic_term) :: MK.goal
  @doc """
  `symbolo` constrains a term to always be a symbol.
  
  ## Examples:
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out]) do
    ...>   symbolo(out)
    ...> end
    [[:_0, {:sym, [:_0]}]]
    
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out]) do
    ...>   symbolo(out)
    ...>   eq(out, 5)
    ...> end
    []
  """
  def symbolo(x) do
    make_tag_A(:sym, &is_atom/1).(x)
  end
  
  @spec numbero(MK.logic_term) :: MK.goal
  @doc """
  `numbero` constrains a term to always be a number.
  
  ## Examples:
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out]) do
    ...>   numbero(out)
    ...> end
    [[:_0, {:num, [:_0]}]]
    
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out]) do
    ...>   numbero(out)
    ...>   eq(out, :five)
    ...> end
    []
  """
  def numbero(x) do
    make_tag_A(:num, &is_number/1).(x)
  end
  
  @spec booleano(MK.logic_term) :: MK.goal
  @doc """
  `booleano` constrains a term to always be a symbol.
  
  ## Examples:
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out]) do
    ...>   booleano(out)
    ...> end
    [[:_0, {:bool, [:_0]}]]
    
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out]) do
    ...>   booleano(out)
    ...>   eq(out, 5)
    ...> end
    []
  """
  def booleano(x) do
    make_tag_A(:bool, &is_boolean/1).(x)
  end
  
  @spec absento(atom, MK.logic_term) :: MK.goal
  @doc """
  `absento` constrains a term so a symbol will not be present in it.
  
  ## Examples:
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out, x, y]) do
    ...>   eq(out, [x, y])
    ...>   absento(:foo, out)
    ...> end
    [[[:_0, :_1], {:absent, :foo, :_0}, {:absent, :foo, :_1}]]
    
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out, x, y]) do
    ...>   absento(:foo, out)
    ...>   eq(out, [x, y])
    ...>   eq(x, :foo)
    ...> end
    []
  """
  def absento(tag, u) when is_atom(tag) do
    case tag?(tag) do
      true  ->
        fn _pkg = {subs, _cons = {d, a, t}, doms, counter, solver} ->
          case absento_plus(u, tag, subs, d, a, t) do
            cons = {_d, _a, _t} -> unit({subs, cons, doms, counter, solver})
            false -> mzero
          end
        end
      false -> fn _ -> mzero end
    end
  end

## ---------------------------------------------------------------------------------------------------
## Solver callbacks
  
  @spec post_unify(MK.unification_log, constraint_store) :: MK.goal
  def post_unify(log, _) do
    fn _pkg = {subs, _cons = {d, a, t}, doms, counter, solver} ->
      case verify_constraints(subs, d, a, t, log) do
        cons = {_d, _a, _t} -> unit({subs, cons, doms, counter, solver})
        false -> mzero
      end
    end
  end

  @spec enforce_constraints(any) :: MK.goal
  def enforce_constraints(_), do: &MK.unit/1
  
  @spec reify_constraints(MK.logic_variable, MK.substitution) :: any
  @docp """
  Removes any constraints on fresh variables from the three stores, flattens the type and absento
  constraint stores to lists of the form `[{x, tag}, ...]` and reifies names for all constraints.
  """
  def reify_constraints(v, reified_subs) do
    fn _pkg = {_subs, {d, a, t}, _doms, _counter, _solver} ->
      d = Enum.reject(d, fn x -> any_var?(x, reified_subs) end)
          |> rem_subsumed
          |> walk_all(reified_subs)
      
      a = Enum.reject(a, fn {al, _ar} -> walk(al, reified_subs) |> var? end)
          |> Enum.map(fn {x, {tag, _pred}} -> {x, tag} end)
          |> walk_all(reified_subs)
      
      t = Enum.reject(t, fn {tl, _tr} -> walk(tl, reified_subs) |> var? end)
          |> Enum.flat_map(fn {x, ls} -> Enum.map(ls, fn tag -> {x, tag} end) end)
          |> walk_all(reified_subs)
      
      v = walk_all(v, reified_subs)
      
      form_result(v, d, a, t)
    end
  end
  
  @spec empty_constraint_store() :: constraint_store
  def empty_constraint_store(), do: {[], Map.new(), Map.new()}
  
  @spec empty_domain_store() :: nil
  def empty_domain_store(), do: nil

## ---------------------------------------------------------------------------------------------------
## Plumbing for symbolo, numbero, booleano
  
  @spec make_tag_A(atom, predicate) :: ((MK.logic_variable) -> MK.goal)
  @docp """
  Handles creating type constraints for `symbolo`, `numbero`, `booleano`, &c.
  If the logic term `u` represents a fresh variable, attempts to add a new constraint. If `u` is not a
  variable, tests with the predicate and fails/succeeds immediately with no need to create a new
  constraint.
  """
  defp make_tag_A(tag, predicate) do
    fn u ->
      fn pkg = {subs, _cons = {d, a, t}, doms, counter, solver} ->
        x = walk(u, subs)
        case var?(x) do
          true -> case make_tag_A_plus(x, tag, predicate, subs, d, a, t) do
                    false -> mzero
                    cons  -> unit({subs, cons, doms, counter, solver})
                  end
          false -> case predicate.(x) do
                     true  -> unit(pkg)
                     false -> mzero
                   end
        end
      end
    end
  end
  
  @spec make_tag_A_plus(MK.logic_variable, atom, predicate, MK.substitution, disequality_store,
                        type_store, absento_store) :: perhaps(constraint_store)
  @docp """
  If possible, extends the type constraints with the new constraint `{tag, pred}` on `x`, and updates
  the disequality and absento constraint stores to remove anything subsumed by the new  constraint.
  Fails if the new constraint contradicts an existing type constraint. 
  """
  defp make_tag_A_plus(x, tag, pred, subs, d, a, t) do
    case ext_A?(x, tag, a) do
      :ok ->
        a_plus = {tag, pred}
        a = Dict.put(a, x, a_plus)
        d = subsume(x, a_plus, d)
        {d, t} = update_D_T(x, subs, d, a, t)
        {d, a, t}
      false      -> false
      :no_action -> {d, a, t}
    end
  end
  
  @spec ext_A?(MK.logic_variable, atom, type_store) :: :ok | :no_action | false
  @docp """
  Determines whether we can extend the type constraints with the constraint `{tag, pred}`, on `x`.
  
  If `x` is already constrained with a different tag, the operation fails; if `x` is already
  constrained with the same tag, no action is required. Otherwise, returns ok to extend constraints.
  """
  defp ext_A?(x, tag, a) do
    case Dict.get(a, x) do
      nil        -> :ok
      {a_tag, _} -> case tag_eq?(tag, a_tag) do
                      true  -> :no_action
                      false -> false
                    end
    end
  end
  
  @spec subsume(MK.logic_variable, type_constraint, disequality_store) :: disequality_store
  @docp """
  Removes any disequality constraints that have been subsumed by the newly created type constraint.
  
  A disequality constraint is subsumed when it constrains a variable to be not equal to a value of a
  type other than the one in the type constraint.
  """
  defp subsume(x, {_tag, pred}, d) do    
    subsumed_pr? = fn {v, u} ->
      case var?(u) do
        true  -> false
        false -> case v == x do
                   false -> false
                   true  -> not pred.(u)
                 end
      end
    end
    
    Enum.reject(d, fn foo -> Enum.any?(foo, subsumed_pr?) end)
  end
  
## ---------------------------------------------------------------------------------------------------
## Plumbing for absento
  
  @spec absento_plus(MK.logic_term, atom, MK.substitution, disequality_store, type_store,
                     absento_store) :: perhaps(constraint_store)
  @docp """
  Creates an absento constraint on a logic term `u`.
  
  If `u` is a variable, creates a new constraint and adds it to the store.
  If `u` is a value, tests against it and succeeds/fails without creating a constraint.
  If `u` is a container, we reapply these rules to all elements in the container.
  """
  defp absento_plus(u, tag, subs, d, a, t) do
    x = walk(u, subs)
    case var?(x) or x do
      true -> case ext_T(x, tag, t) do
                ^t -> {d, a, t}
                t  -> d = subsume_d_t(d, t)
                      subsume_T(subs, d, a, t)
              end
      [u1 | u2] -> case absento_plus(u1, tag, subs, d, a, t) do
                    false     -> false
                    {d, a, t} -> absento_plus(u2, tag, subs, d, a, t)
                  end
      {u1, u2}  -> case absento_plus(u1, tag, subs, d, a, t) do
                     false     -> false
                     {d, a, t} -> absento_plus(u2, tag, subs, d, a, t)
                   end
      {u1, u2, u3} -> case absento_plus(u1, tag, subs, d, a, t) do
                        false     -> false
                        {d, a, t} -> case absento_plus(u2, tag, subs, d, a, t) do
                                       false     -> false
                                       {d, a, t} -> absento_plus(u3, tag, subs, d, a, t)
                                     end
                      end
      v -> case tag?(v) and tag_eq?(v, tag) do
             true  -> false
             false -> {d, a, t}
           end
    end
  end
  
  @spec ext_T(MK.logic_variable, atom, absento_store) :: absento_store
  @docp """
  Extends the absento store with a new constraint on `x`, unless the constraint already exists on `x`
  """
  defp ext_T(x, tag, t) do
    case Dict.get(t, x) do
      nil  -> Dict.put(t, x, [tag])
      list -> case Enum.member?(list, tag) do
                 false -> Dict.update(t, x, [tag], fn ls -> [tag | ls] end)
                 true  -> t
               end
    end
  end
  
## ---------------------------------------------------------------------------------------------------
## Constraint management
  
  @spec post_unify_neq(MK.unification_log, disequality_store, type_store, absento_store)
                      :: disequality_store
  @docp """
  Removes any newly introduced disequality constraints that are subsumed by existing type or absento
  constraints, extends the disequality constraint store with whatever remains.
  """
  defp post_unify_neq(log, d, a, t) do
    d_plus = [log] 
             |> subsume_d_a(a)
             |> subsume_d_t(t)
    d_plus ++ d
  end
  
  @spec verify_constraints(MK.substitution, disequality_store, type_store, absento_store,
                           MK.unification_log) :: perhaps(constraint_store)
  @docp """
  Verifies no constraints have been violated and removes any unneeded constraints from the constraint
  store.
  """
  defp verify_constraints(subs, d, a, t, log) do
    case verify_D(d, subs) do
      false -> false
      d     -> case verify_A(a, subs, log) do
                 false -> false
                 a     -> d = subsume_d_a(d, a)
                          # ^ Could move this after verify_T to avoid possibly uneeded function call
                          case verify_T(t, subs, log) do
                            false -> false
                            t     -> d = subsume_d_t(d, t)
                                     subsume_T(subs, d, a, t)
                          end
               end
    end
  end
  
  @spec subsume_d_a(disequality_store, type_store) :: disequality_store
  @docp """
  Removes any disequality constraints that have been subsumed by a type constraint.
  
  A disequality constraint is subsumed when it constrains a variable to be not equal to a value of a
  type other than the one in the type constraint.
  """
  defp subsume_d_a(d, a) do
    subsumed_pr? = fn {u, v} ->
      case var?(v) do
        true  -> false
        false -> case Dict.get(a, u) do
                   nil -> false
                   {_, pred} -> not pred.(v)
                 end
      end
    end
    
    Enum.reject(d, fn foo -> Enum.any?(foo, subsumed_pr?) end)
  end
  
  @spec subsume_d_t(disequality_store, absento_store) :: disequality_store
  @docp """
  Removes any disequality constraints that have been subsumed by an absento constraint.
  
  A disequality constraint is subsumed when it contains at least one pair `{u, v}` where `v` is a tag
  present in the absento constraints.
  """
  defp subsume_d_t(d, t) do
    subsumed_pr? = fn {u, v} ->
      case var?(v) do
        true  -> false
        false -> case Dict.get(t, u) do
                   nil  -> false
                   cons -> Enum.any?(cons, fn tag -> tag?(v) and tag_eq?(tag, v) end)
                 end
      end
    end
    
    Enum.reject(d, fn foo -> Enum.any?(foo, subsumed_pr?) end)
  end
    
  
  ##########################
  ## Disequality constraints
  
  @spec verify_D(disequality_store, MK.substitution) :: perhaps(disequality_store)
  @docp """
  Iterates over the disequality constraints to ensure none have been violated, and removes constraints
  no longer needed from the store.
  """
  defp verify_D(_d = [dh | dt], subs) do
    case verify_D(dt, subs) do
      false  -> false
      d_plus -> verify_D(dh, d_plus, subs)
    end
  end
  defp verify_D([], _), do: []
  
  @spec verify_D(disequality_constraint, disequality_store, MK.substitution)
                :: perhaps(disequality_store)
  @docp """
  If unifying the disequality constraint with the substitutions fails, the constraint is satisfied and
  does not need to be retained.
  If unifying the disequality constraint with the substitutions does not alter the substitutions, the
  constraint is violated and verification fails.
  Otherwise, we retain the unsatisfied portion of the constraint in the store.
  """
  defp verify_D(d, ds, subs) do
    case unify_list(d, subs) do
      nil        -> ds
      {^subs, _} -> false
      {_, log}   -> [log | ds]
    end
  end
  
  
  ##################
  # Type constraints
  
  @spec verify_A(type_store, MK.substitution, MK.unification_log) :: perhaps(type_store)
  defp verify_A(a, subs, log), do: verify_A(a, subs, log, [])
  
  @spec verify_A(type_store, MK.substitution, MK.unification_log, MK.unification_log)
                :: perhaps(type_store)
  @docp """
  Verifies that no type constraints have been violated by extending the substitutions.
  
  Steps through the pairs {u, v} in the unification log with the following reasoning:
    - If v is a variable we check whether u has an existing type constraint
      - If it does not, no action is required
      - If it does, we walk v and check whether is is a variable, and whether it is constrained
        - If walked_v is a variable, u and walked_v now represent the same variable thus:
          - If u and v have the same constraint, we drop u's constraint from the store
          - If u and v have different constraints, this is a contradiction and verification fails
          - If v is not constrained, we shift u's constraint on to v
        - If v is not a variable, we test u's predicate against it and fail or continue accordingly
   - If v is not a variable we defer testing it until we have finished verifying and shifting
     constraints on variable pairs
  """
  defp verify_A(a, subs, [s = {u, v} | tail], deferred) do
    case var?(v) do
      true  -> case Dict.get(a, u) do
                 {tag, pred} ->
                   walked_v = walk(v, subs)
                   case var?(walked_v) and Dict.get(a, walked_v) do
                     {^tag, _pred} -> Dict.delete(a, u) |> verify_A(subs, tail, deferred)
                     {_, _} -> false
                     nil    -> Dict.delete(a, u)
                               |> Dict.put(v, {tag, pred})
                               |> verify_A(subs, tail, deferred)
                     false  -> case pred.(v) do
                                 false -> false
                                 true  -> Dict.delete(a, u) |> verify_A(subs, tail, deferred)
                               end
                   end
                 nil -> verify_A(a, subs, tail, deferred)
               end
      false -> verify_A(a, subs, tail, [s | deferred])
    end
  end
  @docp """
  Tests the deferred pairs from above, removing satisfied constraints or failing verfication. 
  """
  defp verify_A(a, subs, [], [{u, v} | tail]) do
    # Do we really need to defer these constraints?
    # Can the unifier do something weird here on complex terms and mess us up?
    # I reasoned out this section of code rather late at night and can't remember why.
    case Dict.get(a, u) do
      {_tag, pred} -> case pred.(v) do
                        false -> false
                        true  -> Dict.delete(a, u) |> verify_A(subs, [], tail)
                      end
      nil -> verify_A(a, subs, [], tail)
    end
  end
  defp verify_A(a, _, [], []), do: a
  
  
  #####################
  # Absento constraints
  
  @spec verify_T(absento_store, MK.substitution, MK.unification_log) :: perhaps(absento_store)
  @docp """
  Verifies that no absento constraints have been violated by extending the substitutions.
  
  Steps through the pairs {u, v} in the unification log with the following reasoning:
    - Check if u has an existing absento constraint
      - If not, there is nothing to do, continue checking the rest of the unification log
      - If u does have a constraint, we delete u's constraint and act as follows:
        - If v walks to a variable, we add u's constraint to v
        - If v walks to a value, we verify it does not violate u's constraint
        - If v walks to a container type, we reapply these rules to all elements of the container
  """
  defp verify_T(t, subs, _log = [{u, v} | tail]) do
    case Dict.get(t, u) do
      nil  -> verify_T(t, subs, tail)
      cons -> t = Dict.delete(t, u)
              case verify_T_plus(v, cons, t, subs) do
                false -> false
                t     -> verify_T(t, subs, tail)
              end
    end
  end
  defp verify_T(t, _, []), do: t
  
  @spec verify_T_plus(MK.logic_variable, list(absento_constraint), absento_store, MK.substitution)
                     :: absento_store
  defp verify_T_plus(x, cons, t, subs) do
    x = walk(x, subs)
    case var?(x) or x do
      true -> Dict.update(t, x, cons, fn ls -> (cons ++ ls) |> Enum.uniq end)
      [u1 | u2] -> case verify_T_plus(u1, cons, t, subs) do
                     false -> false
                     t0_   -> verify_T_plus(u2, cons, t0_, subs)
                   end
      {u1, u2}  -> case verify_T_plus(u1, cons, t, subs) do
                     false -> false
                     t0_   -> verify_T_plus(u2, cons, t0_, subs)
                   end
      {u1, u2, u3} -> case verify_T_plus(u1, cons, t, subs) do
                        false -> false
                        t0_   -> case verify_T_plus(u2, cons, t0_, subs) do
                                   false -> false
                                   t1_   -> verify_T_plus(u3, cons, t1_, subs)
                                 end
                      end
      u -> Enum.all?(cons, fn tag -> not (tag?(u) and tag_eq?(tag, u)) end) and t
    end
  end
  
  
  #######################
  # subsume_T and friends
  
  @spec subsume_T(MK.substitution, disequality_store, type_store, absento_store) :: constraint_store
  @docp """
  Removes any absento constraints that have been subsumed by a type constraint.
  
  If a variable is constrained to a type other than symbol, that variable's absento constraints can be
  dropped entirely; otherwise, the constraints can be turned into disequality constraints with the
  symbols constrained by absento.
  """
  defp subsume_T(subs, d, a, t) do
    xs = Dict.keys(a)
    {d, t} = Enum.reduce(xs, {d, t}, fn (x, {d, t}) -> update_D_T(x, subs, d, a, t) end)
    {d, a, t}
  end
  
  @spec update_D_T(MK.logic_variable,  MK.substitution, disequality_store, type_store, absento_store)
                  :: {disequality_store, absento_store}
  @docp """
  Removes any absento constraints on the variable `x` because they have been subsumed by a type
  constraint. If the type is constrained to a symbol, the subsemed absento constraint's tag(s)
  are turned into disequality constraints. Otherwise, the absento constraints are dropped entirely.
  """
  defp update_D_T(x, subs, d, a, t) do
    {tag, _pred} = Dict.get(a, x)
    cond do
      tag_eq?(tag, :sym) -> update_D_T_plus(x, subs, d, t)
      :else -> t = Dict.delete(t, x)
               {d, t}
    end
  end 
  
  @spec update_D_T_plus(MK.logic_variable, MK.substitution, disequality_store, absento_store)
                       :: {disequality_store, absento_store}
  @docp """
  Shifts any absento constraints on `x` to disequality constraints on `x`.
  """
  defp update_D_T_plus(x, subs, d, t) do
    case Dict.get(t, x) do
      nil -> {d, t}
      ls  -> d = ext_D(x, ls, d, subs)
             t = Dict.delete(t, x)
             {d, t}
    end
  end
  
  @spec ext_D(MK.logic_variable, list(absento_constraint), disequality_store, MK.substitution)
             :: disequality_store
  @docp """
  Extends the disequality constraint store with a list of subsumed absento constraints. Avoids
  duplicating constraints already in the disequality store.
  """
  defp ext_D(x, [tag | tail], d, subs) do
    case Enum.any?(d, fn [{y, u} | []] -> (walk(y, subs) == x) and tag?(u) and tag_eq?(u, tag)
                         [{_, _} | _t] -> false
                      end) do
      true  -> ext_D(x, tail, d, subs)
      false -> ext_D(x, tail, [[{x, tag}] | d], subs)
    end
  end
  defp ext_D(_, [], d, _), do: d
    
## ---------------------------------------------------------------------------------------------------
## Owlcats
  
  @spec tag_eq?(atom, atom) :: boolean
  #            ʌ⏜ʌ
  defp tag_eq?(o,o), do: true
  defp tag_eq?(_,_), do: false
  
  @spec tag?(any) :: boolean
  defp tag?(x), do: is_atom(x)
  
#  def show_package() do
#    fn pkg ->
#      IO.inspect(pkg)
#      unit(pkg)
#    end
#  end
  
## ---------------------------------------------------------------------------------------------------
## Reification helpers
  
  @spec any_var?(MK.logic_term, MK.substitution) :: boolean
  @docp """
  Checks whether the given logic term contains any fresh variables.
  """
  defp any_var?(u, subs) do
    case u do
      [u1 | u2] -> any_var?(u1, subs) or any_var?(u2, subs)
      {u1, u2}  -> any_var?(u1, subs) or any_var?(u2, subs)
      {u1, u2, u3} -> any_var?(u1, subs) or any_var?(u2, subs) or any_var?(u3, subs)
      x -> walk(x, subs) |> var?
    end
  end
  
  defp rem_subsumed(d), do: rem_subsumed(d, [])
  
  @docp """
  Removes any reified disequality constraints that have been subsumed by other reified disequality
  constraints.
  """
  defp rem_subsumed([dh | dt], d_plus) do
    case subsumed?(dh, dt) or subsumed?(dh, d_plus) do
      true  -> rem_subsumed(dt, d_plus)
      false -> rem_subsumed(dt, [dh | d_plus])
    end
  end
  defp rem_subsumed([], d_plus), do: d_plus
  
  defp subsumed?(d, [dh | dt]) do
    case unify_list(dh, d) do
      {^d, []} -> true
      _        -> subsumed?(d, dt)
    end
  end
  defp subsumed?(_, []), do: false
    
  @docp """
  Forms the final refified result. Result takes the order: result term, disequality constraints (if
  any), absento constraints (if any), type constaints (if any). Constraint sets are sorted to provide
  consistent result order.
  """
  defp form_result(v, d, a, t) do
    fd = Enum.map(d, &Enum.sort/1) |> Enum.sort
    fa = form_type_store(a)
    ft = Enum.sort(t) |> Enum.map(fn {x, tag} -> {:absent, tag, x} end)
    fb = ft ++ fa
    
    cond do
      fd == [] and fb == [] -> v
      fd == [] -> [v | fb]
      fb == [] -> [v | {:neq, fd}]
      :else -> [v, {:neq, fd} | fb]
    end
  end
  
  @docp """
  Takes a list of reified type constraints in the form `[{x1, tag1}, {x2, tag2}, {x3, tag1}, ...]`
  and returns a sorted list of the form `[{tag1, [x1, x3, ...]}, {tag2, [x2, ...]}, ...]`
  """
  defp form_type_store(a) do
    Enum.reduce(a, %{}, fn {x, tag}, acc -> Map.update(acc, tag, [x], fn ls -> [x | ls] end) end)
    |> Enum.map(fn {tag, ls} -> {tag, Enum.sort(ls)} end)
    |> Enum.sort
  end
end
  
defmodule MiniKanren.CLP.Tree.Functions do
  use MiniKanren
  use MiniKanren.CLP.Tree, :no_functions
  
  @doc """
  Ensures that all elements of `ls` are distinct.
  
  ## Examples
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out, x, y, z]) do
    ...>   distincto([x, y, z])
    ...>   conde do
    ...>     [eq(x, 1), eq(y, 2), eq(z, 3)]
    ...>     [eq(x, 1), eq(y, 1), eq(z, 5)]
    ...>   end
    ...>   eq(out, [x, y, z])
    ...> end
    [[1, 2, 3]]
  """
  def distincto(ls) do
    conde do
      [eq(ls, [])]
      [fresh([x]) do
        eq(ls, [x])
      end]
      [fresh([fst, snd, tail]) do
        eq(ls, [fst, snd | tail])
        neq(fst, snd)
        distincto([fst | tail])
        distincto([snd | tail])
      end]
    end
  end
  
  @doc """
  Removes all occurences of `x` from `ls`
  
  ## Examples
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out, x]) do
    ...>   eq(x, [1, 2, 1, 3, 4, 5, 1])
    ...>   rembero(1, x, out)
    ...> end
    [[2, 3, 4, 5]]
  """
  def rembero(x, ls, out) do
    conde do
      [eq([], ls), eq([], out)]
      [fresh([h, t, res]) do
        eq([h | t], ls)
        rembero(x, t, res)
        conde do
          [eq(h, x), eq(res, out)]
          [neq(h, x), eq([h | res], out)]
        end
      end]
    end
  end
  
  @doc """
  Removes the first occurence of `x` from `ls`
  
  ## Examples
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out, x]) do
    ...>   eq(x, [1, 2, 1, 3, 4, 5, 1])
    ...>   rember_firsto(1, x, out)
    ...> end
    [[2, 1, 3, 4, 5, 1]]
  """
  def rember_firsto(x, ls, out) do
    conde do
      [eq(ls, []), eq(out, [])]
      [fresh([_h, t]) do
        eq([x | t], ls)
        eq(t, out)
      end]
      [fresh([h, t, res]) do
        eq([h | t], ls)
        eq([h | res], out)
        neq(x, h)
        rember_firsto(x, t, res)
      end]
    end
  end
  
  @doc """
  Relates `lhs` to all possible permutations of `rhs`. Returns curious results
  if `rhs` contains any fresh variables.
  
  ## Examples
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out, x, y, z]) do
    ...>   permuteo([x, y, z], [2, 3, 1])
    ...>   eq(out, [x, y, z])
    ...> end |> Enum.sort
    [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]]
  
    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> run_all(CLP_Tree, [out, x, y, z]) do
    ...>   permuteo([x, y, z], [2, 1, 1])
    ...>   eq(out, [x, y, z])
    ...> end |> Enum.sort
    [[1, 1, 2], [1, 2, 1], [2, 1, 1]]
  """
  def permuteo(lhs, rhs) do
    conde do
      [eq(lhs, []), eq(rhs, [])]
      [fresh([h, t, res]) do
        eq([h | t], lhs)
        rember_firsto(h, rhs, res)
        permuteo(t, res)
      end]
    end
  end
end
