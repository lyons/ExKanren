defmodule MiniKanren.CLP.Tree do
  @moduledoc """
  Provides the tree disequality operator `neq`, and hooks for using CLP(Tree)
  in miniKanren.

  `use MiniKanren.CLP.Tree` to import the disequality operator.
  `use MiniKanren.CLP.Tree, :hooks` to set the hooks.
  """

  alias  MiniKanren, as: MK
  import MiniKanren, except: [process_log: 2, enforce_constraints: 1, reify_constraints: 2]

  defmacro __using__(:hooks) do
    quote do
      Process.put(:process_log, &MiniKanren.CLP.Tree.process_log/2)
      Process.put(:enforce_constraints, &MiniKanren.CLP.Tree.enforce_constraints/1)
      Process.put(:reify_constraints, &MiniKanren.CLP.Tree.reify_constraints/2)
    end
  end
  defmacro __using__(_) do
    quote do
      import MiniKanren.CLP.Tree, only: [neq: 2]
    end
  end

  @spec process_log(MK.unification_log, MK.constraint_store) :: MK.goal
  def process_log(log, cons) do
    recover_vars(log)
    |> run_constraints(cons)
  end

  @spec enforce_constraints(any) :: MK.goal
  def enforce_constraints(_), do: &MK.unit/1

  @spec reify_constraints(MK.logic_value, MK.list_substitution) :: any
  def reify_constraints(result_term, reified_names) do
    fn _pkg = {_subs, cons, _doms, _counter} ->
      # Reify variable names in constraint operands
      reified_constraints = Enum.map(cons, fn c -> constraint_operands(c)
                                                   |> walk_all(reified_names) end)
      # Any constraint with an unreified variable is irrelevant
      meaningful_constraints = Enum.reject(reified_constraints, &any_var?/1)
      case meaningful_constraints do
        [] -> result_term
        _  -> [result_term, :- | {:neq, meaningful_constraints}]
      end
    end
  end

  @spec neq(MK.logic_value, MK.logic_value) :: MK.goal
  @doc """
  `neq` ensures two logic terms will never unify.

  ## Examples:

    iex> use MiniKanren
    iex> use MiniKanren.CLP.Tree
    iex> use MiniKanren.CLP.Tree, :hooks
    iex> run_all([out]) do
    ...>   neq(out, 1)
    ...>   membero(out, [1, 2, 3])
    ...>   neq(out, 3)
    ...> end
    [2]
  """
  def neq(u, v) do
    fn pkg = {subs, _cons, _doms, _counter} ->
      case unify(u, v, subs) do
        nil        -> unit(pkg)
        {_, log} -> neq_c(log).(pkg)
      end
    end
  end

  @spec neq_c(MK.unification_log) :: MK.goal
  def neq_c(log) do
    fn pkg = {subs, _cons, _doms, _counter} ->
      case unify_list(log, subs) do
        nil         -> unit(pkg)
        {^subs, []} -> mzero
        {_, log}  -> normalise_store(log, pkg) |> unit
      end
    end
  end

  @spec normalise_store(MK.unification_log, MK.package) :: MK.package
  def normalise_store(log, pkg = {_, cons, _, _}) do
    normalise_store_loop(cons, [], pkg, log)
  end

  def normalise_store_loop([c | t], cons, pkg, log) do
    case constraint_operator(c) == :neq_c do
      true  ->
        p = constraint_operands(c)
        cond do
          subsumes?(p, log) -> pkg
          subsumes?(log, p) -> normalise_store_loop(t, cons, pkg, log)
          true -> normalise_store_loop(t, [c | cons], pkg, log)
        end
      false ->
        normalise_store_loop(t, [c | cons], pkg, log)
    end
  end
  def normalise_store_loop([], cons, {subs, _, doms, counter}, log) do
    cons = constraint(neq_c(log), :neq_c, log) |> extend_constraints(cons)
    {subs, cons, doms, counter}
  end
end
