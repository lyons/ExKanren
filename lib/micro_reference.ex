defmodule MicroKanren.Reference do
  @moduledoc """
  
  """
  
  defmacro __using__(_) do
    quote do
      require MicroKanren.Reference
      import  MicroKanren.Reference
    end
  end
  
  # Goal constructors
  def eq(u, v) do
    fn [subs | counter] ->
      case unify(u, v, subs) do
        nil -> mzero
        s   -> unit([s | counter])
      end
    end
  end
  
  def call_fresh(f) do
    fn [s | counter] ->
      f.(var(counter)).([s | (counter + 1)])
    end
  end
  
  def disj(g1, g2) do
    fn s_c -> mplus(g1.(s_c), g2.(s_c)) end
  end
  
  def conj(g1, g2) do
    fn s_c -> bind(g1.(s_c), g2) end
  end

  # Goal constructor helpers
  defmacro snooze(func) do
    quote do
      fn s_c ->
        fn -> unquote(func).(s_c) end
      end
    end
  end
    
  defmacro conj_many([fun | []]) do
    quote do: snooze(unquote(fun))
  end
  defmacro conj_many([fun | t]) do
    quote do: conj(snooze(unquote(fun)), conj_many(unquote(t)))
  end
  
  defmacro disj_many([fun | []]) do
    quote do: snooze(unquote(fun))
  end
  defmacro disj_many([fun | t]) do
    quote do: disj(snooze(unquote(fun)), disj_many(unquote(t)))
  end
  
  # Interface helpers
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
  
  # Wiring
  def var(c),  do: :"_#{c}"
  def var?(c), do: is_atom(c)
  def var_eq?(c, c), do: true
  def var_eq?(_, _), do: false
  
  def empty_state, do: [[] | 0]
  
  def unit(s_c), do: [s_c]
  def mzero, do: []
  
  def mplus([], s), do: s
  def mplus(s1, s2) when is_function(s1) do
    fn -> mplus(s2, s1.()) end
  end
  def mplus([h | t], s2) do
    [h | mplus(t, s2)]
  end
  
  def bind([], _), do: mzero
  def bind(s, g) when is_function(s) do
    fn -> bind(s.(), g) end
  end
  def bind([h | t], g) do
    mplus(g.(h), bind(t, g))
  end
  
  def walk(u, s) do
    case var?(u) and assp(fn v -> var_eq?(u, v) end, s) do
      false -> u
      [_ | t] -> walk(t, s)
    end
  end
  
  def ext_s(x, v, s) do
    [[x | v] | s]
  end
  
  def unify(t1, t2, s) do
    t1 = walk(t1, s)
    t2 = walk(t2, s)
    var_t1 = var?(t1)
    var_t2 = var?(t2)
    unify(t1, var_t1, t2, var_t2, s)
  end
  
  def unify(t, _, t, _, s), do: s
  def unify(t1, true, t2, _, s), do: ext_s(t1, t2, s)
  def unify(t1, _, t2, true, s), do: ext_s(t2, t1, s)
  def unify([h1 | t1], _, [h2 | t2], _, s) do
    case unify(h1, h2, s) do
      false -> nil
      x     -> unify(t1, t2, x)
    end
  end
  def unify(_, _, _, _, _), do: nil
  
  # Pretending we are Scheme
  def assp(_, []), do: false
  def assp(p, [[k | v] | t]) do
    case p.(k) do
      true  -> [k | v]
      false -> assp(p, t)
    end
  end
end