defmodule MicroKanren do
  @moduledoc """
  An implementation of µKanren.
  
  
  """
  
  defmacro __using__(_) do
    quote do
      require MicroKanren
      import  MicroKanren, except: [var: 1, var?: 1, unit: 1, mzero: 0,
                                    mplus: 2, bind: 2, walk: 2, ext_s: 3,
                                    unify: 3, unify: 5]
    end
  end
  
  # Goal constructors
  @doc """
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
  def empty_state, do: {Map.new, 0}
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
  
  def walk_all(v, s) do
    case walk(v, s) do
      [h | t] -> [walk_all(h, s) | walk_all(t, s)]
      val     -> val
    end
  end
  
  # Internal wiring
  @doc """
  """
  def var(c),  do: :"_#{c}"
  
  @doc """
  """
  def var?(c), do: is_atom(c)
  
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
    [h | mplus(t, s2)]
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
    case var?(u) and Dict.get(s, u, false) do
      false -> u
      val -> walk(val, s)
    end
  end
  
  @doc """
  """
  def ext_s(x, v, s) do
    Dict.put(s, x, v)
  end
  
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
  defp unify(_, _, _, _, _), do: nil
end
