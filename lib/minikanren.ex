defmodule MiniKanren do
  defmacro __using__(:core) do
    quote do
      use    MiniKanren.Core
      import MiniKanren.Core.Functions
    end
  end
  defmacro __using__(:impure) do
    quote do
      use    MiniKanren.Core
      use    MiniKanren.Impure
      import MiniKanren.Core.Functions
      import MiniKanren.Impure.Functions
    end
  end
  defmacro __using__(_) do
    quote do: use(MiniKanren, :impure)
  end
end