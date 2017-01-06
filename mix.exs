defmodule ExKanren.Mixfile do
  use Mix.Project

  def project do
    [ app: :exKanren,
      version: "0.0.3-dev",
      elixir: "~> 1.3 or ~> 1.4",
      deps: deps() ]
  end

  # Configuration for the OTP application
  def application do
    []
  end

  defp deps do
    []
  end
end
