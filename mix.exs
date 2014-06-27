defmodule ExKanren.Mixfile do
  use Mix.Project

  def project do
    [ app: :exKanren,
      version: "0.0.1",
      elixir: "~> 0.14.0",
      deps: deps ]
  end

  # Configuration for the OTP application
  def application do
    []
  end

  defp deps do
    []
  end
end
