defmodule ExSMT.MixProject do
  use Mix.Project

  def project, do: [
    app: :ex_smt,
    version: "0.1.0",
    elixir: "~> 1.9",
    start_permanent: Mix.env() == :prod,
    deps: deps()
  ]

  def application, do: [
    mod: {ExSMT.Application, []},
    extra_applications: [:logger]
  ]

  defp deps, do: [
    {:decimal, "~> 1.8"},
    {:nimble_parsec, "~> 0.5.1"},
    {:porcelain, github: "walkr/porcelain"},
  ]
end
