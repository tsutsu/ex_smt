defmodule ExSMT.Application do
  @moduledoc false

  use Application
  def start(_type, _args) do
    children = [
      ExSMT.Solver,
    ]

    opts = [strategy: :one_for_one, name: ExSMT.Supervisor]
    Supervisor.start_link(children, opts)
  end

  def config_change(_changed, _new, _removed) do
    :ok
  end
end
