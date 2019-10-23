# ExSMT

An Elixir binding for the [Z3 theorem prover](https://github.com/Z3Prover/z3),
using port-program IPC (i.e., no NIF compilation necessary; `z3` is launched as
a managed child process and communicated with over a pipe.)

## Installation

Add `ex_smt` to your list of dependencies in `mix.exs`:

```elixir
def deps, do: [
  {:ex_smt, "~> 0.1.0"}
]
```

Docs can be found at [https://hexdocs.pm/ex_smt](https://hexdocs.pm/ex_smt).

## Usage

```elixir
iex> a = ExSMT.env_var(:a)
iex> b = ExSMT.env_var(:b)
iex> q = ExSMT.expr(:conj,
...>   ExSMT.expr(:>, a, 5),
...>   ExSMT.expr(:<, a, 10),
...>   ExSMT.expr(:=, b, 7)
...> )
((< $A 10) ∧ (> $A 5) ∧ (= $B 7))

iex> ExSMT.solve(q)
{:sat, ((= $A 6) ∧ (= $B 7))}
```

#### A Cute Trick

For better IEx readability of ExSMT expressions, add the following to your
`~/.iex.exs`:

```elixir
new_colors =
  Keyword.fetch!(IEx.inspect_opts(), :syntax_colors)
  |> Keyword.delete(:reset)
  |> Keyword.merge(
    identifier_def: :red,
    identifier_ref: :blue,
    environment_ref: :magenta,
    hidden: :white,
    operator: :red,
  )

IEx.configure(colors: [syntax_colors: new_colors])
```
