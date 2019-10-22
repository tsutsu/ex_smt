defmodule ExSMT.Variable do
  defstruct [:key, :type, :name, :i]

  def new(type, name, i \\ nil) do
    key = mangle(type, name, i)
    %__MODULE__{key: key, type: type, name: name, i: i}
  end

  defp mangle(type, name, i) do
    name_mangled = Macro.underscore(to_string(name))
    i_part = case i do
      nil -> ""
      t -> Macro.underscore(to_string(t))
    end
    "#{type}_#{name_mangled}#{i_part}"
  end
end

defimpl ExSMT.Serializable, for: ExSMT.Variable do
  def serialize(%ExSMT.Variable{key: key}) do
    to_string(key)
  end
end

defimpl Inspect, for: ExSMT.Variable do
  import Inspect.Algebra

  def inspect(%ExSMT.Variable{type: :env, name: name, i: nil}, opts) do
    name = String.upcase(to_string(name))
    color("$#{name}", :environment_ref, opts)
  end
  def inspect(%ExSMT.Variable{type: :env, name: name, i: i}, opts) do
    name = String.upcase(to_string(name))
    concat([
      color("$#{name}", :environment_ref, opts),
      color("[", :tuple, opts),
      Inspect.inspect(i, opts),
      color("]", :tuple, opts)
    ])
  end

  def inspect(%ExSMT.Variable{type: :ssa, name: pc, i: i}, opts) when is_integer(i) do
    color("%#{pc}.#{i}", :identifier_ref, opts)
  end
  def inspect(%ExSMT.Variable{name: pc, i: nil}, opts) do
    color("%#{pc}", :identifier_ref, opts)
  end
end
