defprotocol ExSMT.Serializable do
  def serialize(t)
end

defimpl ExSMT.Serializable, for: Integer do
  def serialize(i) when is_integer(i), do:
    to_string(i)
end
