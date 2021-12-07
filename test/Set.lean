import verbose_tactics

example (a b : ℕ) : ℕ :=
begin
  Set n := max a b,
  exact n,
end
