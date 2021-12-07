import verbose_tactics

example (n : ℕ) : n + n + n = 3*n :=
begin
  Fact key : n + n = 2*n,
  by ring,
  ring,
end

example (n : ℤ) (h : 0 < n) : true :=
begin
  Fact key : 0 < 2*n by h, 
  success_if_fail { Fact key : 0 < 2*n by h }, 
  Fact keybis : 0 < 2*n by mul_pos applied to [zero_lt_two, h],
  trivial
end

example (n : ℕ) (h : 0 < n) : 0 < 2*n :=
begin
  Fact key : 0 < 2*n by h,
  exact key
end