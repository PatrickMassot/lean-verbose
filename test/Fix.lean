import verbose_tactics

example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (set.univ : set ℕ), true :=
begin
  Fix (n > 0) k (l ∈ set.univ),
  trivial
end

example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (set.univ : set ℕ), true :=
begin
  Fix n,
  success_if_fail { Fix h },
  intro hn,
  Fix k (l ∈ set.univ),
  trivial
end

example : ∀ n > 0, ∀ k : ℕ, true :=
begin
  Fix (n > 0),
  success_if_fail { Fix n },
  Fix k,
  trivial
end

example : ∀ n > 0, ∀ k : ℕ, true :=
begin
  Fix n > 0,
  success_if_fail { Fix n },
  Fix k,
  trivial
end

example (k l : ℕ) : ∀ n ≤ k + l, true :=
begin
  Fix n ≤ k + l,
  trivial,
end

example (A : set ℕ) : ∀ n ∈ A, true :=
begin
  Fix n ∈ A,
  trivial
end