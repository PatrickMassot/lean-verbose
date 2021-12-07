import verbose_tactics

example (P Q : (ℕ → ℕ) → Prop) (h : true ∧ ∃ u : ℕ → ℕ, P u ∧ Q u) : true :=
begin
  By h we obtain (a : true) (u : ℕ → ℕ) (b : P u) (c : Q u),
  trivial
end

example (n : ℕ) (h : ∃ k, n = 2*k) : ∃ l, n+1 = 2*l + 1 :=
begin
  By h we obtain k hk,
  use k,
  rw hk
end

example (n : ℕ) (h : ∃ k, n = 2*k) : ∃ l, n+1 = 2*l + 1 :=
begin
  By h we obtain k such that hk : n = 2*k,
  use k,
  rw hk
end

example (n : ℕ) (h : ∃ k, n = 2*k) : ∃ l, n+1 = 2*l + 1 :=
begin
  success_if_fail { 
    By h we obtain k such that (hk : 0 = 1), 
  },
  By h we obtain k such that (hk : n = 2*k),
  use k,
  rw hk
end

example (P : ℕ → Prop) (h : ∀ n, P n) : true :=
begin
  By h applied to 3 we obtain H : P 3,
  trivial
end

example (f g : ℕ → ℕ) (hf : ∀ y, ∃ x, f x = y) (hg : ∀ y, ∃ x, g x = y) : ∀ y, ∃ x, (g ∘ f) x = y :=
begin
  intro y,
  success_if_fail { By hg applied to y we obtain x such that (hx : g x = x) },
  By hg applied to y we obtain x such that (hx : g x = y),
  By hf applied to x we obtain z hz,
  use z,
  change g (f z) = y,
  rw [hz, hx],
end

example (P Q : Prop) (h : P ∧ Q)  : Q :=
begin
  By h we obtain (hP : P) (hQ : Q),
  exact hQ,
end

noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ :=
begin
  By h we choose g such that (H : ∀ (y : ℕ), f (g y) = y),
  exact g,
end

example (P Q : Prop) (h : P → Q) (h' : P) : Q :=
begin
  By h it suffices to prove that P,
  exact h',
end

example (P Q : Prop) (h : P → Q) (h' : P) : Q :=
begin
  By h it suffices to prove P,
  exact h',
end

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q :=
begin
  By h it suffices to prove [P, R],
  exact hP,
  exact hR
end

example (P Q : Prop) (h : ∀ n : ℕ, P → Q) (h' : P) : Q :=
begin
  success_if_fail { By h applied to [0, 1] it suffices to prove P },
  By h applied to 0 it suffices to prove P,
  exact h',
end

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q :=
begin
  By h it suffices to prove (1 > 0),
  norm_num,
end
