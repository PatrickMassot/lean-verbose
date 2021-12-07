import verbose_tactics

example : 1 + 1 = 2 :=
begin
  Let's prove that 2 = 2,
  refl
end 

variables k : nat

example : ∃ k : ℕ, 4 = 2*k :=
begin
  Let's prove that 2 works,
end

example : ∃ k : ℕ, 4 = 2*k :=
begin
  Let's prove that 2 works : 4 = 2*2,
end

example : true ∧ true :=
begin
  Let's prove true,
  all_goals {trivial}
end

example (P Q : Prop) (h : P) : P ∨ Q :=
begin
  Let's prove that P,
  exact h
end

example (P Q : Prop) (h : Q) : P ∨ Q :=
begin
  Let's prove that Q,
  exact h
end

example : 0 = 0 ∧ 1 = 1 :=
begin
  Let's prove that 0 = 0,
  trivial,
  Let's prove that 1 = 1,
  trivial
end
example : 0 = 0 ∧ 1 = 1 :=
begin
  Let's prove that 0 = 0,
  trivial,
  Let's prove that 1 = 1,
  trivial
end

example : true ↔ true :=
begin
  Let's prove that true → true,
  all_goals { exact id },
end

example (h : false) : 2 = 1 :=
begin
  Let's prove it's contradictory,
  exact h
end

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 3 :=
begin
  success_if_fail { Let's prove by induction H : true },
  Let's prove by induction H : ∀ n, P n,
  exact h₀,
  exact h,
end

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : true :=
begin
  Let's prove by induction H : ∀ k, P k,
  exacts [h₀, h, trivial],
end

example : true :=
begin
  Let's prove by induction H : ∀ l, l < l + 1,
  dec_trivial,
  intro l,
  intros hl,
  linarith,
  trivial
end

example : true :=
begin
  success_if_fail { Let's prove by induction H : true },
  success_if_fail { Let's prove by induction H : ∀ n : ℤ, true },
  trivial
end