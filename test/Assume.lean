import verbose_tactics

example : ∀ n > 0, true :=
begin
  intro n,
  success_if_fail { Assume H : n < 0 },
  success_if_fail { Assume n : n > 0 },
  Assume H : n > 0,
  trivial
end

example : ∀ n > 0, true :=
begin
  intro n,
  Assume that H : n > 0,
  trivial
end

example : ∀ n > 0, true :=
begin
  success_if_fail { Assume n },
  intro n,
  Assume H : n > 0,
  trivial
end

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q :=
begin
  Assume hP,
  Assume for contradiction hnQ,
  exact h hnQ hP,
end

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q :=
begin
  Assume hP,
  Assume for contradiction hnQ : ¬ Q,
  exact h hnQ hP,
end

example (P Q : Prop) (h : Q → ¬ P) : P → ¬ Q :=
begin
  Assume hP,
  Assume for contradiction hnQ : Q,
  exact h hnQ hP,
end