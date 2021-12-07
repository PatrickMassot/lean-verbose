import data.real.basic
import verbose_tactics

example (P Q R : Prop) (hRP : R → P) (hR : R) (hQ : Q) : P :=
begin
  fail_if_success { We conclude by hRP applied to hQ },
  We conclude by hRP applied to hR,
end

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 :=
begin
  We conclude by h applied to _,
end

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 :=
begin
  We conclude by h,
end
    
    
example {a b : ℕ}: a + b = b + a :=
begin
  We compute,
end 

example {a b : ℕ} (h : a + b - a = 0) : b = 0 :=
begin
  We compute at h,
  We conclude by h,
end 

variables k : nat

example (h : true) : true :=
begin
  We conclude by h,
end

example (h : ∀ n : ℕ, true) : true :=
begin
  We conclude by h applied to 0,
end

example (h : true → true) : true :=
begin
  We apply h,
  trivial,
end

example (h : ∀ n k : ℕ, true) : true :=
begin
  We conclude by h applied to [0, 1],
end

example (a b : ℕ) (h : a < b) : a ≤ b :=
begin
  We conclude by h,
end

example (a b c : ℕ) (h : a < b ∧ a < c) : a ≤ b :=
begin
  We conclude by h,
end

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c :=
begin
  We combine [h, h'],
end

example (a b c : ℤ) (h : a = b + c) (h' : b - a = c) : c = 0 :=
begin
  We combine [h, h'],
end

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c ∧ a+b ≤ a+c) : a ≤ c :=
begin
  We combine [h, h'],
end

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c :=
begin
  We replace ← h,
  We conclude by h',
end

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c :=
begin
  We replace h at h',
  We conclude by h',
end

example (f : ℕ → ℕ) (n : ℕ) (h : n > 0 → f n = 0) (hn : n > 0): f n = 0 :=
begin
  We replace h,
  exact hn
end

example (f : ℕ → ℕ) (n : ℕ) (h : ∀ n > 0, f n = 0) : f 1 = 0 :=
begin
  We replace h,
  norm_num
end

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c :=
begin
  success_if_fail { We replace h at h' which becomes a = c },
  We replace h at h' which becomes b = c,
  We conclude by h',
end

example (a b c : ℕ) (h : a = b) (h' : a = c) : a = c :=
begin
  We replace h everywhere,
  We conclude by h',
end

example (P Q R : Prop) (h : P → Q) (h' : P) : Q :=
begin
  We apply h to h',
  We conclude by h',
end

example (P Q R : Prop) (h : P → Q → R) (hP : P) (hQ : Q) : R :=
begin
  We conclude by h applied to [hP, hQ],
end

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b :=
begin
  We apply f to h,
  We conclude by h,
end

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 :=
begin
  We apply h to 0,
  We conclude by h
end

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 :=
begin
  We contrapose,
  intro h,
  use x/2,
  split,
   We conclude by h, -- linarith
  We conclude by h, -- linarith
end

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by We conclude by h
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by We conclude by h
example (ε : ℝ) (h : ε > 0) : ε ≥ -1 := by We conclude by h
example (ε : ℝ) (h : ε > 0) : ε/2 ≥ -3 := by We conclude by h

example (x : ℝ) (h : x = 3) : 2*x = 6 := by We conclude by h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 :=
begin
  We contrapose simply,
  intro h,
  We push the negation,
  We push the negation at h,
  use x/2,
  split,
   We conclude by h, -- linarith
  We conclude by h, -- linarith
end

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 :=
begin
  We contrapose simply,
  intro h,
  success_if_fail { We push the negation which becomes 0 < x },
  We push the negation,
  success_if_fail { We push the negation at h which becomes ∃ (ε : ℝ), ε > 0 ∧ ε < x },
  We push the negation at h which becomes 0 < x,
  use x/2,
  split,
   We conclude by h, -- linarith
  We conclude by h, -- linarith
end

example : (∀ n : ℕ, false) → 0 = 1 :=
begin
  We contrapose,
  We compute,
end

example (P Q : Prop) (h : P ∨ Q) : true :=
begin
  We discuss using h,
  all_goals { intro, trivial }
end

example (P : Prop) (hP₁ : P → true) (hP₂ : ¬ P → true): true :=
begin
  We discuss depending on P,
  intro h,
  exact hP₁ h,
  intro h,
  exact hP₂ h,
end

def f (n : ℕ) := 2*n

example : f 2 = 4 :=
begin
  We unfold f,
  refl,
end

example (h : f 2 = 4) : true → true :=
begin
  We unfold f at h,
  guard_hyp_strict h : 2*2 = 4,
  exact id
end

example (h : f 2 = 4) : true → true :=
begin
  success_if_fail { We unfold f at h which becomes 2*2 = 5 },
  We unfold f at h which becomes 2*2 = 4,
  exact id
end

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : true :=
begin
  We rename n to p at h,
  We rename k to l at h,
  guard_hyp_strict h : ∀ p, ∃ l, P p l,
  trivial
end

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : true :=
begin
  We rename n to p at h which becomes ∀ p, ∃ k, P p k,
  success_if_fail { We rename k to l at h which becomes ∀ p, ∃ j, P p j },
  We rename k to l at h which becomes ∀ p, ∃ l, P p l,
  trivial
end

example (P : ℕ → ℕ → Prop) : (∀ n : ℕ, ∃ k, P n k) ∨ true :=
begin
  We rename n to p,
  We rename k to l,
  guard_target_strict (∀ p, ∃ l, P p l) ∨ true,
  right,
  trivial
end

example (a b c : ℕ) : true :=
begin
  We forget a,
  We forget b c,
  trivial
end

example (h : 1 + 1 = 2) : true :=
begin
  success_if_fail { We reformulate h to 2 = 3 },
  We reformulate h to 2 = 2,
  trivial,
end