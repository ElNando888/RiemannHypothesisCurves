import Mathlib

lemma natCast_le_div (a b n : ℕ) (h : a ≤ b / n) :
    (a : ℝ) ≤ (b : ℝ) / n := by
  have h1 : (a : ℝ) ≤ ((b / n : ℕ) : ℝ) := by exact_mod_cast h
  have h2 : ((b / n : ℕ) : ℝ) ≤ (b : ℝ) / n := by
    simpa using (Nat.cast_div_le (α := ℝ) (m := b) (n := n))
  exact le_trans h1 h2

