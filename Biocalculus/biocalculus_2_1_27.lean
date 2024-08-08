import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base


noncomputable def b : Nat → ℝ := λ n ↦ match n with
|0 => 1
|Nat.succ t => (1/2) * b t + 1


lemma characterize (n : ℕ) : b n = 2 - 1/2^n := by
  induction n with
  |zero => simp;unfold b;ring
  |succ m hm => unfold b;rw [hm];ring

lemma pow_neg (x : ℝ) : (2:ℝ)^(-x) = 1/2^x := by
  refine eq_one_div_of_mul_eq_one_left ?h;
  have : 1 = (2:ℝ)^((-x) + x) := by simp
  rw [this]
  let Q := @Real.rpow_add 2 zero_lt_two (-x) x
  tauto

lemma two : ∀ ε : ℝ, 0 < ε →
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |b n - 2| ≤ ε := by

  intro ε hε
  use Nat.ceil (Real.logb 2 (1/ε));intro n hn
  rw [characterize]
  simp;ring_nf;field_simp;
  have : |(1:ℝ) / 2^n| = 1/2^n := abs_eq_self.mpr (by
    refine one_div_nonneg.mpr ?_
    refine pow_nonneg ?H n
    exact zero_le_two
  )
  rw [this]
  have h₀ : Real.logb 2 (1/ε) ≤ Nat.ceil (Real.logb 2 (1/ε)) := by
    apply Nat.le_ceil
  have h₁ : Real.logb 2 (1/ε) ≤ n := calc
                            _ ≤ _ := h₀
                            _ ≤ _ := by simp;simp at hn;tauto
  suffices 1/ε ≤ 2^n by
    refine (one_div_le hε ?hb).mp this;refine pow_pos ?hb.H n;exact zero_lt_two
  let Q := (Real.rpow_le_rpow_left_iff (one_lt_two)).mpr h₁
  simp at Q
  rw [pow_neg,Real.rpow_logb] at Q
  · tauto
  · exact zero_lt_two
  · exact Ne.symm (OfNat.one_ne_ofNat 2)
  tauto

noncomputable def a : PNat → ℝ := λ n ↦ b n.1.pred

example : ∀ ε : ℝ, 0 < ε →
  ∃ N : PNat, ∀ n : PNat, N ≤ n →
    |a n - 2| ≤ ε := by
      unfold a
      intro ε hε
      let Q := two ε hε
      obtain ⟨ N,hN⟩ := Q
      use ⟨N+1,by simp⟩
      intro n hn
      have : N ≤ n.1.pred := by
        exact Nat.le_pred_of_lt hn
      exact hN n.1.pred this
