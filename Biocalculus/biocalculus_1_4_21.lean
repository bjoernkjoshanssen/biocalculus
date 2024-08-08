import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals

--f(x)=C b^x goes through (1,6) and (3,24)
-- We need to assume b>0 (as the book also does) or there would also be the solution
-- b=-2, C=-3.
example (b C : ℝ) (h : b > 0) (h₀ : C * b^1 = 6) (h₁ : C * b^3 = 24) : b = 2 ∧ C = 3 := by
  have h₂: (C * b^1) * b^2 = 24 := by
    rw [← h₁]
    simp only [pow_one]
    ring
  rw [h₀] at h₂
  have : (24:ℝ) = 6 * 4 := by ring_nf
  rw [this] at h₂
  have : b^2 = 4 := by
    field_simp at h₂
    tauto
  have : b^2 = 2^2 := by
    rw [this]
    ring
  have : b = 2 ∨ b = -2 := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  cases this
  constructor
  · tauto

  · subst ‹b=2›
    simp at h₀
    have : C * 2 = 3 * 2 := by
      rw [h₀]
      ring
    field_simp at this
    tauto

  exfalso
  subst ‹b=-2›
  contrapose h
  simp
