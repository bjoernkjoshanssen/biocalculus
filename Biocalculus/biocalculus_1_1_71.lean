import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals

def even_function (f: ℝ → ℝ) := ∀ x, f (-x) = f x

example : even_function (λ x ↦ 1 + 3*x^2 - x^4) := by
  intro x
  simp only [even_two, Even.neg_pow, sub_right_inj]
  refine Even.neg_pow ?_ x
  use 2
