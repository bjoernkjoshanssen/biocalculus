import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

example (x:ℝ) (h : x ≠ 0) : @DifferentiableAt ℝ _ ℝ _ _ ℝ _ _ Real.sqrt x := by
  have : Real.sqrt = (λ x : ℝ ↦ x^((1:ℝ)/2)) := by
    ext x
    exact Real.sqrt_eq_rpow x
  rw [this]
  exact Real.differentiableAt_rpow_const_of_ne (1/2) h
