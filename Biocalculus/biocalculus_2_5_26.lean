import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

example : Continuous (λ x : ℝ ↦ Real.sin (Real.cos (Real.sin x))) := by
  show Continuous (Real.sin ∘ (Real.cos ∘ Real.sin))
  apply Continuous.comp
  exact Real.continuous_sin
  apply Continuous.comp
  exact Real.continuous_cos
  exact Real.continuous_sin
