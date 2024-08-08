import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals

def a : ℕ → ℚ := λ n ↦ 3*n + 2

#eval (λ i : Fin 5 ↦ a i.1.succ)
