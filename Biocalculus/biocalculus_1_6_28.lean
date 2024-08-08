import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals

def c : ℚ := 2.5
def x₀ : ℚ := 0.5

def x (t:ℕ) : ℚ := match t with
|0 => x₀
|Nat.succ n => c * (x n) * (1 - x n)

#eval (λ i : Fin 11 ↦ (x i : Float))
