import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

-- d/dt (1/t) = -1/t^2 as long as t ≠ 0.
-- Actually, even at t=0 with Lean's conventions: both sides are 0.
-- But we probably shouldn't try to prove that.
example (t : ℝ) (ht : t ≠ 0) : deriv (λ t : ℝ ↦ t ^ (-(1:ℝ))) t
              = (-(1:ℝ)) * t ^(-(2:ℝ)) := by
  let Q := @deriv_rpow_const id t (-1) differentiableAt_id
    (by left;exact ht)
  simp at *
  show deriv (fun t ↦ (id t) ^ (-1)) t = -t ^ (-2)
  rw [Q]
  simp
  ring_nf

def sdfg : ℕ → ℕ
| 0 => 0
| Nat.succ k => k

#check (⊤ : EReal)
#check (-⊤ : EReal)
example : (⊤ : EReal) ≠ (-⊤ : EReal) := ne_of_beq_false rfl
