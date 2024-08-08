import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals

def c : ℝ := 2
def x₀ : ℝ := 0.2

noncomputable def x : ℕ → ℝ := λ n ↦ match n with
|0 => x₀
|Nat.succ t => c * (x t) * (Real.exp ( - (x t)))

-- We show that ln(2) is the limit:

lemma one (r : ℝ) : Real.exp (-r) = 1/(Real.exp r) := by
  refine eq_one_div_of_mul_eq_one_left ?h
  have : Real.exp r * Real.exp (-r) = Real.exp (r + (-r)) := by exact Eq.symm (Real.exp_add r (-r))
  rw [mul_comm,this]
  simp

lemma two (r : ℝ) (h : r = - Real.log (1/c)) : 1 = c * Real.exp (-r) := by
    subst h
    simp
    rw [one]
    rw [Real.exp_log]
    show 1 = 2 * (1/2)
    simp
    show 0 < 2
    simp

lemma three (r : ℝ) (h : r = Real.log (c)) : 1 = c * Real.exp (-r) := by
  subst h
  rw [one,Real.exp_log]
  show 1 = 2 * (1/2)
  simp
  show 0 < 2
  simp
