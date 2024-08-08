import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

-- We only prove that Real.exp goes to ∞:
example : ∀ y : ℝ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → y ≤ Real.exp x := by
  intro y
  use Real.log y -- even if y is negative!
  intro x hx
  by_cases H : 0 < y
  · rw [← Real.exp_log H]
    exact Real.exp_le_exp.mpr hx
  · calc
    y ≤ 0 := le_of_not_lt H
    _ ≤ _ := by exact Real.exp_nonneg x


-- How to use Filter.map:
example (a : ℝ) : Set.Ioo a (a+2) ∈ Filter.map (λ x ↦ x + 1) (nhds a) := by
    unfold Filter.map
    simp;rw [nhds_def];simp
    apply Filter.mem_iInf_of_mem (Set.Ioo (a-1) (a+1))
    simp;
    apply Filter.mem_iInf_of_mem
    simp
    · intro x hx;
      simp at *
      constructor
      linarith
      linarith
    · exact isOpen_Ioo

-- This, I believe, is how you are supposed to work with limits:
example : Filter.Tendsto (λ x : ℝ ↦ x) (nhds 0) (nhds 0)  := by
  refine Metric.tendsto_nhds_nhds.mpr ?_
  intro ε hε
  use ε
  constructor
  · linarith
  · intro x hx
    tauto


-- This proves x^2 goes to ∞, but the point is hidden in ENNReal.continuous_pow
example : Filter.Tendsto (λ x : ENNReal ↦ x^2) (nhds ⊤) (nhds ⊤)  := by

  refine Continuous.tendsto' ?hf ⊤ ⊤ rfl
  exact ENNReal.continuous_pow 2

example : Filter.Tendsto (λ x : ENNReal ↦ x^2 + x) (nhds ⊤) (nhds ⊤)  := by
  refine Continuous.tendsto' ?hf ⊤ ⊤ rfl
  refine Continuous.add ?hf.a.hf.hf ?hf.a.hf.hg
  · exact ENNReal.continuous_pow 2
  · exact continuous_id'



example : Filter.Tendsto (λ x : ENNReal ↦ x - 1) (nhds ⊤) (nhds ⊤)  := by
  refine Continuous.tendsto' ?hf ⊤ ⊤ rfl
  exact ENNReal.continuous_sub_right 1
