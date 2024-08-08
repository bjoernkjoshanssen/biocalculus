import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals

def is_composition {α : Type} (h : α → α) := ∃ f g : α → α, f ≠ id ∧ g ≠ id ∧ h = f ∘ g

lemma classify_bool_functions (f : Bool → Bool) :
  f = id ∨ f = not ∨ f = (λ _ ↦ false) ∨ f = (λ _ ↦ true) := by
  cases H₀ : (f true) with
  |false =>
    cases H₁ : (f false) with
    |false => right;right;left;ext b;cases b;tauto;tauto
    |true  => right;left;      ext b;cases b;tauto;tauto
  |true =>
    cases H₁ : (f false) with
    |false => left;            ext b;cases b;tauto;tauto
    |true  => right;right;right;ext b;cases b;tauto;tauto

-- Negation is irreducible:
example : ∃ h : Bool → Bool, ¬ is_composition h := by
  use (not)
  intro hc
  obtain ⟨f,g,hfg⟩ := hc
  let Q₀ := (classify_bool_functions f)
  cases Q₀ with
  |inl Q₁ => tauto
  |inr Q₁ =>
    cases Q₁ with
    |inl Q₁ =>
      subst Q₁; let Q₂ := hfg.2.2; have Q₃ := hfg.2.1
      contrapose Q₃
      simp only [ne_eq, Decidable.not_not]; ext b; simp
      let Q₄ := congrFun Q₂ b
      simp at Q₄
      exact Bool.not_inj_iff.mp Q₄.symm
    |inr Q₁ =>
    cases Q₁ with
      |inl Q₁ =>
      subst Q₁;
      let Q₃ := congrFun hfg.2.2 false
      simp at Q₃
      |inr Q₁ =>
        subst Q₁
        let Q₃ := congrFun hfg.2.2 true
        simp at Q₃

  example : is_composition (λ x : ℝ ↦ x^(1/3) / (1 + x^(1/3))) := by
    use (λ x ↦ 1/(1+x))
    use (λ x ↦ x^(1/3))
    constructor
    intro hc
    let Q := congrFun hc 0
    simp at Q
    constructor
    intro hc
    let Q := congrFun hc 2
    simp at Q
    ext
    simp
