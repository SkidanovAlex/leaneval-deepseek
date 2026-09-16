import Mathlib.RingTheory.Valuation.IsTrivialOn

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Valuation

theorem v_eval2_eq {F K : Type*} [Field F] [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) (f : F →+* K) {θ : K}
    (hf : ∀ c : F, c ≠ 0 → v (f c) = 1) (hθ : 1 < v θ) (p : Polynomial F) (hp : p ≠ 0) :
    v (p.eval₂ f θ) = (v θ) ^ p.natDegree := by
  letI : Algebra F K := f.toAlgebra
  haveI : v.IsTrivialOn F := ⟨fun a ha => hf a ha⟩
  have h := Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
      (v := v) θ hθ hp
  simpa only [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using h

end Commons.RingTheory.Valuation