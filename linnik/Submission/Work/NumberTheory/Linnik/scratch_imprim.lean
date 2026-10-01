import Mathlib

open DirichletCharacter Filter
open scoped Topology

set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

/-- The finite product `∏_{p ∣ N} (1 - χ*(p) p^{-s})` relating `L(s,χ)` to the L-function of the
primitive character `χ*` inducing `χ`.  (The factors with `p ∣ χ.conductor` are `1`, since
`χ*(p) = 0` there.) -/
noncomputable def imprimitiveProduct {N : ℕ} (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  ∏ p ∈ N.primeFactors, fun s => (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s))

theorem imprimitiveProduct_differentiable {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Differentiable ℂ (imprimitiveProduct χ) := by
  refine Differentiable.finsetProd (u := N.primeFactors)
    (f := fun p : ℕ => fun s : ℂ =>
      1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) (fun p hp => ?_)
  have hp' : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp'.ne_zero
  have hmul : Differentiable ℂ (fun s : ℂ =>
      χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) :=
    (differentiable_const (χ.primitiveCharacter (p : ZMod χ.conductor))).mul
      (differentiable_neg.const_cpow (Or.inl hpc))
  exact (differentiable_const (1:ℂ)).sub hmul

theorem imprimitiveProduct_apply {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) :
    imprimitiveProduct χ s = ∏ p ∈ N.primeFactors,
      (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) := by
  simp only [imprimitiveProduct, Finset.prod_apply]

/-- `L(s,χ) = L(s,χ*) · ∏_{p ∣ N} (1 - χ*(p) p^{-s})` for `1 < re s`. -/
lemma LSeries_primitiveCharacter_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n => χ ↑n) s =
      LSeries (fun n => χ.primitiveCharacter ↑n) s * imprimitiveProduct χ s := by
  have h := DirichletCharacter.LSeries_changeLevel (M := χ.conductor) (N := N)
    χ.conductor_dvd_level χ.primitiveCharacter hs
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  simpa [imprimitiveProduct_apply] using h

/-- The same identity for the entire `LFunction`. -/
theorem LFunction_eq_primitiveCharacter_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    [NeZero χ.conductor] (hχ : χ ≠ 1) :
    LFunction χ = fun s => LFunction χ.primitiveCharacter s * imprimitiveProduct χ s := by
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  refine AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := 2)
      (f := LFunction χ)
      (g := fun s => LFunction χ.primitiveCharacter s * imprimitiveProduct χ s) ?_ ?_ ?_
  · exact fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  · intro z _
    exact ((DirichletCharacter.differentiable_LFunction hχ').analyticAt z).mul
      ((imprimitiveProduct_differentiable χ).analyticAt z)
  · have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2:ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hmem] with z hz
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz,
      LSeries_primitiveCharacter_eq χ hz,
      DirichletCharacter.LFunction_eq_LSeries χ.primitiveCharacter hz]

end Commons.NumberTheory.DirichletCharacter
