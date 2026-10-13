/-
  Work.WilE2 — setup lemmas for the compact level-curve flow
  (`Work.WilE2.compact_level_curve_flow`).

  These are elementary facts about `fderiv` used to feed the implicit function
  theorem: if at `z` the `m-1` component gradients of `V : ℝᵐ → ℝ^{m-1}` are
  linearly independent, then `fderiv ℝ V z` is surjective.
-/
import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace Work.WilE2

/-- A linear functional on `Fin n → ℝ` is determined by its values on the standard basis. -/
lemma dual_pi_apply {n : ℕ} (c : Module.Dual ℝ (Fin n → ℝ)) (f : Fin n → ℝ) :
    c f = ∑ i, c (Pi.single i (1:ℝ)) * f i := by
  conv_lhs => rw [← Finset.univ_sum_single f]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show Pi.single i (f i) = f i • Pi.single i (1:ℝ) from by
      ext j; by_cases h : j = i <;> simp [Pi.single_eq_same, Pi.single_eq_of_ne, h]]
  rw [map_smul]
  simp [smul_eq_mul, mul_comm]

/-- If a finite family of continuous linear functionals on `ℝᵐ` is linearly independent,
the evaluation map `x ↦ (g i x)` is surjective. -/
lemma pi_surjective {m k : ℕ} (g : Fin k → ((Fin m → ℝ) →L[ℝ] ℝ))
    (hgrad : LinearIndependent ℝ g) : Function.Surjective (ContinuousLinearMap.pi g) := by
  set T : (Fin m → ℝ) →ₗ[ℝ] (Fin k → ℝ) := LinearMap.pi (fun i => (g i).toLinearMap) with hT
  have hfun : ⇑T = ⇑(ContinuousLinearMap.pi g) := by funext x i; rfl
  have hinj : Function.Injective T.dualMap := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have hcx : ∀ x, c (fun i => g i x) = 0 := by
      intro x
      have h1 : T.dualMap c x = 0 := by rw [hc]; rfl
      rw [LinearMap.dualMap_apply] at h1
      rw [hT] at h1
      exact h1
    have hsum : ∑ i, c (Pi.single i (1:ℝ)) • g i = 0 := by
      ext x
      simp only [sum_apply, smul_apply, zero_apply, smul_eq_mul]
      rw [← dual_pi_apply c (fun i => g i x), hcx x]
    have hcoef := (Fintype.linearIndependent_iff.mp hgrad) (fun i => c (Pi.single i (1:ℝ))) hsum
    apply LinearMap.ext
    intro y
    rw [dual_pi_apply]
    simp [hcoef]
  have hTsurj : Function.Surjective T := LinearMap.dualMap_injective_iff.mp hinj
  intro y
  obtain ⟨x, hx⟩ := hTsurj y
  exact ⟨x, by rw [← hfun]; exact hx⟩

/-- If the `m-1` component gradients of `V` at `z` are linearly independent, then
`fderiv ℝ V z` is surjective. -/
lemma fderiv_range_top {m : ℕ} (V : (Fin m → ℝ) → (Fin (m-1) → ℝ)) (hV : ContDiff ℝ 1 V)
    (z : Fin m → ℝ) (hgrad : LinearIndependent ℝ (fun i => fderiv ℝ (fun w => V w i) z)) :
    (fderiv ℝ V z).range = ⊤ := by
  have hcomp : ∀ i : Fin (m-1), HasStrictFDerivAt (fun w => V w i) (fderiv ℝ (fun w => V w i) z) z :=
    fun i => (contDiffAt_pi.mp hV.contDiffAt i).hasStrictFDerivAt (by norm_num)
  have hst : HasStrictFDerivAt V (fderiv ℝ V z) z := hV.contDiffAt.hasStrictFDerivAt (by norm_num)
  have hpi : (fderiv ℝ V z) = ContinuousLinearMap.pi (fun i => fderiv ℝ (fun w => V w i) z) := by
    have h := hasStrictFDerivAt_pi.mpr hcomp
    exact hst.hasFDerivAt.unique h.hasFDerivAt
  rw [hpi, LinearMap.range_eq_top]
  exact pi_surjective _ hgrad

end Work.WilE2
