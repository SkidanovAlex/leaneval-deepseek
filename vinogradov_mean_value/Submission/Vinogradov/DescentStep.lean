/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.DecouplingClass
import Submission.Vinogradov.BilinearReduction

/-!
# The class transfer and the change of variables for the `L^p` norm

Two auxiliary tools for the *one-step* of the scale descent (GLYZ §3.3):

* `exists_isFourierRep_preimage`: the class transfer for an arbitrary invertible adjoint pair
  `(Linv, M)`.  If `f` lies in the class over the affine image `c + Linv '' U`, then `f` is the
  unimodular phase `e(⟪·,c⟫)` times `g ∘ M` for some `g` in the class over `U`.  The proof
  produces the lifted frequency datum `Γ' u = Λ⁻¹(Γ u - c)` (measurable, because `Λ⁻¹` is a
  continuous linear map and `Linv` is *injective* — this is where the torsion of the curve
  enters) and then applies `DecouplingClass.repFun_linear_rescale`.
* `lpNorm_comp_linearMap` / `lpNorm_phase_comp_linearMap`: the `L^p` change of variables
  `‖g ∘ M‖_p = |det M|^{-1/p}‖g‖_p` (and its phase-twisted form), from the Haar-measure identity
  `Measure.map_linearMap_addHaar_eq_smul_addHaar`.

Together with `exists_isFourierRep_preimage` this shows that a decoupling inequality is invariant
under the straightening rescaling: the unimodular phase does not change the `L^p` norm, and the
`|det M|^{-1/p}` factors of the two sides cancel.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Submission.Vinogradov

/-! ## 1. The class transfer for an arbitrary invertible adjoint pair -/

open scoped Classical in
/-- **The class transfer.**  If `Linv` is an injective linear map with transpose `M`, and `f` lies
in the class `𝒞(c + Linv '' U)`, then `f` is the unimodular phase `e(⟪·,c⟫)` times the composition
of `M` with an element `g` of the class `𝒞(U)`. -/
theorem exists_isFourierRep_preimage (k : ℕ) {U : Set (E k)} (Linv M : E k →ₗ[ℝ] E k)
    (hM : ∀ x y : E k, ⟪M x, y⟫ = ⟪x, Linv y⟫) (hLinv : Function.Injective Linv) (c : E k)
    {f : E k → ℂ} (hf : IsFourierRep k ((fun ξ => c + Linv ξ) '' U) f) :
    ∃ g : E k → ℂ, IsFourierRep k U g ∧ f = fun x => chat k x c * g (M x) := by
  classical
  obtain ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, hfrep⟩ := hf
  letI : MeasurableSpace ι := m
  have hsurj : Function.Surjective Linv :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (rfl : Module.finrank ℝ (E k)
      = Module.finrank ℝ (E k))).mp hLinv
  obtain ⟨Λe, hΛe⟩ : ∃ Λe : E k ≃ₗ[ℝ] E k, ∀ x : E k, Λe x = Linv x :=
    ⟨LinearEquiv.ofBijective Linv ⟨hLinv, hsurj⟩, fun x => rfl⟩
  set Γ' : ι → E k := fun u => Λe.symm (Γ u - c) with hΓ'def
  have hΓ'm : Measurable Γ' :=
    (Λe.symm.toLinearMap.continuous_of_finiteDimensional.measurable).comp
      (hΓ.sub measurable_const)
  have hΓeq : Γ = fun u => c + Linv (Γ' u) := by
    funext u
    have h1 : Linv (Λe.symm (Γ u - c)) = Γ u - c := by
      rw [← hΛe (Λe.symm (Γ u - c))]
      exact LinearEquiv.apply_symm_apply Λe (Γ u - c)
    rw [hΓ'def]
    simp only
    rw [h1]
    abel
  refine ⟨repFun k Γ' ν φ, ?_, ?_⟩
  · refine IsFourierRep.mk' hν hφ hΓ'm hmφ (fun u hu => ?_) (fun x => rfl)
    obtain ⟨ξ, hξU, hξ⟩ := hU u hu
    have hξ' : Γ u = c + Linv ξ := hξ.symm
    have h2 : Γ' u = ξ := by
      rw [hΓ'def]
      simp only
      exact Λe.symm_apply_eq.mpr (by rw [hΛe ξ, hξ']; abel)
    rw [h2]
    exact hξU
  · have hthis : repFun k (fun u => c + Linv (Γ' u)) ν φ
        = fun x => chat k x c * repFun k Γ' ν φ (M x) :=
      repFun_linear_rescale k Γ' ν φ Linv M hM c
    rw [← hΓeq] at hthis
    have hf' : f = repFun k Γ ν φ := funext fun x => (hfrep x).trans rfl
    exact hf'.trans hthis

/-! ## 2. The change of variables for the `L^p` norm -/

/-- **The `L^p` change of variables** for an invertible linear map:
`‖g ∘ M‖_p = |det M|^{-1/p} ‖g‖_p`. -/
lemma lpNorm_comp_linearMap (k : ℕ) {p : ℝ≥0∞} (hp : p ≠ ∞) {M : E k →ₗ[ℝ] E k}
    (hM : LinearMap.det M ≠ 0) {g : E k → ℂ} (hg : AEStronglyMeasurable g volume) :
    lpNorm k p (fun x => g (M x))
      = (ENNReal.ofReal |(LinearMap.det M)⁻¹|) ^ (1 / p).toReal * lpNorm k p g := by
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (E k)) hM
  have hae : AEMeasurable M volume :=
    (LinearMap.continuous_of_finiteDimensional M).measurable.aemeasurable
  have hg' : AEStronglyMeasurable g (Measure.map M volume) := by
    rw [hmap]
    exact hg.mono_ac Measure.smul_absolutelyContinuous
  have h2 : eLpNorm (fun x : E k => g (M x)) p volume = eLpNorm g p (Measure.map M volume) :=
    (eLpNorm_map_measure hg' hae).symm
  rw [lpNorm, lpNorm, h2, hmap, eLpNorm_smul_measure_of_ne_top hp]
  rfl

/-- **The `L^p` change of variables with a unimodular phase**. -/
lemma lpNorm_phase_comp_linearMap (k : ℕ) {p : ℝ≥0∞} (hp : p ≠ ∞) {M : E k →ₗ[ℝ] E k}
    (hM : LinearMap.det M ≠ 0) (c : E k) {g : E k → ℂ} (hg : AEStronglyMeasurable g volume) :
    lpNorm k p (fun x => chat k x c * g (M x))
      = (ENNReal.ofReal |(LinearMap.det M)⁻¹|) ^ (1 / p).toReal * lpNorm k p g := by
  have hstrip : eLpNorm (fun x : E k => chat k x c * g (M x)) p volume
      = eLpNorm (fun x : E k => g (M x)) p volume := by
    rw [← eLpNorm_norm (f := fun x : E k => chat k x c * g (M x)),
      ← eLpNorm_norm (f := fun x : E k => g (M x))]
    exact eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [norm_mul, chat_norm, one_mul])
  rw [lpNorm, hstrip, ← lpNorm]
  exact lpNorm_comp_linearMap k hp hM hg

end Submission.Vinogradov
