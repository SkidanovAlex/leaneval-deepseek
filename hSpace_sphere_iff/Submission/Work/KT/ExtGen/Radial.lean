import Mathlib
import Submission.Work.KT.Defs

/-!
# `Work.KT.ExtGen.Radial` — radial normalisation of a linear equivalence

A linear equivalence `e : V ≃ₗ[ℝ] V'` between (finite-dimensional) real normed spaces induces a
homeomorphism of the unit balls `Ball V ≃ₜ Ball V'` by *radial normalisation*: `x ↦ e x` rescaled
to have the same norm as `x`.  It preserves norms, hence maps the boundary spheres onto each other.

This is the geometric input for `Work.KT.ExtGen.pairIso_of_linearEquiv` ("change of norm and
dimension").
-/

namespace Work.KT.ExtGen

open Work.KT

noncomputable section

/-! ## The radial map -/

section RadialMap

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']

/-- Radial normalisation of a linear equivalence: `e x` rescaled by `‖x‖ / ‖e x‖`, so that the
result has the same norm as `x` (and lies in the same direction as `e x`). -/
def radialMap (e : V ≃ₗ[ℝ] V') (x : V) : V' := (‖x‖ * ‖e x‖⁻¹) • e x

@[simp] lemma radialMap_zero (e : V ≃ₗ[ℝ] V') : radialMap e (0 : V) = 0 := by
  simp [radialMap]

/-- The radial map preserves norms. -/
lemma norm_radialMap (e : V ≃ₗ[ℝ] V') (x : V) : ‖radialMap e x‖ = ‖x‖ := by
  rw [radialMap, norm_smul]
  by_cases hx : e x = 0
  · have hx0 : x = 0 := e.injective (by simpa using hx)
    subst hx0; simp
  · have hnorm : ‖e x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))),
      mul_assoc, inv_mul_cancel₀ hnorm, mul_one]

/-- `radialMap e.symm` is a left inverse of `radialMap e`. -/
lemma radialMap_symm_radialMap (e : V ≃ₗ[ℝ] V') (x : V) :
    radialMap e.symm (radialMap e x) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radialMap]
  · have hex : e x ≠ 0 := fun h => hx (e.injective (by simpa using h))
    have hxn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hx
    have hexn : (‖e x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hex
    have ha : (0 : ℝ) ≤ ‖x‖ * ‖e x‖⁻¹ :=
      mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))
    rw [radialMap, radialMap, map_smul, LinearEquiv.symm_apply_apply]
    simp only [norm_smul, Real.norm_of_nonneg ha, smul_smul]
    rw [show (‖x‖ * ‖e x‖⁻¹ * ‖e x‖ * (‖x‖ * ‖e x‖⁻¹ * ‖x‖)⁻¹ * (‖x‖ * ‖e x‖⁻¹))
        = (1 : ℝ) by
      field_simp, one_smul]

/-- `radialMap e` is a left inverse of `radialMap e.symm`. -/
lemma radialMap_radialMap_symm (e : V ≃ₗ[ℝ] V') (y : V') :
    radialMap e (radialMap e.symm y) = y := by
  simpa using radialMap_symm_radialMap (e := e.symm) y

/-- The radial map is continuous (continuity at `0` from `‖radialMap e x‖ = ‖x‖`, elsewhere from
continuity of `x ↦ ‖e x‖⁻¹`). -/
lemma continuous_radialMap [FiniteDimensional ℝ V] (e : V ≃ₗ[ℝ] V') :
    Continuous (radialMap e) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have h0 : radialMap e 0 = 0 := by simp [radialMap]
    simp only [h0, sub_zero]
    simpa only [norm_radialMap, norm_zero] using (continuous_norm.tendsto (0 : V))
  · have hex : e x ≠ 0 := fun h => hx (e.injective (by simpa using h))
    have hnorm : ‖e x‖ ≠ 0 := norm_ne_zero_iff.mpr hex
    have h1 : ContinuousAt (fun y : V => ‖y‖) x := continuous_norm.continuousAt
    have h2 : ContinuousAt (fun y : V => (‖e y‖)⁻¹) x :=
      ((continuous_norm.comp e.continuous_of_finiteDimensional).continuousAt).inv₀ hnorm
    have h3 : ContinuousAt (fun y : V => (‖y‖ * (‖e y‖)⁻¹)) x := h1.mul h2
    have h4 : ContinuousAt (fun y : V => e y) x := e.continuous_of_finiteDimensional.continuousAt
    exact h3.smul h4

end RadialMap

/-! ## The induced maps of unit balls -/

section Ball

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']

/-- The radial normalisation induces a map of unit balls. -/
def phiBall (e : V ≃ₗ[ℝ] V') (x : Ball V) : Ball V' :=
  ⟨radialMap e (x : V), by
    rw [mem_closedBall_zero_iff, norm_radialMap]; exact mem_closedBall_zero_iff.mp x.2⟩

/-- The inverse map of unit balls, given by radial normalisation of `e.symm`. -/
def psiBall (e : V ≃ₗ[ℝ] V') (y : Ball V') : Ball V :=
  ⟨radialMap e.symm (y : V'), by
    rw [mem_closedBall_zero_iff, norm_radialMap]; exact mem_closedBall_zero_iff.mp y.2⟩

@[simp] lemma coe_phiBall (e : V ≃ₗ[ℝ] V') (x : Ball V) :
    (phiBall e x : V') = radialMap e (x : V) := rfl

@[simp] lemma coe_psiBall (e : V ≃ₗ[ℝ] V') (y : Ball V') :
    (psiBall e y : V) = radialMap e.symm (y : V') := rfl

/-- `phiBall` preserves the norm. -/
@[simp] lemma phiBall_norm (e : V ≃ₗ[ℝ] V') (x : Ball V) :
    ‖(phiBall e x : V')‖ = ‖(x : V)‖ := by
  rw [coe_phiBall, norm_radialMap]

/-- `psiBall` preserves the norm. -/
@[simp] lemma psiBall_norm (e : V ≃ₗ[ℝ] V') (y : Ball V') :
    ‖(psiBall e y : V)‖ = ‖(y : V')‖ := by
  rw [coe_psiBall, norm_radialMap]

/-- `phiBall` maps the boundary to the boundary. -/
lemma phiBall_mem_bdry (e : V ≃ₗ[ℝ] V') {x : Ball V} (hx : x ∈ bdry V) :
    phiBall e x ∈ bdry V' := by
  change ‖(phiBall e x : V')‖ = 1
  rw [phiBall_norm]; exact hx

/-- `psiBall` maps the boundary to the boundary. -/
lemma psiBall_mem_bdry (e : V ≃ₗ[ℝ] V') {y : Ball V'} (hy : y ∈ bdry V') :
    psiBall e y ∈ bdry V := by
  change ‖(psiBall e y : V)‖ = 1
  rw [psiBall_norm]; exact hy

/-- `psiBall` is a left inverse of `phiBall`. -/
@[simp] lemma psiBall_phiBall (e : V ≃ₗ[ℝ] V') (x : Ball V) :
    psiBall e (phiBall e x) = x := by
  apply Subtype.ext
  show radialMap e.symm (radialMap e (x : V)) = (x : V)
  exact radialMap_symm_radialMap e (x : V)

/-- `phiBall` is a left inverse of `psiBall`. -/
@[simp] lemma phiBall_psiBall (e : V ≃ₗ[ℝ] V') (y : Ball V') :
    phiBall e (psiBall e y) = y := by
  apply Subtype.ext
  show radialMap e (radialMap e.symm (y : V')) = (y : V')
  exact radialMap_radialMap_symm e (y : V')

/-- `phiBall` is continuous. -/
lemma continuous_phiBall (e : V ≃ₗ[ℝ] V') : Continuous (phiBall e) := by
  apply Continuous.subtype_mk
  exact (continuous_radialMap e).comp continuous_subtype_val

/-- `psiBall` is continuous. -/
lemma continuous_psiBall (e : V ≃ₗ[ℝ] V') : Continuous (psiBall e) := by
  apply Continuous.subtype_mk
  exact (continuous_radialMap e.symm).comp continuous_subtype_val

/-- `phiBall` as a continuous map. -/
def phiBallCM (e : V ≃ₗ[ℝ] V') : C(Ball V, Ball V') := ⟨phiBall e, continuous_phiBall e⟩

/-- `psiBall` as a continuous map. -/
def psiBallCM (e : V ≃ₗ[ℝ] V') : C(Ball V', Ball V) := ⟨psiBall e, continuous_psiBall e⟩

@[simp] lemma phiBallCM_apply (e : V ≃ₗ[ℝ] V') (x : Ball V) : phiBallCM e x = phiBall e x := rfl
@[simp] lemma psiBallCM_apply (e : V ≃ₗ[ℝ] V') (y : Ball V') : psiBallCM e y = psiBall e y := rfl

end Ball

end

end Work.KT.ExtGen
