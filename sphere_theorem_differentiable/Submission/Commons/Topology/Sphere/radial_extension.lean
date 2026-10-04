import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Topology.GDelta.MetrizableSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The radial (conical) extension of a homeomorphism of the unit sphere

This file proves the *Alexander trick* for the unit sphere of a real inner product
space: a homeomorphism `φ` of the unit sphere `S = Metric.sphere 0 1` extends to a
homeomorphism of the closed unit ball `Metric.closedBall 0 1`, fixing the origin,
by the conical formula `Φ x = ‖x‖ • φ (x / ‖x‖)` for `x ≠ 0` and `Φ 0 = 0`.

The key points are:
* the conical extension is norm preserving, hence continuous at the origin;
* it is continuous away from the origin because there the radial projection
  `x ↦ ‖x‖⁻¹ • x` is continuous;
* the conical extension of `φ.symm` is a two-sided inverse, by the same formula.
-/

namespace Commons.Topology.Sphere

open Metric
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

/-- Radial projection of a nonzero vector onto the unit sphere of a real inner
product space. -/
def sphereProj (x : E) (hx : x ≠ 0) : Metric.sphere (0 : E) 1 :=
  ⟨(‖x‖)⁻¹ • x, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv,
      Real.norm_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

@[simp] lemma sphereProj_coe (x : E) (hx : x ≠ 0) :
    ((sphereProj x hx : Metric.sphere (0 : E) 1) : E) = (‖x‖)⁻¹ • x := rfl

/-- The conical (radial) extension of a map of the unit sphere: `x ↦ ‖x‖ • φ (x/‖x‖)`
for `x ≠ 0`, and `0 ↦ 0`. -/
def coneMap (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) : E → E := by
  classical
  exact fun x => if hx : x = 0 then 0 else ‖x‖ • ((φ (sphereProj x hx)) : E)

@[simp] lemma coneMap_zero (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    coneMap φ 0 = 0 := dif_pos rfl

lemma coneMap_of_ne (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) {x : E}
    (hx : x ≠ 0) : coneMap φ x = ‖x‖ • ((φ (sphereProj x hx)) : E) := dif_neg hx

/-- The conical extension is norm preserving. -/
lemma norm_coneMap (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) (x : E) :
    ‖coneMap φ x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [coneMap_of_ne φ hx, norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
    have hmem : ‖((φ (sphereProj x hx) : Metric.sphere (0 : E) 1) : E)‖ = 1 := by
      have h := (φ (sphereProj x hx)).2
      rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    rw [hmem, mul_one]

/-- Continuity of the conical extension away from the origin. -/
lemma continuous_coneMap_subtype (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    Continuous fun x : {x : E // x ≠ 0} => coneMap φ (x : E) := by
  have hval : Continuous fun x : {x : E // x ≠ 0} => (‖(x : E)‖)⁻¹ • (x : E) :=
    (Continuous.inv₀ (continuous_norm.comp continuous_subtype_val)
      (fun x => norm_ne_zero_iff.mpr x.2)).smul continuous_subtype_val
  have hproj : Continuous fun x : {x : E // x ≠ 0} => sphereProj (x : E) x.2 :=
    Continuous.subtype_mk hval (fun x => (sphereProj (x : E) x.2).2)
  have hφ : Continuous fun x : {x : E // x ≠ 0} =>
      ((φ (sphereProj (x : E) x.2)) : E) :=
    continuous_subtype_val.comp (φ.continuous.comp hproj)
  have hsmul : Continuous fun x : {x : E // x ≠ 0} =>
      ‖(x : E)‖ • ((φ (sphereProj (x : E) x.2)) : E) :=
    (Continuous.smul (continuous_norm.comp continuous_subtype_val) hφ).congr
      (fun _ => rfl)
  refine hsmul.congr ?_
  intro x
  exact (coneMap_of_ne φ x.2).symm

/-- Continuity of the conical extension at the origin. -/
lemma continuousAt_coneMap_zero (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    ContinuousAt (coneMap φ) 0 := by
  have hnorm : ContinuousAt (fun x : E => ‖x‖) (0 : E) := continuous_norm.continuousAt
  rw [ContinuousAt, coneMap_zero, tendsto_zero_iff_norm_tendsto_zero]
  refine Filter.Tendsto.congr'
    (Filter.Eventually.of_forall (fun x => (norm_coneMap φ x).symm)) ?_
  rw [ContinuousAt] at hnorm
  simpa using hnorm

/-- The conical extension is continuous. -/
lemma continuous_coneMap (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    Continuous (coneMap φ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx; exact continuousAt_coneMap_zero φ
  · have hs : ContinuousOn (coneMap φ) {x : E | x ≠ 0} :=
      continuousOn_iff_continuous_domRestrict.mpr (continuous_coneMap_subtype φ)
    exact (hs x hx).continuousAt (isOpen_ne.mem_nhds hx)

omit [InnerProductSpace ℝ E] in
/-- Membership in the closed unit ball, in terms of the norm. -/
lemma norm_le_one_of_mem (x : Metric.closedBall (0 : E) 1) : ‖(x : E)‖ ≤ 1 := by
  have h := x.2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  exact h

lemma coneMap_mem_closedBall (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1)
    (x : Metric.closedBall (0 : E) 1) :
    coneMap φ (x : E) ∈ Metric.closedBall (0 : E) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_coneMap]
  exact norm_le_one_of_mem x

/-- The conical extension, restricted to the closed unit ball. -/
def ballMap (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    Metric.closedBall (0 : E) 1 → Metric.closedBall (0 : E) 1 :=
  fun x => ⟨coneMap φ x, coneMap_mem_closedBall φ x⟩

lemma continuous_ballMap (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    Continuous (ballMap φ) :=
  Continuous.subtype_mk ((continuous_coneMap φ).comp continuous_subtype_val)
    (coneMap_mem_closedBall φ)

/-- The conical extension of `φ.symm` is a left inverse of the conical extension of `φ`. -/
lemma coneMap_comp_symm (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) (x : E) :
    coneMap φ.symm (coneMap φ x) = x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hne : coneMap φ x ≠ 0 := by
      intro h
      have h1 : ‖coneMap φ x‖ = 0 := by rw [h, norm_zero]
      rw [norm_coneMap] at h1
      exact (norm_ne_zero_iff.mpr hx) h1
    have key : sphereProj (coneMap φ x) hne = φ (sphereProj x hx) := by
      apply Subtype.ext
      rw [sphereProj_coe, norm_coneMap, coneMap_of_ne φ hx,
        inv_smul_smul₀ (norm_ne_zero_iff.mpr hx)]
    rw [coneMap_of_ne φ.symm hne, norm_coneMap, key, Homeomorph.symm_apply_apply,
      sphereProj_coe, smul_inv_smul₀ (norm_ne_zero_iff.mpr hx)]

lemma ballMap_left_inv (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    Function.LeftInverse (ballMap φ.symm) (ballMap φ) := by
  intro x
  apply Subtype.ext
  exact coneMap_comp_symm φ (x : E)

lemma ballMap_right_inv (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    Function.RightInverse (ballMap φ.symm) (ballMap φ) := by
  intro y
  apply Subtype.ext
  exact coneMap_comp_symm φ.symm (y : E)

/-- The conical extension of a sphere homeomorphism as a homeomorphism of the closed ball. -/
def ballHomeomorph (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    Metric.closedBall (0 : E) 1 ≃ₜ Metric.closedBall (0 : E) 1 where
  toFun := ballMap φ
  invFun := ballMap φ.symm
  left_inv := ballMap_left_inv φ
  right_inv := ballMap_right_inv φ
  continuous_toFun := continuous_ballMap φ
  continuous_invFun := continuous_ballMap φ.symm

@[simp] lemma ballHomeomorph_apply (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1)
    (x : Metric.closedBall (0 : E) 1) : ballHomeomorph φ x = ballMap φ x := rfl

/-- On the unit sphere, the conical extension agrees with the original map. -/
lemma coneMap_sphere (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1)
    (x : Metric.sphere (0 : E) 1) : coneMap φ (x : E) = (φ x : E) := by
  have hnorm : ‖(x : E)‖ = 1 := by
    have h := x.2
    rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
  have hx : (x : E) ≠ 0 := by
    intro h; rw [h] at hnorm; simp at hnorm
  have hsub : sphereProj (x : E) hx = x := by
    apply Subtype.ext
    rw [sphereProj_coe, hnorm, inv_one, one_smul]
  rw [coneMap_of_ne φ hx, hnorm, one_smul, hsub]

/-- **The radial extension (Alexander trick)**: every homeomorphism of the unit sphere of a real
inner product space extends to a homeomorphism of the closed unit ball fixing the origin.  The
extension is the conical one: `Φ x = ‖x‖ • φ (x / ‖x‖)` for `x ≠ 0`, and `Φ 0 = 0`. -/
theorem radial_extension {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    ∃ Φ : Metric.closedBall (0 : E) 1 ≃ₜ Metric.closedBall (0 : E) 1,
      Φ 0 = 0 ∧ ∀ x : Metric.sphere (0 : E) 1,
        Φ (Set.inclusion Metric.sphere_subset_closedBall x)
          = Set.inclusion Metric.sphere_subset_closedBall (φ x) := by
  refine ⟨ballHomeomorph φ, ?_, ?_⟩
  · apply Subtype.ext
    simp [ballHomeomorph, ballMap, coneMap]
  · intro x
    apply Subtype.ext
    exact coneMap_sphere φ x

end

end Commons.Topology.Sphere