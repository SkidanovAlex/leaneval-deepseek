import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs

/-!
# The Alexander trick: a homeomorphism of the circle extends to the disc

Given a homeomorphism `ρ` of the unit circle `Metric.sphere (0 : ℂ) 1`, we build a
homeomorphism `Φ` of the closed unit disc `Metric.closedBall (0 : ℂ) 1` whose restriction
to the boundary is `ρ` and which fixes the centre `0`.

The map is the *radial (cone) extension*

`Φ z = ‖z‖ • ρ(z / ‖z‖)`   for `z ≠ 0`,   and   `Φ 0 = 0`.

It is continuous because it preserves the norm (at the origin `‖Φ z‖ = ‖z‖ → 0`), and it is a
homeomorphism with inverse the radial extension of `ρ.symm`.  This is the classical
"Alexander trick" (every homeomorphism of `Sⁿ⁻¹` extends to one of `Dⁿ`), in the plane.
-/

namespace Work.Smooth.SphereJordan

open Metric Set

noncomputable section

/-- The **radial direction** of a complex number as a point of the unit circle: `x ↦ x / ‖x‖`
for `x ≠ 0`, and the base point `1` at the origin.  (The latter choice is immaterial: every
occurrence of `circleDir` is multiplied by `‖x‖`, which vanishes at `0`.) -/
def circleDir (x : ℂ) : Metric.sphere (0 : ℂ) 1 :=
  if hx : x = 0 then ⟨1, mem_sphere_zero_iff_norm.mpr (by simp)⟩
  else ⟨(‖x‖)⁻¹ • x, mem_sphere_zero_iff_norm.mpr (by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)] )⟩

/-- The **radial extension** of a circle homeomorphism `ρ` to a self-map of `ℂ`:
`x ↦ ‖x‖ • ρ(x / ‖x‖)` (with `0 ↦ 0`).  It preserves the norm and is continuous. -/
def radialMap (ρ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) (x : ℂ) : ℂ :=
  ‖x‖ • ((ρ (circleDir x) : Metric.sphere (0 : ℂ) 1) : ℂ)

lemma radialMap_zero (ρ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) :
    radialMap ρ 0 = 0 := by
  simp [radialMap]

/-- `radialMap ρ` preserves the norm. -/
lemma norm_radialMap (ρ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) (x : ℂ) :
    ‖radialMap ρ x‖ = ‖x‖ := by
  rw [radialMap, norm_smul, Real.norm_of_nonneg (norm_nonneg x),
    mem_sphere_zero_iff_norm.mp (ρ (circleDir x)).2, mul_one]

/-- On the circle, the radial direction is the point itself. -/
lemma circleDir_coe (a : Metric.sphere (0 : ℂ) 1) : circleDir (a : ℂ) = a := by
  have ha : (a : ℂ) ≠ 0 := by
    intro h
    have := mem_sphere_zero_iff_norm.mp a.2
    rw [h, norm_zero] at this
    norm_num at this
  rw [circleDir, dif_neg ha]
  apply Subtype.ext
  change (‖(a : ℂ)‖)⁻¹ • (a : ℂ) = (a : ℂ)
  rw [mem_sphere_zero_iff_norm.mp a.2, inv_one, one_smul]

/-- The radial direction is invariant under positive rescaling. -/
lemma circleDir_smul_pos (x : ℂ) {t : ℝ} (ht : 0 < t) :
    circleDir (t • x) = circleDir x := by
  by_cases hx : x = 0
  · rw [hx, smul_zero]
  · have htx : t • x ≠ 0 := by
      intro h
      rcases smul_eq_zero.mp h with h' | h'
      · exact ht.ne' h'
      · exact hx h'
    rw [circleDir, dif_neg htx, circleDir, dif_neg hx]
    apply Subtype.ext
    change ‖t • x‖⁻¹ • (t • x) = ‖x‖⁻¹ • x
    have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    rw [norm_smul, Real.norm_of_nonneg ht.le, smul_smul]
    congr 1
    field_simp

/-- The value of the radial direction off the origin: `circleDir x = x / ‖x‖`. -/
lemma coe_circleDir_of_ne (x : ℂ) (hx : x ≠ 0) :
    ((circleDir x : Metric.sphere (0 : ℂ) 1) : ℂ) = ‖x‖⁻¹ • x := by
  rw [circleDir, dif_neg hx]

/-- The radial extension of `ρ.symm` inverts the radial extension of `ρ`. -/
lemma radialMap_symm_radialMap (ρ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1)
    (x : ℂ) : radialMap ρ.symm (radialMap ρ x) = x := by
  by_cases hx : x = 0
  · rw [hx, radialMap_zero, radialMap_zero]
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h1 : circleDir (radialMap ρ x) = ρ (circleDir x) := by
      rw [radialMap]
      rw [circleDir_smul_pos _ hxpos, circleDir_coe]
    have hmain : radialMap ρ.symm (radialMap ρ x)
        = ‖radialMap ρ x‖ •
          ((ρ.symm (circleDir (radialMap ρ x)) : Metric.sphere (0 : ℂ) 1) : ℂ) := rfl
    rw [hmain, h1, Homeomorph.symm_apply_apply, norm_radialMap,
      coe_circleDir_of_ne x hx, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),
      one_smul]

/-- Polar coordinates on the punctured plane: the (Mathlib) homeomorphism
`ℂ \ {0} ≃ₜ S¹ × (0,∞)`, `x ↦ (x/‖x‖, ‖x‖)`. -/
abbrev sphereProdHomeo : ({0}ᶜ : Set ℂ) ≃ₜ
    (Metric.sphere (0 : ℂ) 1 × Set.Ioi (0 : ℝ)) :=
  homeomorphUnitSphereProd ℂ

lemma sphereProdHomeo_fst (x : ({0}ᶜ : Set ℂ)) :
    ((sphereProdHomeo x).1 : ℂ) = ‖(x : ℂ)‖⁻¹ • (x : ℂ) :=
  homeomorphUnitSphereProd_apply_fst_coe ℂ x

lemma sphereProdHomeo_snd (x : ({0}ᶜ : Set ℂ)) :
    ((sphereProdHomeo x).2 : ℝ) = ‖(x : ℂ)‖ :=
  homeomorphUnitSphereProd_apply_snd_coe ℂ x

/-- `radialMap ρ` is continuous off the origin: in polar coordinates it is
`(u, t) ↦ t • ρ u`, which is continuous. -/
lemma continuousOn_radialMap_compl (ρ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) :
    ContinuousOn (radialMap ρ) ({0}ᶜ : Set ℂ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : ({0}ᶜ : Set ℂ).domRestrict (radialMap ρ)
      = fun x : ({0}ᶜ : Set ℂ) =>
          ((sphereProdHomeo x).2 : ℝ) •
            ((ρ (sphereProdHomeo x).1 : Metric.sphere (0 : ℂ) 1) : ℂ) := by
    funext x
    have hx0 : (x : ℂ) ≠ 0 := by
      have h := x.2
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h
      exact h
    have hdir : circleDir (x : ℂ) = (sphereProdHomeo x).1 := by
      apply Subtype.ext
      rw [coe_circleDir_of_ne (x : ℂ) hx0, sphereProdHomeo_fst]
    show radialMap ρ (x : ℂ) = _
    rw [radialMap, sphereProdHomeo_snd, hdir]
  rw [heq]
  exact (by fun_prop : Continuous (fun p : Metric.sphere (0 : ℂ) 1 × Set.Ioi (0 : ℝ) =>
            (p.2 : ℝ) • ((ρ p.1 : Metric.sphere (0 : ℂ) 1) : ℂ))).comp sphereProdHomeo.continuous

/-- `radialMap ρ` is continuous everywhere: off the origin by the polar-coordinate
description, and at the origin because it preserves the norm. -/
lemma continuous_radialMap (ρ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) :
    Continuous (radialMap ρ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun y hy => ?_⟩
    rw [radialMap_zero, dist_zero_right, norm_radialMap, ← dist_zero_right]
    exact hy
  · exact (continuousOn_radialMap_compl ρ).continuousAt
      (isOpen_compl_singleton.mem_nhds (by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hx))

/-- On the circle, the radial extension of `ρ` is `ρ` itself. -/
lemma radialMap_coe_sphere (ρ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1)
    (x : Metric.sphere (0 : ℂ) 1) :
    radialMap ρ (x : ℂ) = ((ρ x : Metric.sphere (0 : ℂ) 1) : ℂ) := by
  rw [radialMap, circleDir_coe x, mem_sphere_zero_iff_norm.mp x.2, one_smul]

/-- **The Alexander trick.**  The radial extension of a circle homeomorphism `ρ`, restricted to
the closed unit disc, is a homeomorphism of the disc with inverse the radial extension of
`ρ.symm`. -/
def discHomeo (ρ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) :
    Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1 where
  toFun z := ⟨radialMap ρ z.1, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_radialMap, ← dist_zero_right]
    exact z.2⟩
  invFun z := ⟨radialMap ρ.symm z.1, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_radialMap, ← dist_zero_right]
    exact z.2⟩
  left_inv z := by
    apply Subtype.ext
    change radialMap ρ.symm (radialMap ρ z.1) = z.1
    exact radialMap_symm_radialMap ρ z.1
  right_inv z := by
    apply Subtype.ext
    change radialMap ρ (radialMap ρ.symm z.1) = z.1
    have h := radialMap_symm_radialMap ρ.symm z.1
    rwa [Homeomorph.symm_symm] at h
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_radialMap ρ).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_radialMap ρ.symm).comp continuous_subtype_val

/-- **Pardon, Alexander's trick**: every homeomorphism of the unit circle extends to a
homeomorphism of the closed unit disc, fixing the centre and restricting to `ρ` on the
boundary. -/
theorem ballHomeo_of_circleHomeo (ρ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : ℂ) 1) :
    ∃ Φ : Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1,
      (∀ x : Metric.sphere (0 : ℂ) 1,
        ((Φ ⟨(x : ℂ), by
            rw [Metric.mem_closedBall, dist_zero_right]
            exact le_of_eq (by simpa [dist_eq_norm] using x.2)⟩ : Metric.closedBall (0 : ℂ) 1) : ℂ)
          = ((ρ x : Metric.sphere (0 : ℂ) 1) : ℂ)) ∧
      Φ ⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩
        = ⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩ := by
  refine ⟨discHomeo ρ, ?_, ?_⟩
  · intro x
    change radialMap ρ (x : ℂ) = ((ρ x : Metric.sphere (0 : ℂ) 1) : ℂ)
    exact radialMap_coe_sphere ρ x
  · apply Subtype.ext
    change radialMap ρ 0 = 0
    exact radialMap_zero ρ

end

end Work.Smooth.SphereJordan
