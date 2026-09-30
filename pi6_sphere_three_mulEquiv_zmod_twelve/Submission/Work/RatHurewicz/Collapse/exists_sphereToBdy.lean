import Mathlib
import Submission.Work.RatHurewicz.Collapse.Defs

set_option synthInstance.maxHeartbeats 400000

/-!
# The ℓ∞-radial projection `S^d → ∂I^{d+1}`

For every `d` the map `u ↦ (max_i |u_i|)⁻¹ • u`, rescaled from `∂[-1,1]^{d+1}` to `∂I^{d+1}`
(that is, `x ↦ (u_i / max_j |u_j| + 1)/2` in coordinates), sends the unit sphere onto the boundary
of the cube `I^{d+1}`, is injective, and sends the corner direction `cornerPt d` to the corner
`(0,…,0)`.  This is the `d`-dimensional version of
`Work.Stems.Hur2b.exists_collapse_IC2_Bdy3` (the case `d = 2`); the proof is the same.
-/

open scoped unitInterval Topology

namespace Work.RatHurewicz.Collapse

noncomputable section

open Work.Stems.Cubical

variable (d : ℕ)

/-- The `ℓ∞` norm `max_i |u_i|` on `ℝ^{d+1}`. -/
def mnorm (u : EuclideanSpace ℝ (Fin (d + 1))) : ℝ :=
  (Finset.univ : Finset (Fin (d + 1))).sup' ⟨(0 : Fin (d + 1)), Finset.mem_univ _⟩
    (fun i => |u i|)

theorem mnorm_apply_le (u : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin (d + 1)) :
    |u i| ≤ mnorm d u :=
  Finset.le_sup' (fun i : Fin (d + 1) => |u i|) (Finset.mem_univ i)

theorem mnorm_eq_of_forall {u : EuclideanSpace ℝ (Fin (d + 1))} {c : ℝ}
    (h : ∀ i : Fin (d + 1), |u i| = c) : mnorm d u = c := by
  rw [mnorm]
  exact Finset.sup'_eq_of_forall _ _ (fun i _ => h i)

theorem mnorm_pos {u : EuclideanSpace ℝ (Fin (d + 1))} (hu : u ≠ 0) : 0 < mnorm d u := by
  by_contra h
  push Not at h
  apply hu
  refine PiLp.ext (fun i => ?_)
  have h1 := mnorm_apply_le d u i
  have h2 : |u i| ≤ 0 := le_trans h1 h
  have h3 : |u i| = 0 := le_antisymm h2 (abs_nonneg _)
  simpa using h3

theorem continuous_mnorm : Continuous (mnorm d) := by
  refine Continuous.finset_sup'_apply
    (⟨(0 : Fin (d + 1)), Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin (d + 1))).Nonempty) ?_
  intro i _
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.abs

theorem mnorm_cornerVec : mnorm d (cornerVec d) = (Real.sqrt ((d : ℝ) + 1))⁻¹ := by
  refine mnorm_eq_of_forall d (fun i => ?_)
  rw [cornerVec_apply, abs_neg, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- A point of the unit sphere is nonzero. -/
theorem sphere_ne_zero (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) : u.1 ≠ 0 := by
  intro h
  have h1 : ‖u.1‖ = 1 := norm_eq_of_mem_sphere u
  rw [h] at h1
  simp at h1

/-- The coordinates of the inverse radial projection `S^d → ∂I^{d+1}`, before clamping. -/
def sphereVal (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) (i : Fin (d + 1)) : ℝ :=
  ((mnorm d u.1)⁻¹ * u.1 i + 1) / 2

theorem sphereVal_mem (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)
    (i : Fin (d + 1)) : 0 ≤ sphereVal d u i ∧ sphereVal d u i ≤ 1 := by
  have hM := mnorm_pos d (sphere_ne_zero d u)
  have hle := mnorm_apply_le d u.1 i
  have hinv : 0 < (mnorm d u.1)⁻¹ := inv_pos.mpr hM
  have hmul : (mnorm d u.1)⁻¹ * mnorm d u.1 = 1 := inv_mul_cancel₀ (ne_of_gt hM)
  have h2 : -(mnorm d u.1) ≤ u.1 i := (abs_le.mp hle).1
  have h3 : u.1 i ≤ mnorm d u.1 := (abs_le.mp hle).2
  have hl : -1 ≤ (mnorm d u.1)⁻¹ * u.1 i := by nlinarith [h2, hmul, hinv, hM]
  have hr : (mnorm d u.1)⁻¹ * u.1 i ≤ 1 := by nlinarith [h3, hmul, hinv, hM]
  constructor <;> rw [sphereVal] <;> linarith

/-- The coordinates of `sphereToBdy` as elements of the unit interval. -/
def sphereCoord (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) (i : Fin (d + 1)) :
    unitInterval :=
  ⟨sphereVal d u i, (sphereVal_mem d u i).1, (sphereVal_mem d u i).2⟩

theorem sphereCoord_coe (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)
    (i : Fin (d + 1)) : ((sphereCoord d u i : unitInterval) : ℝ) = sphereVal d u i := rfl

/-- **The inverse of the radial projection, rescaled to `∂I^{d+1}`.**  It sends a unit vector `u` to
`(max_i |u_i|)⁻¹ u`, rescaled from `∂[-1,1]^{d+1}` to `∂I^{d+1}`; in particular it is the inverse
of the radial projection from the centre of the cube. -/
def sphereToBdy (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) :
    ↥(Cube.boundary (Fin (d + 1))) :=
  ⟨fun i => sphereCoord d u i, by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup'
      (⟨(0 : Fin (d + 1)), Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin (d + 1))).Nonempty)
      (fun i : Fin (d + 1) => |u.1 i|)
    have hMi : mnorm d u.1 = |u.1 i| := by rw [mnorm]; exact hi
    have hM := mnorm_pos d (sphere_ne_zero d u)
    refine ⟨i, ?_⟩
    rcases abs_cases (u.1 i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      apply Subtype.ext
      show sphereVal d u i = ((1 : unitInterval) : ℝ)
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
      have hui : u.1 i = mnorm d u.1 := h1.symm.trans hMi.symm
      rw [sphereVal, hui, inv_mul_cancel₀ (ne_of_gt hM)]
      ring
    · left
      apply Subtype.ext
      show sphereVal d u i = ((0 : unitInterval) : ℝ)
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
      have hui : u.1 i = -(mnorm d u.1) := by linarith [h1, hMi]
      rw [sphereVal, hui, mul_neg, inv_mul_cancel₀ (ne_of_gt hM)]
      ring⟩

theorem sphereToBdy_coe (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)
    (i : Fin (d + 1)) : ((sphereToBdy d u).1 i : ℝ) = sphereVal d u i := rfl

theorem continuous_sphereToBdy : Continuous (sphereToBdy d) := by
  refine continuous_induced_rng.mpr (continuous_pi (fun i => ?_))
  refine Continuous.subtype_mk ?_ _
  have hM : Continuous fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 =>
      mnorm d u.1 := (continuous_mnorm d).comp continuous_subtype_val
  have hinv : Continuous fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 =>
      (mnorm d u.1)⁻¹ := hM.inv₀ (fun u => ne_of_gt (mnorm_pos d (sphere_ne_zero d u)))
  have hproj : Continuous fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 => u.1 i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_subtype_val
  exact ((hinv.mul hproj).add continuous_const).div_const 2

/-- **`sphereToBdy` sends the corner direction to the corner `(0,…,0)`.** -/
theorem sphereToBdy_cornerPt : sphereToBdy d (cornerPt d) = cornerBdy d := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  show sphereVal d (cornerPt d) i = ((0 : unitInterval) : ℝ)
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sphereVal]
  have hM : mnorm d (cornerPt d).1 = (Real.sqrt ((d : ℝ) + 1))⁻¹ := mnorm_cornerVec d
  have hc : (cornerPt d).1 i = -(Real.sqrt ((d : ℝ) + 1))⁻¹ := cornerVec_apply d i
  rw [hM, hc, inv_inv]
  field_simp
  ring

/-- **`sphereToBdy` is injective.** -/
theorem sphereToBdy_injective : Function.Injective (sphereToBdy d) := by
  intro u u' h
  have hM := mnorm_pos d (sphere_ne_zero d u)
  have hM' := mnorm_pos d (sphere_ne_zero d u')
  have hcoord : ∀ i, sphereVal d u i = sphereVal d u' i := by
    intro i
    have := congrArg (fun z : ↥(Cube.boundary (Fin (d + 1))) => ((z.1 i : unitInterval) : ℝ)) h
    simpa [sphereToBdy_coe] using this
  have hvec : (mnorm d u.1)⁻¹ • u.1 = (mnorm d u'.1)⁻¹ • u'.1 := by
    refine PiLp.ext (fun i => ?_)
    have := hcoord i
    simp only [sphereVal] at this
    have h2 : (mnorm d u.1)⁻¹ * u.1 i = (mnorm d u'.1)⁻¹ * u'.1 i := by linarith
    simpa [PiLp.smul_apply, smul_eq_mul] using h2
  have hnorm : (mnorm d u.1)⁻¹ = (mnorm d u'.1)⁻¹ := by
    have := congrArg norm hvec
    rw [norm_smul, norm_smul, norm_eq_of_mem_sphere u, norm_eq_of_mem_sphere u',
      mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hM), abs_of_pos (inv_pos.mpr hM')] at this
    exact this
  have hMeq : mnorm d u.1 = mnorm d u'.1 := by
    have := congrArg Inv.inv hnorm
    simpa using this
  have h5 : u.1 = u'.1 := by
    rw [hMeq] at hvec
    have := congrArg (fun v : EuclideanSpace ℝ (Fin (d + 1)) => mnorm d u'.1 • v) hvec
    simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt hM'), one_smul] at this
    exact this
  exact Subtype.ext h5

/-- **The inverse radial projection `S^d → ∂I^{d+1}`**: a continuous injection sending the corner
direction to the corner. -/
theorem exists_sphereToBdy (d : ℕ) :
    ∃ Φ : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1,
        ↥(Cube.boundary (Fin (d + 1)))),
      Function.Injective Φ ∧
        Φ (cornerPt d) = cornerBdy d :=
  ⟨⟨sphereToBdy d, continuous_sphereToBdy d⟩, sphereToBdy_injective d, sphereToBdy_cornerPt d⟩

end

end Work.RatHurewicz.Collapse
