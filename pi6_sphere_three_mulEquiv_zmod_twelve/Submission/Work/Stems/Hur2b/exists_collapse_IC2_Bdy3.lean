import Mathlib
import Submission.Work.Stems.Hur2b.GluingModel
import Submission.Work.Stems.exists_collapsingMap

set_option synthInstance.maxHeartbeats 400000

/-!
# A collapse `I² → ∂I³` with the corner `(0,0,0)` as base point

The target theorem of this file produces a continuous map `ψ : I² → ∂I³` which is *constant* on
the boundary `∂I²` with value the vertex `(0,0,0)` of `∂I³` (`Work.Stems.Hur2b.vertexBdy3`), and
which is injective off `∂I²`; equivalently `ψ` realises the quotient `I²/∂I² ≅ S² ≅ ∂I³`.

The construction goes through the round sphere `S² ⊆ ℝ³`:

* `C2.cornerDir = -(1,1,1)/√3` is the unit vector pointing from the centre `(1/2,1/2,1/2)` of the
  cube `I³` to the corner `(0,0,0)`; it is the "north pole" of our stereographic chart.
* `C2.sphereToBdy3 : S² → ∂I³` is the inverse of the radial projection from the cube centre:
  `u ↦ (max_i |u_i|)⁻¹ • u`, rescaled by `(z ↦ (z+1)/2)` from `[-1,1]³` to `I³`.  It is
  continuous, injective, and sends `cornerDir` to the corner `(0,0,0)`.
* `C2.onePointHomeo : OnePoint ℝ² ≃ₜ S²` is Mathlib's homeomorphism (stereographic projection from
  `cornerDir`, transported along a continuous linear equivalence
  `ℝ² ≅ (ℝ ∙ cornerDir)ᗮ`) — it sends `∞` to `cornerDir`.
* Finally `Work.Stems.cubeToOnePoint 2` collapses `∂I²` to `∞` and is injective off `∂I²`, so the
  composite `ψ = sphereToBdy3 ∘ onePointHomeo ∘ cubeToOnePoint 2` has the required properties.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

/-! The auxiliary construction of the collapse `I² → ∂I³`. -/
namespace CollapseC2

noncomputable section

open Work.Stems.Cubical

/-- The vector `(1,1,1) ∈ ℝ³`. -/
def oneVec : EuclideanSpace ℝ (Fin 3) := !₂[(1:ℝ),1,1]

theorem oneVec_apply (i : Fin 3) : oneVec i = 1 := by fin_cases i <;> rfl

theorem oneVec_norm : ‖oneVec‖ = Real.sqrt 3 := by
  have h2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) oneVec
  rw [Fin.sum_univ_three] at h2
  have h3 : ∀ i : Fin 3, ‖oneVec i‖ ^ 2 = (1:ℝ) := by intro i; rw [oneVec_apply]; simp
  simp only [h3] at h2
  norm_num at h2
  rw [← Real.sqrt_sq (norm_nonneg oneVec), h2]

/-- The unit vector pointing from the centre `(1/2,1/2,1/2)` of `I³` to the corner `(0,0,0)`:
`-(1,1,1)/√3`. -/
def cornerDir : EuclideanSpace ℝ (Fin 3) := -(Real.sqrt 3)⁻¹ • oneVec

theorem cornerDir_apply (i : Fin 3) : cornerDir i = -(Real.sqrt 3)⁻¹ := by
  rw [cornerDir, PiLp.smul_apply, oneVec_apply, smul_eq_mul, mul_one]

theorem cornerDir_norm : ‖cornerDir‖ = 1 := by
  rw [cornerDir, norm_smul, oneVec_norm, Real.norm_eq_abs, abs_neg, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg 3)]
  rw [inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))]

theorem cornerDir_ne_zero : cornerDir ≠ 0 := by
  intro h
  have h1 := cornerDir_norm
  rw [h] at h1
  simp at h1

/-- The `ℓ∞` norm `max_i |u_i|` on `ℝ³`. -/
def mnorm (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (Finset.univ : Finset (Fin 3)).sup' ⟨0, Finset.mem_univ 0⟩ (fun i => |u i|)

theorem mnorm_apply_le (u : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) : |u i| ≤ mnorm u :=
  Finset.le_sup' (fun i : Fin 3 => |u i|) (Finset.mem_univ i)

theorem mnorm_eq_of_forall {u : EuclideanSpace ℝ (Fin 3)} {c : ℝ}
    (h : ∀ i : Fin 3, |u i| = c) : mnorm u = c := by
  rw [mnorm]
  exact Finset.sup'_eq_of_forall _ _ (fun i _ => h i)

theorem mnorm_pos {u : EuclideanSpace ℝ (Fin 3)} (hu : u ≠ 0) : 0 < mnorm u := by
  by_contra h
  push Not at h
  apply hu
  refine PiLp.ext (fun i => ?_)
  have h1 := mnorm_apply_le u i
  have h2 : |u i| ≤ 0 := le_trans h1 h
  have h3 : |u i| = 0 := le_antisymm h2 (abs_nonneg _)
  simpa using h3

theorem continuous_mnorm : Continuous mnorm := by
  refine Continuous.finset_sup'_apply
    (⟨0, Finset.mem_univ 0⟩ : (Finset.univ : Finset (Fin 3)).Nonempty) ?_
  intro i _
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.abs

theorem mnorm_cornerDir : mnorm cornerDir = (Real.sqrt 3)⁻¹ := by
  refine mnorm_eq_of_forall (fun i => ?_)
  rw [cornerDir_apply, abs_neg, abs_inv, abs_of_nonneg (Real.sqrt_nonneg 3)]

/-- A point of the unit sphere is nonzero. -/
theorem sphere_ne_zero (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : u.1 ≠ 0 := by
  intro h
  have h1 : ‖u.1‖ = 1 := norm_eq_of_mem_sphere u
  rw [h] at h1
  simp at h1

/-- The coordinates of the inverse radial projection `S² → ∂I³`, before clamping. -/
def sphereVal (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (i : Fin 3) : ℝ :=
  ((mnorm u.1)⁻¹ * u.1 i + 1) / 2

theorem sphereVal_mem (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (i : Fin 3) :
    0 ≤ sphereVal u i ∧ sphereVal u i ≤ 1 := by
  have hM := mnorm_pos (sphere_ne_zero u)
  have hle := mnorm_apply_le u.1 i
  have hinv : 0 < (mnorm u.1)⁻¹ := inv_pos.mpr hM
  have hmul : (mnorm u.1)⁻¹ * mnorm u.1 = 1 := inv_mul_cancel₀ (ne_of_gt hM)
  have h2 : -(mnorm u.1) ≤ u.1 i := (abs_le.mp hle).1
  have h3 : u.1 i ≤ mnorm u.1 := (abs_le.mp hle).2
  have hl : -1 ≤ (mnorm u.1)⁻¹ * u.1 i := by nlinarith [h2, hmul, hinv, hM]
  have hr : (mnorm u.1)⁻¹ * u.1 i ≤ 1 := by nlinarith [h3, hmul, hinv, hM]
  constructor <;> rw [sphereVal] <;> linarith

/-- The coordinates of `sphereToBdy3` as elements of the unit interval. -/
def sphereCoord (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (i : Fin 3) : unitInterval :=
  ⟨sphereVal u i, (sphereVal_mem u i).1, (sphereVal_mem u i).2⟩

theorem sphereCoord_coe (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (i : Fin 3) :
    ((sphereCoord u i : unitInterval) : ℝ) = sphereVal u i := rfl

/-- **The inverse of the radial projection, rescaled to `∂I³`.**  It sends a unit vector `u` to
`(max_i |u_i|)⁻¹ u`, rescaled from `∂[-1,1]³` to `∂I³ = Bdy3`; in particular it is the inverse of
the radial projection from the centre of the cube. -/
def sphereToBdy3 (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : Bdy3 :=
  ⟨fun i => sphereCoord u i, by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup'
      (⟨0, Finset.mem_univ 0⟩ : (Finset.univ : Finset (Fin 3)).Nonempty) (fun i : Fin 3 => |u.1 i|)
    have hMi : mnorm u.1 = |u.1 i| := by rw [mnorm]; exact hi
    have hM := mnorm_pos (sphere_ne_zero u)
    refine ⟨i, ?_⟩
    rcases abs_cases (u.1 i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      apply Subtype.ext
      show sphereVal u i = ((1 : unitInterval) : ℝ)
      rw [show ((1:unitInterval):ℝ) = 1 from rfl]
      have hui : u.1 i = mnorm u.1 := h1.symm.trans hMi.symm
      rw [sphereVal, hui, inv_mul_cancel₀ (ne_of_gt hM)]
      ring
    · left
      apply Subtype.ext
      show sphereVal u i = ((0 : unitInterval) : ℝ)
      rw [show ((0:unitInterval):ℝ) = 0 from rfl]
      have hui : u.1 i = -mnorm u.1 := by linarith [h1, hMi]
      rw [sphereVal, hui, mul_neg, inv_mul_cancel₀ (ne_of_gt hM)]
      ring⟩

theorem sphereToBdy3_coe (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (i : Fin 3) :
    ((sphereToBdy3 u).1 i : ℝ) = sphereVal u i := rfl

theorem continuous_sphereToBdy3 : Continuous sphereToBdy3 := by
  refine continuous_induced_rng.mpr (continuous_pi (fun i => ?_))
  refine Continuous.subtype_mk ?_ _
  have hM : Continuous fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => mnorm u.1 :=
    continuous_mnorm.comp continuous_subtype_val
  have hinv : Continuous fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => (mnorm u.1)⁻¹ :=
    hM.inv₀ (fun u => ne_of_gt (mnorm_pos (sphere_ne_zero u)))
  have hproj : Continuous fun u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => u.1 i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_subtype_val
  exact ((hinv.mul hproj).add continuous_const).div_const 2

/-- `cornerDir` as a point of the unit sphere. -/
def cornerPt : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨cornerDir, mem_sphere_zero_iff_norm.mpr cornerDir_norm⟩

/-- **`sphereToBdy3` sends the corner direction to the vertex `(0,0,0)`.** -/
theorem sphereToBdy3_cornerPt : sphereToBdy3 cornerPt = vertexBdy3 := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  show sphereVal cornerPt i = ((0 : unitInterval) : ℝ)
  rw [show ((0:unitInterval):ℝ) = 0 from rfl, sphereVal]
  have hM : mnorm cornerPt.1 = (Real.sqrt 3)⁻¹ := mnorm_cornerDir
  have hc : cornerPt.1 i = -(Real.sqrt 3)⁻¹ := cornerDir_apply i
  rw [hM, hc, inv_inv]
  field_simp
  ring

/-- **`sphereToBdy3` is injective.** -/
theorem sphereToBdy3_injective : Function.Injective sphereToBdy3 := by
  intro u u' h
  have hM := mnorm_pos (sphere_ne_zero u)
  have hM' := mnorm_pos (sphere_ne_zero u')
  have hcoord : ∀ i, sphereVal u i = sphereVal u' i := by
    intro i
    have := congrArg (fun z : Bdy3 => ((z.1 i : unitInterval) : ℝ)) h
    simpa [sphereToBdy3_coe] using this
  have hvec : (mnorm u.1)⁻¹ • u.1 = (mnorm u'.1)⁻¹ • u'.1 := by
    refine PiLp.ext (fun i => ?_)
    have := hcoord i
    simp only [sphereVal] at this
    have h2 : (mnorm u.1)⁻¹ * u.1 i = (mnorm u'.1)⁻¹ * u'.1 i := by linarith
    simpa [PiLp.smul_apply, smul_eq_mul] using h2
  have hnorm : (mnorm u.1)⁻¹ = (mnorm u'.1)⁻¹ := by
    have := congrArg norm hvec
    rw [norm_smul, norm_smul, norm_eq_of_mem_sphere u, norm_eq_of_mem_sphere u',
      mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hM), abs_of_pos (inv_pos.mpr hM')] at this
    exact this
  have hMeq : mnorm u.1 = mnorm u'.1 := by
    have := congrArg Inv.inv hnorm
    simpa using this
  have h5 : u.1 = u'.1 := by
    rw [hMeq] at hvec
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => mnorm u'.1 • v) hvec
    simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt hM'), one_smul] at this
    exact this
  exact Subtype.ext h5

theorem finrank_eq : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) =
    Module.finrank ℝ ↥(ℝ ∙ cornerDir)ᗮ := by
  have h : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  rw [Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := 2) cornerDir_ne_zero]
  simp

/-- A continuous linear equivalence `ℝ² ≅ (ℝ ∙ cornerDir)ᗮ`. -/
def linEquiv : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ↥(ℝ ∙ cornerDir)ᗮ :=
  (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq finrank_eq).some

/-- **The one-point compactification of `ℝ²` as the unit sphere, with `∞ ↦ cornerDir`:** the
inverse stereographic projection from the pole `cornerDir`. -/
def onePointHomeo : OnePoint (EuclideanSpace ℝ (Fin 2)) ≃ₜ
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  (linEquiv.toHomeomorph).onePointCongr.trans (onePointHyperplaneHomeoUnitSphere cornerDir_norm)

theorem onePointHomeo_infty : onePointHomeo OnePoint.infty = cornerPt := by
  simp only [onePointHomeo, Homeomorph.trans_apply, Homeomorph.onePointCongr_apply,
    OnePoint.map_infty, cornerPt]
  rw [onePointHyperplaneHomeoUnitSphere, OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty]

end
end CollapseC2

open CollapseC2

theorem exists_collapse_IC2_Bdy3 :
    ∃ ψ : ContinuousMap (Work.Stems.Cubical.IC 2) Work.Stems.Hur2b.Bdy3,
      (∀ y ∈ Cube.boundary (Fin 2), ψ y = Work.Stems.Hur2b.vertexBdy3) ∧
      (∀ y y', ψ y = ψ y' →
        y = y' ∨ (y ∈ Cube.boundary (Fin 2) ∧ y' ∈ Cube.boundary (Fin 2))) := by
  refine ⟨⟨fun y => sphereToBdy3 (onePointHomeo (Work.Stems.cubeToOnePoint 2 y)),
    continuous_sphereToBdy3.comp
      (onePointHomeo.continuous.comp (Work.Stems.cubeToOnePoint_continuous 2))⟩, ?_, ?_⟩
  · intro y hy
    show sphereToBdy3 (onePointHomeo (Work.Stems.cubeToOnePoint 2 y))
      = Work.Stems.Hur2b.vertexBdy3
    rw [Work.Stems.cubeToOnePoint_eq_infty_of_mem_boundary hy, onePointHomeo_infty,
      sphereToBdy3_cornerPt]
  · intro y y' h
    have h1 : onePointHomeo (Work.Stems.cubeToOnePoint 2 y)
        = onePointHomeo (Work.Stems.cubeToOnePoint 2 y') := sphereToBdy3_injective h
    exact Work.Stems.cubeToOnePoint_fibers 2 (onePointHomeo.injective h1)

end Work.Stems.Hur2b
