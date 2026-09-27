import Mathlib
import Submission.Work.KT.ClutchGeom

namespace Work.KT

open Matrix

noncomputable section

/-! ## Radial contraction of the sphere into the ball -/

section Rad

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The origin of the closed unit ball. -/
def origBall : Ball V :=
  ⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩

/-- Radial contraction of the sphere into the ball: `(x, s) ↦ (1 - s) • x`. -/
def radMap : C(Sph V × unitInterval, Ball V) :=
  ⟨fun p => ⟨(1 - (p.2 : ℝ)) • (p.1 : V), by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
      have h := p.2.2; rw [Set.mem_Icc] at h
      have hx : ‖(p.1 : V)‖ = 1 := by simp
      rw [abs_of_nonneg (by linarith [h.1]), hx, mul_one]
      linarith [h.2]⟩, by
    apply Continuous.subtype_mk
    apply Continuous.smul ?_ ?_
    · exact continuous_const.sub (continuous_subtype_val.comp continuous_snd)
    · exact continuous_subtype_val.comp continuous_fst⟩

end Rad

/-- Evaluation of a function on `X × [0,1]` on the slice `X × {t}`. -/
lemma sliceAt_apply {X : Type} [TopologicalSpace X] (t : unitInterval)
    (g : C(X × unitInterval, ℂ)) (x : X) : sliceAt t g x = g (x, t) := rfl

section Rad

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Application rule for the pull-back along the radial contraction. -/
lemma pullAlg_radMap_apply (f : C(Ball V, ℂ)) (p : Sph V × unitInterval) :
    pullAlg (radMap (V := V)) f p = f (radMap (V := V) p) := by
  simp only [pullAlg, StarAlgHom.coe_toAlgHom, ContinuousMap.compStarAlgHom'_apply,
    ContinuousMap.comp_apply]

/-- The `0`-slice of the pull-back along the radial contraction is restriction to the boundary. -/
lemma sliceAt_zero_pullAlg_radMap (f : C(Ball V, ℂ)) :
    sliceAt (0 : unitInterval) (pullAlg (radMap (V := V)) f) = restRho V f := by
  ext x
  rw [sliceAt_apply, pullAlg_radMap_apply]
  rw [show radMap (V := V) (x, (0 : unitInterval)) = sphToBall V x from by
    apply Subtype.ext; simp [radMap, sphToBall]]
  rfl

/-- The `1`-slice of the pull-back along the radial contraction is evaluation at the origin. -/
lemma sliceAt_one_pullAlg_radMap (f : C(Ball V, ℂ)) :
    sliceAt (1 : unitInterval) (pullAlg (radMap (V := V)) f) =
      algebraMap ℂ C(Sph V, ℂ) (f (origBall (V := V))) := by
  ext x
  rw [sliceAt_apply, pullAlg_radMap_apply]
  rw [show radMap (V := V) (x, (1 : unitInterval)) = origBall (V := V) from by
    apply Subtype.ext; simp [radMap, origBall]]
  rfl

end Rad

/-- **Unwinding the clutching.** If the restriction to the boundary spheres of invertible matrices
`G₁`, `G₂` over the two disks satisfy `ρ G₁ = w · ρ G₂` (i.e. `w = ρ G₁ * (ρ G₂)⁻¹`), then `w` is
homotopic through invertible matrices to a constant matrix: the disks are contractible, so the
radial contractions `y ↦ (1-s)·y` give homotopies from `Gᵢ` to the constant value `Gᵢ(0)`, whence
`H(x,s) = G₁((1-s)x) * (G₂((1-s)x))⁻¹` is the required homotopy. -/
theorem homotopy_of_units {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (w : Matrix (Fin n) (Fin n) C(Sph V, ℂ))
    (G₁ G₂ : (Matrix (Fin n) (Fin n) C(Ball V, ℂ))ˣ)
    (h : RingHom.mapMatrix (Work.KT.restRho V) (↑G₁ : Matrix (Fin n) (Fin n) C(Ball V, ℂ)) =
      w * RingHom.mapMatrix (Work.KT.restRho V) (↑G₂ : Matrix (Fin n) (Fin n) C(Ball V, ℂ))) :
    ∃ H : Matrix (Fin n) (Fin n) C(Sph V × unitInterval, ℂ), IsUnit H ∧
      H.map (sliceAt (0 : unitInterval)) = w ∧
      ∃ c : Matrix (Fin n) (Fin n) ℂ,
        H.map (sliceAt (1 : unitInterval)) = c.map (algebraMap ℂ C(Sph V, ℂ)) := by
  -- The pull-back of functions on the ball along the radial contraction.
  let φ : C(Ball V, ℂ) →+* C(Sph V × unitInterval, ℂ) := (pullAlg (radMap (V := V))).toRingHom
  -- The invertible matrix whose slices are the two ends of the homotopy.
  let M : Matrix (Fin n) (Fin n) C(Ball V, ℂ) := ↑(G₁ * G₂⁻¹)
  -- The co-unit of the radial pull-back is restriction to the boundary.
  have hcomp₀ : (⇑(sliceAt (0 : unitInterval))) ∘ φ = ⇑(restRho V) := by
    funext f
    exact sliceAt_zero_pullAlg_radMap f
  -- The unit of the radial pull-back is evaluation at the origin.
  have hcomp₁ : (⇑(sliceAt (1 : unitInterval))) ∘ φ =
      (algebraMap ℂ C(Sph V, ℂ)) ∘ (⇑(evalC (origBall (V := V)))) := by
    funext f
    rw [Function.comp_apply, Function.comp_apply]
    exact sliceAt_one_pullAlg_radMap f
  -- The two `M`-equations expressing that `M` unwinds the clutching.
  have hval : M * (↑G₂ : Matrix (Fin n) (Fin n) C(Ball V, ℂ)) =
      (↑G₁ : Matrix (Fin n) (Fin n) C(Ball V, ℂ)) := by
    rw [show M = ↑(G₁ * G₂⁻¹) from rfl, ← Units.val_mul]
    congr 1
    group
  have hMw : RingHom.mapMatrix (restRho V) M = w := by
    have hQ : IsUnit (RingHom.mapMatrix (restRho V) (↑G₂ : Matrix (Fin n) (Fin n) C(Ball V, ℂ))) :=
      IsUnit.map (RingHom.mapMatrix (restRho V)) G₂.isUnit
    refine IsUnit.mul_right_cancel hQ ?_
    rw [← map_mul, hval, h]
  refine ⟨RingHom.mapMatrix φ M, IsUnit.map (RingHom.mapMatrix φ) (G₁ * G₂⁻¹).isUnit, ?_, ?_⟩
  · rw [RingHom.mapMatrix_apply, Matrix.map_map, hcomp₀, ← RingHom.mapMatrix_apply]
    exact hMw
  · refine ⟨M.map (evalC (origBall (V := V))), ?_⟩
    rw [RingHom.mapMatrix_apply, Matrix.map_map, hcomp₁, Matrix.map_map]

end

end Work.KT
