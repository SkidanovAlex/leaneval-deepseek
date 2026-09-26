import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData

/-!
# The fibre model of a level of the tilted sweep: vocabulary

The projection `π y = (⟪v,y⟫, ℓ y) : R3 → ℝ²` of the tilted sweep and the planar pieces cut out of
it by the slab faces and the wall: the planar image `tlsZ` of the removed set
`Work.Drive.Mono.tiltedLevelRemoved` and the planar `Π`-region `tlsPiRegion`.

These are the objects in which the one-sphere window of a level of the tilted sweep is analysed in
this directory: the planar image of the level is a disc (`tlsPiRegion` is), and the level itself is
a solid over it.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono.WindowCase

noncomputable section

/-- **The projection of the tilted sweep**: `π y = (⟪v,y⟫, ℓ y)`. -/
def tlsProj (v : R3) (ℓ : R3 →L[ℝ] ℝ) : R3 →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm.toLinearMap.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi (fun i : Fin 2 =>
      if i = 0 then (innerSL ℝ v : R3 →L[ℝ] ℝ) else ℓ))

theorem tlsProj_apply (v : R3) (ℓ : R3 →L[ℝ] ℝ) (y : R3) :
    tlsProj v ℓ y = WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then inner ℝ v y else ℓ y) := by
  ext i
  fin_cases i <;> simp [tlsProj]

/-- The first coordinate of the plane of the fibres. -/
def tlsP (X : EuclideanSpace ℝ (Fin 2)) : ℝ := WithLp.ofLp X 0

/-- The second coordinate of the plane of the fibres. -/
def tlsQ (X : EuclideanSpace ℝ (Fin 2)) : ℝ := WithLp.ofLp X 1

theorem tlsP_tlsProj (v : R3) (ℓ : R3 →L[ℝ] ℝ) (y : R3) : tlsP (tlsProj v ℓ y) = inner ℝ v y := by
  simp [tlsP, tlsProj_apply]

theorem tlsQ_tlsProj (v : R3) (ℓ : R3 →L[ℝ] ℝ) (y : R3) : tlsQ (tlsProj v ℓ y) = ℓ y := by
  simp [tlsQ, tlsProj_apply]

/-- The two coordinates determine a point of the plane of the fibres. -/
theorem tlsP_tlsQ_ext {X Y : EuclideanSpace ℝ (Fin 2)} (h1 : tlsP X = tlsP Y)
    (h2 : tlsQ X = tlsQ Y) : X = Y := by
  ext i
  fin_cases i
  · exact h1
  · exact h2

/-- The **planar image** of a level of the tilted sweep: the image of the removed set under `π`. -/
def tlsZ (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  tlsProj v ℓ '' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam

/-- The **planar `Π`-region** of a level of the tilted sweep: the projection of the closed box cut
by the two slab faces and the wall. -/
def tlsPiRegion (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ) (v : R3)
    (ℓ : R3 →L[ℝ] ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  tlsProj v ℓ '' closure (Submission.PBox s c σ) ∩
    ({X | inner ℝ v c + u + h ≤ tlsP X} ∪ {X | tlsP X ≤ inner ℝ v c + u - h} ∪
      {X | lam ≤ tlsQ X})

/-- **The projection is surjective** as soon as `v ≠ 0` and `ℓ v = 0` with `ℓ ≠ 0`: the two
functionals `⟪v,·⟫` and `ℓ` are then linearly independent, and the range of `π` is all of `ℝ²`. -/
theorem tlsProj_surjective {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) : Function.Surjective (tlsProj v ℓ) := by
  obtain ⟨y₁, hy₁⟩ : ∃ y : R3, ℓ y ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓne (ContinuousLinearMap.ext fun y => by simpa using h y)
  have hv2 : ‖v‖ ^ 2 ≠ 0 := by
    have h : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    positivity
  intro X
  set y : R3 := (tlsQ X / ℓ y₁) • y₁ +
    ((tlsP X - (tlsQ X / ℓ y₁) * inner ℝ v y₁) / ‖v‖ ^ 2) • v with hy_def
  refine ⟨y, tlsP_tlsQ_ext ?_ ?_⟩
  · rw [tlsP_tlsProj, hy_def, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp
    ring
  · rw [tlsQ_tlsProj, hy_def]
    simp only [map_add, map_smul, hℓv, smul_eq_mul, mul_zero, add_zero]
    field_simp

end

end Work.Drive.Mono.WindowCase
