import Mathlib
import Submission.Work.WilkiesH.Norm.Defs

/-!
# `normMap σ` is continuous on the normalised image `normSet σ X`

Every point `y` of `normSet σ X = normMap σ '' (X ∩ normPiece σ)` is the image of a point
`w ∈ normPiece σ`, hence for a coordinate `i` with `σ i = big` (resp. `bigNeg`) we have
`w i ∈ (1,∞)` (resp. `(-∞,-1)`), so `y i = (w i)⁻¹` (resp. `-(w i)⁻¹`) is non-zero.  Inversion
is continuous at non-zero points, so the `i`-th coordinate map `y ↦ shapeMap (σ i) (y i)` is
continuous on `normSet σ X`; the identity and negation coordinates are continuous everywhere.
Continuity into a finite product then follows coordinatewise (`continuousOn_pi`).
-/

set_option autoImplicit false

namespace Work.WilkiesH.Norm

theorem continuousOn_normMap_normSet {n : ℕ} (σ : Fin n → NormShape) (X : Set (Fin n → ℝ)) :
    ContinuousOn (normMap σ) (normSet σ X) := by
  rw [continuousOn_pi]
  intro i
  have hcoord : ContinuousOn (fun y : Fin n → ℝ => y i) (normSet σ X) :=
    (continuous_apply i).continuousOn
  cases hs : σ i with
  | pos =>
    have hfun : (fun y : Fin n → ℝ => normMap σ y i) = fun y => y i := by
      funext y; simp [normMap, shapeMap, hs]
    rw [hfun]; exact hcoord
  | neg =>
    have hfun : (fun y : Fin n → ℝ => normMap σ y i) = fun y => -(y i) := by
      funext y; simp [normMap, shapeMap, hs]
    rw [hfun]; exact hcoord.neg
  | big =>
    have hne : ∀ y ∈ normSet σ X, y i ≠ 0 := by
      intro y hy
      obtain ⟨w, ⟨_, hwPiece⟩, hwe⟩ := hy
      have h1 : w i ∈ Set.Ioi (1 : ℝ) := by simpa [shapeSet, hs] using hwPiece i
      have h2 : w i ≠ 0 := ne_of_gt (lt_trans one_pos h1)
      have hw : y i = (w i)⁻¹ := by rw [← hwe]; simp [normMap, shapeMap, hs]
      rw [hw]
      exact inv_ne_zero h2
    have hbig : ContinuousOn (fun y : Fin n → ℝ => (y i)⁻¹) (normSet σ X) :=
      ContinuousOn.inv₀ hcoord hne
    have hfun : (fun y : Fin n → ℝ => normMap σ y i) = fun y => (y i)⁻¹ := by
      funext y; simp [normMap, shapeMap, hs]
    rw [hfun]; exact hbig
  | bigNeg =>
    have hne : ∀ y ∈ normSet σ X, y i ≠ 0 := by
      intro y hy
      obtain ⟨w, ⟨_, hwPiece⟩, hwe⟩ := hy
      have h1 : w i ∈ Set.Iio (-1 : ℝ) := by simpa [shapeSet, hs] using hwPiece i
      have h2 : w i ≠ 0 := ne_of_lt (lt_trans h1 (by norm_num))
      have hw : y i = -(w i)⁻¹ := by rw [← hwe]; simp [normMap, shapeMap, hs]
      rw [hw]
      exact neg_ne_zero.mpr (inv_ne_zero h2)
    have hbig : ContinuousOn (fun y : Fin n → ℝ => -(y i)⁻¹) (normSet σ X) :=
      (ContinuousOn.inv₀ hcoord hne).neg
    have hfun : (fun y : Fin n → ℝ => normMap σ y i) = fun y => -(y i)⁻¹ := by
      funext y; simp [normMap, shapeMap, hs]
    rw [hfun]; exact hbig

end Work.WilkiesH.Norm
