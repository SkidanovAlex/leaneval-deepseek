import Mathlib
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.ballConvexAux
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.segfunSpeed

/-!
# The time coordinate `tpart` along the explicit geodesic segment

`segfun p q s` is the chart expression of the point at distance `s` from `p` on the unit-speed
geodesic from `p` to `q`.  Its time coordinate (i.e. the function `tpart`) is the corresponding
convex combination of `tpart p` and `tpart q`:

`tpart (segfun p q s) = sinh (d - s)/sinh d * tpart p + sinh s/sinh d * tpart q`, `d = hdist p q`.

The proof goes through the hyperboloid: the ambient chord
`amb p q s = (sinh (d - s)/sinh d) • hlift p + (sinh s/sinh d) • hlift q`
satisfies `mink_localIsomDefs (amb p q s) (amb p q s) = -1` (this is `mink_amb_self`), so it is the lift of its
own chart point `spatial (amb p q s) = segfun p q s`; comparing time coordinates gives the claim.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- A vector of the ambient Minkowski space that lies on the upper sheet (`mink_localIsomDefs`-norm `-1`,
nonnegative time) is the lift of its own chart point. -/
lemma hlift_spatial_of_mink {W : Fin n ⊕ Fin 1 → ℝ} (hW : mink_localIsomDefs W W = -1)
    (ht : 0 ≤ tcoord W) : hlift (spatial W) = W := by
  have hsq : (tcoord W) ^ 2 = 1 + ‖spatial W‖ ^ 2 := by
    have h := mink_spatial W W
    rw [hW, real_inner_self_eq_norm_sq] at h
    simp only [tcoord] at h ⊢
    nlinarith
  have htcoord : tcoord W = tpart (spatial W) := by
    rw [tpart, ← hsq, Real.sqrt_sq ht]
  funext x
  rcases x with i | j
  · show hlift (spatial W) (Sum.inl i) = W (Sum.inl i)
    simp [hlift, spatial]
  · have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    show tpart (spatial W) = W (Sum.inr 0)
    rw [← htcoord]
    rfl

/-- The time coordinate of the ambient chord is the convex combination of the time coordinates
of the endpoints. -/
lemma tcoord_amb (p q : E n) (s : ℝ) :
    tcoord (amb p q s) = Real.sinh (hdist p q - s) / Real.sinh (hdist p q) * tpart p +
      Real.sinh s / Real.sinh (hdist p q) * tpart q := by
  simp [amb, tcoord_add, tcoord_smul, tcoord_hlift]

theorem tpartSegfun {n : ℕ} (p q : Submission.Mostow.E n) (s : ℝ)
    (hd : Real.sinh (Submission.Mostow.hdist p q) ≠ 0)
    (hs : s ∈ Set.Icc 0 (Submission.Mostow.hdist p q)) :
    Submission.Mostow.tpart (Work.Mostow.segfun p q s) =
      Real.sinh (Submission.Mostow.hdist p q - s) / Real.sinh (Submission.Mostow.hdist p q) *
        Submission.Mostow.tpart p +
      Real.sinh s / Real.sinh (Submission.Mostow.hdist p q) * Submission.Mostow.tpart q := by
  have hspos : 0 < Real.sinh (hdist p q) :=
    lt_of_le_of_ne (Real.sinh_nonneg_iff.mpr (hdist_nonneg p q)) (Ne.symm hd)
  have hA : 0 ≤ Real.sinh (hdist p q - s) / Real.sinh (hdist p q) :=
    div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith [hs.2])) (le_of_lt hspos)
  have hB : 0 ≤ Real.sinh s / Real.sinh (hdist p q) :=
    div_nonneg (Real.sinh_nonneg_iff.mpr hs.1) (le_of_lt hspos)
  have htc : 0 ≤ tcoord (amb p q s) := by
    rw [tcoord_amb]
    exact add_nonneg (mul_nonneg hA (le_of_lt (tpart_pos p))) (mul_nonneg hB (le_of_lt (tpart_pos q)))
  have hlift_eq : hlift (spatial (amb p q s)) = amb p q s :=
    hlift_spatial_of_mink (mink_amb_self p q s hd) htc
  have hkey : tpart (spatial (amb p q s)) = tcoord (amb p q s) := by
    rw [← tcoord_hlift (spatial (amb p q s)), hlift_eq]
  rw [← spatial_amb p q s, hkey, tcoord_amb]

end Work.Mostow
