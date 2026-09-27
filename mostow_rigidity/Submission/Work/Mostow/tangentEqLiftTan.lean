import Mathlib
import Submission.Work.Mostow.localIsomDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- The Minkowski pairing of a vector `W` with the hyperboloid point over `p` is the Euclidean
inner product of the spatial parts minus `tcoord W * tpart p`. -/
theorem mink_hlift_eq {n : ℕ} (p : E n) (W : Fin n ⊕ Fin 1 → ℝ) :
    mink_localIsomDefs W (hlift p) = (∑ i : Fin n, W (Sum.inl i) * p i) - W (Sum.inr 0) * tpart p := by
  simp only [mink_localIsomDefs, hlift, Sum.elim_inl, Sum.elim_inr]

/-- The Euclidean inner product of the chart points in terms of ambient coordinates. -/
theorem inner_spatial {n : ℕ} (p : E n) (W : Fin n ⊕ Fin 1 → ℝ) :
    inner ℝ p (spatial W) = ∑ i : Fin n, p i * W (Sum.inl i) := by
  rw [PiLp.inner_apply]
  simp [spatial, mul_comm]

/-- A vector of the ambient Minkowski space which is Minkowski-orthogonal to the hyperboloid point
over `p` is the tangent lift at `p` of its own spatial part. -/
theorem tangentEqLiftTan {n : ℕ} (p : E n) (W : Fin n ⊕ Fin 1 → ℝ) (h : mink_localIsomDefs W (hlift p) = 0) :
    W = liftTan p (spatial W) := by
  funext x
  rcases x with i | j
  · rfl
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    have hm : (∑ i : Fin n, W (Sum.inl i) * p i) - W (Sum.inr 0) * tpart p = 0 := by
      simpa only [mink_hlift_eq] using h
    have hS : W (Sum.inr 0) * tpart p = ∑ i : Fin n, W (Sum.inl i) * p i := by linarith
    have ht : tpart p ≠ 0 := ne_of_gt (tpart_pos p)
    simp only [liftTan, Sum.elim_inr, inner_spatial]
    rw [eq_div_iff ht, hS]
    simp only [mul_comm]

end Work.Mostow
