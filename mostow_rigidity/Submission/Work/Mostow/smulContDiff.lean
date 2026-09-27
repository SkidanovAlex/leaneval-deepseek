import Mathlib
import Submission.Work.Mostow.Hyper

/-!
# Smoothness of the `PO n 1`-action on the chart

`g • u = actO (rep g) u` and, unfolding `actO`,

`actO A u = WithLp.toLp 2 (fun i => tsign A * (mat A *ᵥ hlift u) (Sum.inl i))`.

The matrix `mat A` and the sign `tsign A` are *constants* here: the only dependence on `u` is
through the hyperboloid lift `hlift u = (u, √(1+‖u‖²))`, i.e. through the identity and the
smooth function `√(1+‖·‖²)` (smooth because `1 + ‖u‖² ≥ 1 > 0`).  Hence `actO A` is smooth
(`ContDiff ℝ 1`, in fact `C^∞`), with no hypothesis on `A` at all; in particular
`u ↦ g • u` is `ContDiff ℝ 1` for every `g : PO n 1`.

This is the smoothness clause of `HypIsometryProp`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- The time coordinate `u ↦ √(1+‖u‖²)` of the hyperboloid chart is `C¹`. -/
lemma smc_contDiff_tpart : ContDiff ℝ 1 (fun u : E n => tpart u) := by
  rw [show (fun u : E n => tpart u) = (fun u : E n => Real.sqrt (1 + ‖u‖ ^ 2)) from rfl]
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun u => by positivity)

/-- The hyperboloid lift `u ↦ (u, √(1+‖u‖²))` is `C¹`. -/
lemma smc_contDiff_hlift : ContDiff ℝ 1 (hlift (n := n)) := by
  rw [show hlift (n := n) = (fun u : E n => fun a : Fin n ⊕ Fin 1 => hlift u a) from rfl]
  rw [contDiff_pi]
  intro a
  rcases a with i | j
  · simpa [hlift] using
      (ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i))
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa [hlift] using smc_contDiff_tpart

/-- The `i`-th spatial coordinate of `mat A *ᵥ hlift u` is `C¹` in `u`. -/
lemma smc_contDiff_mulVec (A : O1 n) (i : Fin n) :
    ContDiff ℝ 1 (fun u : E n => (mat A *ᵥ hlift u) (Sum.inl i)) := by
  rw [show (fun u : E n => (mat A *ᵥ hlift u) (Sum.inl i))
      = (fun u : E n => ∑ j : Fin n ⊕ Fin 1, mat A (Sum.inl i) j * hlift u j) from by
    funext u; rw [Matrix.mulVec_apply_eq_sum]]
  refine ContDiff.sum (fun j _ => ?_)
  exact contDiff_const.mul ((contDiff_pi.mp smc_contDiff_hlift) j)

/-- The chart action `actO A` of a single matrix is `C¹`. -/
theorem smc_contDiff_actO (A : O1 n) : ContDiff ℝ 1 (fun u : E n => actO A u) := by
  have hcoord : ContDiff ℝ 1 (fun u : E n => fun i : Fin n =>
      tsign A * ((mat A) *ᵥ (hlift u)) (Sum.inl i)) := by
    rw [contDiff_pi]
    intro i
    exact contDiff_const.mul (smc_contDiff_mulVec A i)
  have hcomp := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff.comp hcoord
  convert hcomp using 1
  ext u i
  rfl

/-- The `PO n 1`-action on the chart is `C¹`. -/
theorem smulContDiff (n : ℕ) (hA : POActionProp n) (g : PO n 1) :
    ContDiff ℝ 1 (fun u : E n => g • u) := by
  change ContDiff ℝ 1 (fun u : E n => actO (rep g) u)
  exact smc_contDiff_actO (rep g)

end

end Work.Mostow
