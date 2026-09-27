import Mathlib
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.StabLift

/-!
# The linear part of an isometry of `ℍⁿ` fixing the base point

For `g : PO n 1` whose chart action fixes the base point `0 : E n = ℍⁿ`, the chart action
`u ↦ g • u` is *linear*: it is the restriction of a linear isometry of `E n`.

The point is purely matrix-theoretic.  Writing `A = rep g` and `M = mat A`, the action on the
chart is

`actO A u = WithLp.toLp 2 (fun i => tsign A * (M.mulVec (hlift u)) (Sum.inl i))`

(`Submission.Mostow.actO`) while `hlift u = (u, tpart u)`.  The hypothesis `actO A 0 = 0` forces
the space–time column entries `M (Sum.inl i) (Sum.inr 0)` to vanish, so `M.mulVec (hlift u)` has
space part `B.mulVec u` for the spatial block `B i j = M (Sum.inl i) (Sum.inl j)`.  Hence
`actO A u = tsign A • ((linSpatBlock A).toEuclideanLin u)`, which is visibly linear.

That `tsign A • (linSpatBlock A).toEuclideanLin` is an *isometry* follows from
`Submission.Mostow.Hyper.cc_actO`: `cc (actO A u) (actO A v) = cc u v`, i.e. the cosh-kernel is
preserved.  Combining with `actO A 0 = 0` (so that `tpart (actO A u) = tpart u`) gives
`⟪actO A u, actO A v⟫ = ⟪u, v⟫`.
-/

open Submission.Mostow LeanEval.Geometry.MostowRigidity

namespace Work.Mostow

noncomputable section

variable {n : ℕ}

/-- The spatial block `(i,j) ↦ mat A (Sum.inl i) (Sum.inl j)` of `mat A`. -/
def linSpatBlock (A : O1 n) : Matrix (Fin n) (Fin n) ℝ := fun i j => mat A (Sum.inl i) (Sum.inl j)

/-- If the space–time column of `mat A` vanishes, then the chart action of `A` is the linear map
`tsign A • (linSpatBlock A).toEuclideanLin`. -/
lemma actO_eq_of_col (A : O1 n) (hcol : ∀ i : Fin n, mat A (Sum.inl i) (Sum.inr 0) = 0)
    (u : E n) :
    actO A u = tsign A • ((linSpatBlock A).toEuclideanLin u) := by
  ext i
  rw [show (actO A u) i = tsign A * Matrix.mulVec (mat A) (hlift u) (Sum.inl i) from rfl]
  rw [show (tsign A • ((linSpatBlock A).toEuclideanLin u) : E n) i
        = tsign A * ((linSpatBlock A).toEuclideanLin u) i from rfl]
  congr 1
  rw [show ((linSpatBlock A).toEuclideanLin u) i = ∑ j, linSpatBlock A i j * u j from by
    rw [show ((linSpatBlock A).toEuclideanLin u) i
        = (WithLp.ofLp ((linSpatBlock A).toEuclideanLin u)) i from rfl]
    rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]; rfl]
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  simp only [Fin.sum_univ_one, hlift]
  simp only [linSpatBlock]
  rw [hcol]
  simp

/-- An isometry of `ℍⁿ` fixing the base point acts linearly in the chart. -/
theorem linPartExists (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (hg : g • (0 : Submission.Mostow.E n) = 0) :
    ∃ R : Submission.Mostow.E n ≃ₗᵢ[ℝ] Submission.Mostow.E n, ∀ u : Submission.Mostow.E n, g • u = R u := by
  -- The representative of `g` and the vanishing of the space–time column of its matrix.
  set A : O1 n := rep g
  have hA0 : actO A (0 : E n) = 0 := hg
  have hcol : ∀ i : Fin n, mat A (Sum.inl i) (Sum.inr 0) = 0 := by
    intro i
    have hc := congrArg (fun x : E n => x i) hA0
    simp only at hc
    rw [actO] at hc
    rw [hlift_zero, Matrix.mulVec_single_one] at hc
    exact (mul_eq_zero.mp hc).resolve_left (tsign_ne_zero A)
  -- The linear map which is the chart action.
  set f : E n →ₗ[ℝ] E n := tsign A • (linSpatBlock A).toEuclideanLin with hfdef
  have hfu : ∀ u : E n, f u = actO A u := by
    intro u
    rw [hfdef]
    exact (actO_eq_of_col A hcol u).symm
  -- `actO A` fixes `0`, hence preserves `tpart`.
  have ht : ∀ w : E n, tpart (actO A w) = tpart w := by
    intro w
    have h1 : Hyper.cc (actO A (0 : E n)) (actO A w) = Hyper.cc (0 : E n) w :=
      Hyper.cc_actO A 0 w
    rw [hA0, Hyper.cc_comm 0 (actO A w), Hyper.cc_zero, Hyper.cc_comm 0 w,
      Hyper.cc_zero] at h1
    exact h1
  -- `f` preserves the inner product.
  have hinner : ∀ u v : E n, inner ℝ (f u) (f v) = inner ℝ u v := by
    intro u v
    rw [hfu u, hfu v]
    have h := Hyper.cc_actO A u v
    simp only [Hyper.cc] at h
    rw [ht u, ht v] at h
    linarith
  have hinj : Function.Injective f := (f.isometryOfInner hinner).injective
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hinj
  refine ⟨LinearIsometryEquiv.ofSurjective (f.isometryOfInner hinner) hsurj, fun u => ?_⟩
  show g • u = f u
  rw [hfu u]
  rfl

end

end Work.Mostow
