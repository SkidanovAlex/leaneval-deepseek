import Mathlib
import Submission.Work.Diff.EXT.ricCore
import Submission.Work.Diff.EXT.kosDefs
import Submission.Work.Diff.EXT.eq_sum_frameVector_of_pairing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `EXT` area: expanding a covariant derivative in the chart frame

Fix a chart centre `x`.  The results of `kosDefs` express the *pairings* of `∇_X Z` with the
coordinate frame of the chart at `x`; here we invert those pairings with the Gram matrix, obtaining
the *value* of `∇_X Z` as an explicit linear combination of the frame:

* `fr x i` is the `i`-th coordinate frame field at `x`;
* `gramM g x y` is the Gram matrix of the frame at `y` for the metric `g`;
* `reconCoef G x Xdir Z j t y` is the `j`-th coefficient in that expansion for `∇_{Xdir} Z`
  (Koszul pairings pushed through the inverse Gram matrix);
* `lcOf_eq_sum_reconCoef` is the resulting identity,
  `∇_{Xdir} Z (y) = Σ_j reconCoef j • fr j (y)`.

The coefficients are explicit, so their (joint) smoothness can be read off from the smoothness of
the Koszul pairings and of the inverse Gram matrix.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The `i`-th coordinate frame field of the chart at `x`: the tangent vector field whose
coordinates in that chart are the constant vector `Module.finBasis ℝ E i`. -/
noncomputable def fr (x : M) (i : Fin (Module.finrank ℝ E)) : Π y : M, TangentSpace I y :=
  fun y => Submission.Geodesic.frameVector (I := I) x y (Module.finBasis ℝ E i)

/-- The Gram matrix of the coordinate frame of the chart at `x`, for the metric `g`, at `y`. -/
noncomputable def gramM (g : SMet I M) (x y : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j => g.inner y (fr (I := I) x i y) (fr (I := I) x j y)

/-- The `j`-th coefficient of `∇_{Xdir} Z` in the coordinate frame of the chart at `x`: the Koszul
pairings pushed through the inverse Gram matrix. -/
noncomputable def reconCoef (G : ℝ → SMet I M) (x : M)
    (Xdir Z : Π y : M, TangentSpace I y) (j : Fin (Module.finrank ℝ E)) (t : ℝ) (y : M) : ℝ :=
  Matrix.mulVec ((gramM (I := I) (G t) x y))⁻¹
    (fun i => kosGen (I := I) G Xdir Z (fr (I := I) x i) t y) j

/-- **The Gram matrix of the coordinate frame at the base point is invertible** (it is the matrix
of a positive definite form in a basis). -/
lemma gramM_det_ne_zero (g : SMet I M) (x : M) : (gramM (I := I) g x x).det ≠ 0 := by
  classical
  have hb : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := mem_chart_source H x
  let L : E ≃ₗ[ℝ] TangentSpace I x :=
    (Bundle.Trivialization.linearEquivAt ℝ (trivializationAt E (TangentSpace I) x) x hb).symm
  have hL : ∀ v : E, L v = Submission.Geodesic.frameVector (I := I) x x v := by
    intro v
    rw [Bundle.Trivialization.linearEquivAt_symm_apply]
    exact (Bundle.Trivialization.symmL_apply (R := ℝ)
      (trivializationAt E (TangentSpace I) x) hb v).symm
  have hfr : ∀ i : Fin (Module.finrank ℝ E), fr (I := I) x i x = L (Module.finBasis ℝ E i) := by
    intro i
    show Submission.Geodesic.frameVector (I := I) x x (Module.finBasis ℝ E i) = L _
    rw [hL]
  have hentry : ∀ i j : Fin (Module.finrank ℝ E),
      gramM (I := I) g x x i j =
        g.inner x (L (Module.finBasis ℝ E i)) (L (Module.finBasis ℝ E j)) :=
    fun i j => by simp only [gramM, Matrix.of_apply, hfr]
  -- linearity of the metric in its second argument along a finite sum
  have h2 : ∀ (u : TangentSpace I x) (d : Fin (Module.finrank ℝ E) → ℝ)
      (v : Fin (Module.finrank ℝ E) → TangentSpace I x),
      g.inner x u (∑ i, d i • v i) = ∑ i, d i * g.inner x u (v i) := by
    intro u d v
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  -- the quadratic form of the Gram matrix in coordinates
  have key : ∀ d : Fin (Module.finrank ℝ E) → ℝ,
      g.inner x (∑ i, d i • L (Module.finBasis ℝ E i))
          (∑ j, d j • L (Module.finBasis ℝ E j))
        = ∑ j, d j * (∑ i, d i * gramM (I := I) g x x j i) := by
    intro d
    calc g.inner x (∑ i, d i • L (Module.finBasis ℝ E i))
          (∑ j, d j • L (Module.finBasis ℝ E j))
        = ∑ j, d j * g.inner x (∑ i, d i • L (Module.finBasis ℝ E i))
            (L (Module.finBasis ℝ E j)) := h2 _ _ _
      _ = ∑ j, d j * (∑ i, d i * g.inner x (L (Module.finBasis ℝ E j))
            (L (Module.finBasis ℝ E i))) := by
            refine Finset.sum_congr rfl fun j _ => congrArg (fun t => d j * t) ?_
            rw [g.symm x]
            exact h2 _ _ _
      _ = ∑ j, d j * (∑ i, d i * gramM (I := I) g x x j i) := by
            refine Finset.sum_congr rfl fun j _ => congrArg (fun t => d j * t) ?_
            exact Finset.sum_congr rfl fun i _ => by rw [hentry j i]
  have hLsum : ∀ d : Fin (Module.finrank ℝ E) → ℝ,
      (∑ i, d i • L (Module.finBasis ℝ E i)) = L (∑ i, d i • Module.finBasis ℝ E i) := by
    intro d
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  -- the Gram matrix is injective as a linear map
  have hinj : Function.Injective (Matrix.mulVec (gramM (I := I) g x x)) := by
    intro z w hzw
    have h0 : Matrix.mulVec (gramM (I := I) g x x) (z - w) = 0 := by
      rw [Matrix.mulVec_sub, hzw, sub_self]
    have hcoord : ∀ j, (∑ i, (z - w) i * gramM (I := I) g x x j i) = 0 := by
      intro j
      have h1 := congrFun h0 j
      rw [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
    have hz : (∑ i, (z - w) i • L (Module.finBasis ℝ E i)) = 0 := by
      by_contra hne
      have hpos : 0 < g.inner x (∑ i, (z - w) i • L (Module.finBasis ℝ E i))
          (∑ i, (z - w) i • L (Module.finBasis ℝ E i)) := g.pos x _ hne
      have hq : g.inner x (∑ i, (z - w) i • L (Module.finBasis ℝ E i))
          (∑ i, (z - w) i • L (Module.finBasis ℝ E i)) = 0 := by
        rw [key (z - w)]
        exact Finset.sum_eq_zero fun j _ => by rw [hcoord j, mul_zero]
      rw [hq] at hpos
      exact lt_irrefl 0 hpos
    have hzero : (∑ i, (z - w) i • Module.finBasis ℝ E i) = 0 := by
      have h1 : L (∑ i, (z - w) i • Module.finBasis ℝ E i) = 0 := by
        rw [← hLsum (z - w)]
        exact hz
      exact L.injective (by rw [h1, map_zero])
    have hd : (z - w) = 0 := by
      funext i
      exact (Fintype.linearIndependent_iff.mp (Module.finBasis ℝ E).linearIndependent)
        (fun i => (z - w) i) hzero i
    exact sub_eq_zero.mp hd
  have hunit : IsUnit (gramM (I := I) g x x) := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdetunit : IsUnit (gramM (I := I) g x x).det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  intro h0
  exact not_isUnit_zero (h0 ▸ hdetunit)

/-- **Expansion of `∇_{Xdir} Z` in the coordinate frame.**  For `y` in the chart at `x` and
sections `Xdir`, `Z` smooth at `y`, the covariant derivative `∇_{Xdir} Z` at `y` is the linear
combination of the frame vectors with coefficients `reconCoef`. -/
lemma lcOf_eq_sum_reconCoef (G : ℝ → SMet I M) (x : M)
    (Xdir Z : Π y : M, TangentSpace I y) (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x).source)
    (hX : SmoothFieldAt I M Xdir y) (hZ : SmoothFieldAt I M Z y) :
    lcOf (G t) Z y (Xdir y)
      = ∑ j, reconCoef (I := I) G x Xdir Z j t y • fr (I := I) x j y := by
  classical
  have hpair : ∀ i : Fin (Module.finrank ℝ E),
      (G t).inner y (lcOf (G t) Z y (Xdir y))
          (Submission.Geodesic.frameVector (I := I) x y (Module.finBasis ℝ E i))
        = kosGen (I := I) G Xdir Z (fr (I := I) x i) t y := by
    intro i
    have hsm : SmoothFieldAt I M (fr (I := I) x i) y := by
      have h := contMDiffAt_frameVector (I := I) x (Module.finBasis ℝ E i) hy
      simpa [SmoothFieldAt, fr] using h
    exact lcOf_pairing_eq_kosGen (I := I) G Xdir Z (fr (I := I) x i) t hX hZ
      (by simpa [SmoothFieldAt] using hsm)
  have hmain := eq_sum_frameVector_of_pairing (I := I) (g := G t) hy
    (w := lcOf (G t) Z y (Xdir y))
  have hfun : (fun k => (G t).inner y (lcOf (G t) Z y (Xdir y))
        (Submission.Geodesic.frameVector (I := I) x y (Module.finBasis ℝ E k)))
      = fun i => kosGen (I := I) G Xdir Z (fr (I := I) x i) t y := funext hpair
  rw [hfun] at hmain
  simpa [reconCoef, gramM, fr] using hmain

end

end Work.Diff.EXT
