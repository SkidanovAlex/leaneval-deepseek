import Mathlib
import Submission.Work.Diff.GE.rmPDeps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- The coordinate vector form of the Christoffel symbol of the Levi-Civita connection in the
chart at `x₀`.

`Submission.ChartCurv.chrB (lcOf (G t)) x₀ y a b` is the coordinate vector (in the model space `E`,
canonically identified with the tangent space via the chart trivialisation) of `∇_{σ_b} σ_a`, where
`σ_i` is the `i`-th coordinate frame vector of the chart at `x₀`.  The claim is that this vector is
obtained from the *lowered* Christoffel pairings
`koszulPair G x₀ a b k t y = ⟨∇_{σ_a} σ_b, σ_k⟩` by raising the index with the inverse Gram matrix of
the coordinate frame.

Usable route: `Work.Diff.EXT.eq_sum_frameVector_of_pairing` recovers a tangent vector from its
pairings with the frame, using the inverse Gram matrix
`Matrix.of (fun i j => (G t).inner y (σ_i y) (σ_j y))⁻¹` (which unfolds to `GramM`, hence to
`GramInv`); the pairings are `Work.Diff.GE.cGram_chrB_eq_koszulPair`; the frame map
`Submission.Geodesic.frameVector x₀ y` is linear (`frameVector_sum`) and injective on the chart
source (`Submission.ChartBounds.frameVector_eq_zero_iff` plus `frameVector_sub`), which turns the
equality of the frame images into the equality of the coordinate vectors.  (`hy` is used for the
injectivity and for `cGram_chrB_eq_koszulPair`.) -/
theorem chrB_eq_sum_gramInv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (a b : Fin (Module.finrank ℝ E)) :
    Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
        (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b)
      = ∑ k, (Matrix.mulVec (Work.Diff.GE.GramInv (I := I) G x₀ t y)
          (fun k ↦ Work.Diff.GE.koszulPair (I := I) G x₀ a b k t y)) k
          • Work.Diff.GE.cBasis (E := E) k := by
  classical
  -- The Gram matrix of the frame in `eq_sum_frameVector_of_pairing` is `GramM`, so its inverse is
  -- the raising matrix `GramInv`.
  have hmatrix : (Matrix.of (fun i j => (G t).inner y
      (Submission.Geodesic.frameVector (I := I) x₀ y (Module.finBasis ℝ E i))
      (Submission.Geodesic.frameVector (I := I) x₀ y (Module.finBasis ℝ E j))))⁻¹
      = Work.Diff.GE.GramInv (I := I) G x₀ t y := by
    rw [Work.Diff.GE.GramInv]
    congr 1
  -- The pairings of `∇_{σ_b}σ_a` with the frame are the lowered Christoffel symbols.
  have hv : ∀ k, (G t).inner y
      (Submission.Geodesic.frameVector (I := I) x₀ y
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
          (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b)))
      (Submission.Geodesic.frameVector (I := I) x₀ y (Module.finBasis ℝ E k))
      = Work.Diff.GE.koszulPair (I := I) G x₀ a b k t y := by
    intro k
    rw [← Work.Diff.GE.cGram_apply]
    exact Work.Diff.GE.cGram_chrB_eq_koszulPair G x₀ hy t a b k
  -- Recover the tangent vector `∇_{σ_b}σ_a` from its pairings with the frame.
  have hkey := Work.Diff.EXT.eq_sum_frameVector_of_pairing (I := I) (g := G t) hy
    (Submission.Geodesic.frameVector (I := I) x₀ y
      (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
        (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b)))
  have hkey' : (Submission.Geodesic.frameVector (I := I) x₀ y
      (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
        (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b)))
      = ∑ k, (Matrix.mulVec (Work.Diff.GE.GramInv (I := I) G x₀ t y)
          (fun k ↦ Work.Diff.GE.koszulPair (I := I) G x₀ a b k t y)) k
          • Submission.Geodesic.frameVector (I := I) x₀ y (Module.finBasis ℝ E k) := by
    simpa only [hmatrix, hv] using hkey
  -- The frame map is linear, so the raised combination of the frame vectors is the frame vector of
  -- the raised combination of the coordinate vectors.
  have hfinal : Submission.Geodesic.frameVector (I := I) x₀ y
        (∑ k, (Matrix.mulVec (Work.Diff.GE.GramInv (I := I) G x₀ t y)
          (fun k ↦ Work.Diff.GE.koszulPair (I := I) G x₀ a b k t y)) k
          • Work.Diff.GE.cBasis (E := E) k)
      = Submission.Geodesic.frameVector (I := I) x₀ y
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
          (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b)) := by
    rw [Submission.Geodesic.frameVector_sum, ← hkey']
  -- The frame map is injective on the chart source, so the coordinate vectors agree.
  have hV : (∑ k, (Matrix.mulVec (Work.Diff.GE.GramInv (I := I) G x₀ t y)
          (fun k ↦ Work.Diff.GE.koszulPair (I := I) G x₀ a b k t y)) k
          • Work.Diff.GE.cBasis (E := E) k)
      = Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
          (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b) := by
    have hz : Submission.Geodesic.frameVector (I := I) x₀ y
        ((∑ k, (Matrix.mulVec (Work.Diff.GE.GramInv (I := I) G x₀ t y)
          (fun k ↦ Work.Diff.GE.koszulPair (I := I) G x₀ a b k t y)) k
          • Work.Diff.GE.cBasis (E := E) k)
        - Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
          (Work.Diff.GE.cBasis (E := E) a) (Work.Diff.GE.cBasis (E := E) b)) = 0 := by
      rw [Submission.ChartCurv.frameVector_sub, hfinal, sub_self]
    exact sub_eq_zero.mp ((Submission.ChartBounds.frameVector_eq_zero_iff (I := I) hy _).mp hz)
  exact hV.symm

end Work.Diff.GE
