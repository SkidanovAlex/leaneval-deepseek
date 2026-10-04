import Mathlib
import Submission.Work.Diff.STE.deTurck.deTurckVec_chartComp
import Submission.Work.Diff.EXT.eq_sum_frameVector_of_pairing
import Submission.Work.Diff.STE.DeTurckField

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.deTurck

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option maxHeartbeats 400000

/-
Work.Diff.STE.DeTurck.deTurckVec g gbar is the frame-free DeTurck field W(g) = tr_g(∇^g - ∇^gbar),
defined as the metric trace of the connection difference connDiff g gbar.
Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ p k is the classical coordinate expression
∑_{ab} γ^{ab}(Γ^k_{ab} - Γ̃^k_{ab}) of that field in the chart at x₀, and Work.Diff.GE.cFrame x₀ k is
the coordinate frame field of that chart. The claim below says the frame-free field is the linear
combination of the chart frame with those components: the pointwise bridge used to prove smoothness
of deTurckVec (and its canonicity).

INGREDIENTS ALREADY PROVED (the proof is an assembly):
* Work.Diff.STE.deTurck.deTurckVec_chartComp : for p ∈ (chartAt H x₀).source,
  ∑ j, GramInv (fun _ => g) x₀ 0 p k j * g.inner p (deTurckVec g gbar p) (cFrame x₀ j p)
     = deTurckChartComp g gbar x₀ p k.
* Work.Diff.EXT.eq_sum_frameVector_of_pairing : a tangent vector is the (Gram⁻¹ *ᵥ pairings)
  combination of the chart frame vectors frameVector x₀ p (finBasis i).
* Work.Diff.GE.cFrame_apply, GramInv = (GramM)⁻¹, GramM = mComp,
  mComp G x₀ i j t y = (G t).inner y (cFrame x₀ i y) (cFrame x₀ j y), Matrix.mulVec_apply_eq_sum.
-/
theorem deTurckVec_eq_sum_chartComp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g gbar : Submission.Diff.SMet I M) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) :
    Work.Diff.STE.DeTurck.deTurckVec g gbar p
      = ∑ k : Fin (Module.finrank ℝ E),
          Work.Diff.STE.DeTurck.deTurckChartComp g gbar x₀ p k
            • Work.Diff.GE.cFrame (I := I) x₀ k p := by
  classical
  -- The chart coordinate frame at `p` as a basis of `T_pM`.
  set e : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    Work.Diff.EXT.frameBasis (I := I) x₀ p hp with he
  have hcv : ∀ i : Fin (Module.finrank ℝ E),
      e i = Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E i) := by
    intro i
    rw [he, Work.Diff.EXT.frameBasis_apply]
  have hcf : ∀ i : Fin (Module.finrank ℝ E), e i = Work.Diff.GE.cFrame (I := I) x₀ i p :=
    fun i => by rw [hcv i]; rfl
  -- Recover the DeTurck field from its pairings with the chart frame.
  have hFU := Work.Diff.EXT.eq_sum_frameVector_of_pairing (I := I) (g := g) hp
    (Work.Diff.STE.DeTurck.deTurckVec g gbar p)
  simp only [← hcv] at hFU
  -- The Gram matrix of `e` is `GramM`, hence its inverse is `GramInv`.
  have hGram : (Matrix.of fun i j => g.inner p (e i) (e j))
      = Work.Diff.GE.GramM (I := I) (fun _ : ℝ => g) x₀ 0 p := by
    ext i j
    rw [Matrix.of_apply]
    show g.inner p (e i) (e j) = Work.Diff.GE.mComp (I := I) (fun _ : ℝ => g) x₀ i j 0 p
    rw [hcf i, hcf j]
    rfl
  have hγ : (Matrix.of fun i j => g.inner p (e i) (e j))⁻¹
      = Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 p := by
    rw [Work.Diff.GE.GramInv, hGram]
  rw [hγ] at hFU
  -- The DeTurck field is the `GramInv *ᵥ pairings` combination of the chart frame.
  rw [hFU]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcoe : (Matrix.mulVec (Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 p)
      (fun j => g.inner p (Work.Diff.STE.DeTurck.deTurckVec g gbar p) (e j))) k
      = Work.Diff.STE.DeTurck.deTurckChartComp (I := I) g gbar x₀ p k := by
    rw [Matrix.mulVec_apply_eq_sum]
    rw [← Work.Diff.STE.deTurck.deTurckVec_chartComp (I := I) g gbar x₀ k hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcf j]
  rw [hcoe, hcf k]

end Work.Diff.STE.deTurck
