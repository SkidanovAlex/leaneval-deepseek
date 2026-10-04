import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.EXT.chartRic_partial_jet
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.cGram_chrB_eq_koszulPair
import Submission.Work.Diff.GE.koszul
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.T.mvfderiv_frameVector_real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]

/-- The coordinates `Γ^p_{ab}` of the Christoffel vector `∇_{σ_a}σ_b` contracted with the Gram
matrix reproduce the metric pairing of `∇_{σ_a}σ_b`. -/
theorem cmfb_sum_cGam_mul_GramM_eq
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (a b k : Fin (Module.finrank ℝ E)) :
    (∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G t) x₀ y p a b * Work.Diff.GE.GramM G x₀ t y p k)
      = Work.Diff.GE.cGram (G t) x₀ y
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
            (Module.finBasis ℝ E b) (Module.finBasis ℝ E a))
          (Module.finBasis ℝ E k) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨(G t).inner, (G t).contMDiff, fun _ _ _ => rfl⟩
  rw [Work.Diff.GE.cGram_eq_sum_coord (I := I) G x₀ hy t
    (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
      (Module.finBasis ℝ E b) (Module.finBasis ℝ E a)) k]
  exact Finset.sum_congr rfl (fun p _ => rfl)

/-- Swapping the two metric slots of a coefficient does not change its derivative. -/
theorem cmfb_mvfderiv_metric_comm
    (G : ℝ → Submission.Diff.SMet I M) (x₀ y : M) (t : ℝ)
    (u v w : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun q : M => (G t).inner q
          (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E u))
          (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E v))) y
        (Submission.Geodesic.frameVector (I := I) x₀ y (Module.finBasis ℝ E w))
      = mvfderiv I (fun q : M => (G t).inner q
          (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E v))
          (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E u))) y
        (Submission.Geodesic.frameVector (I := I) x₀ y (Module.finBasis ℝ E w)) := by
  have hf : (fun q : M => (G t).inner q
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E u))
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E v)))
      = (fun q : M => (G t).inner q
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E v))
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E u))) := by
    funext q
    exact (G t).symm q _ _
  rw [hf]

/-- The Koszul Christoffel pairing is symmetric in its first two indices. -/
theorem cmfb_koszulPair_comm
    (G : ℝ → Submission.Diff.SMet I M) (x₀ y : M) (t : ℝ)
    (a b c : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.koszulPair (I := I) G x₀ a b c t y
      = Work.Diff.GE.koszulPair (I := I) G x₀ b a c t y := by
  simp only [Work.Diff.GE.koszulPair, Work.Diff.GE.cFrame_apply]
  rw [cmfb_mvfderiv_metric_comm (I := I) G x₀ y t b c a,
    cmfb_mvfderiv_metric_comm (I := I) G x₀ y t c a b,
    cmfb_mvfderiv_metric_comm (I := I) G x₀ y t a b c]
  ring

/-- **Koszul combination.**  The sum of the Koszul pairings `Γ_{mij} + Γ_{mji}` is the first
coordinate derivative of the metric coefficient `g_{ij}`. -/
theorem cmfb_koszulPair_add_swap
    (G : ℝ → Submission.Diff.SMet I M) (x₀ y : M) (t : ℝ)
    (m i j : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.koszulPair (I := I) G x₀ m i j t y
      + Work.Diff.GE.koszulPair (I := I) G x₀ m j i t y
      = mvfderiv I (fun q : M => (G t).inner q
            (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E i))
            (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E j))) y
          (Submission.Geodesic.frameVector (I := I) x₀ y (Module.finBasis ℝ E m)) := by
  simp only [Work.Diff.GE.koszulPair, Work.Diff.GE.cFrame_apply]
  rw [cmfb_mvfderiv_metric_comm (I := I) G x₀ y t j i m,
    cmfb_mvfderiv_metric_comm (I := I) G x₀ y t j m i,
    cmfb_mvfderiv_metric_comm (I := I) G x₀ y t i m j]
  ring

theorem chartMat_fderiv_basis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j m : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
        (Module.finBasis ℝ E m)
      = ∑ p : Fin (Module.finrank ℝ E),
          (Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m i
              * Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) p j
            + Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m j
              * Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i p) := by
  let p : M := (extChartAt I x₀).symm y
  have hp : p ∈ (chartAt H x₀).source := by
    have h1 : p ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have hpy : (extChartAt I x₀) p = y := (extChartAt I x₀).right_inv hy
  have hL : fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
        (Module.finBasis ℝ E m)
      = mvfderiv I (fun q : M => (G t).inner q
            (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E i))
            (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E j))) p
          (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E m)) := by
    have hmd : MDifferentiableAt I 𝓘(ℝ,ℝ)
        (fun q : M => (G t).inner q
          (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E i))
          (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E j))) p :=
      (contMDiffAt_metric_coeff (I := I) (G t) x₀ hp i j).mdifferentiableAt (by simp)
    have h := Work.Diff.T.mvfderiv_frameVector_real (I := I) x₀ hp
      (g := fun q : M => (G t).inner q
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E i))
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E j)))
      hmd (Module.finBasis ℝ E m)
    rw [hpy] at h
    rw [h]
    refine congrArg (fun f : E → ℝ => fderiv ℝ f y (Module.finBasis ℝ E m)) ?_
    funext z
    simp only [Work.Diff.EXT.chartMat, Work.Diff.EXT.chartMatFun]
  have hK := cmfb_koszulPair_add_swap (I := I) G x₀ p t m i j
  have hS1 : (∑ q : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G t) x₀ p q m i * Work.Diff.GE.GramM G x₀ t p q j)
      = Work.Diff.GE.cGram (G t) x₀ p
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ p
            (Module.finBasis ℝ E i) (Module.finBasis ℝ E m))
          (Module.finBasis ℝ E j) :=
    cmfb_sum_cGam_mul_GramM_eq (I := I) G x₀ t hp m i j
  have hS2 : (∑ q : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G t) x₀ p q m j * Work.Diff.GE.GramM G x₀ t p i q)
      = Work.Diff.GE.cGram (G t) x₀ p
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ p
            (Module.finBasis ℝ E j) (Module.finBasis ℝ E m))
          (Module.finBasis ℝ E i) := by
    have hsw : (∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G t) x₀ p q m j * Work.Diff.GE.GramM G x₀ t p i q)
        = ∑ q : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G t) x₀ p q m j * Work.Diff.GE.GramM G x₀ t p q i := by
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [show Work.Diff.GE.GramM (I := I) G x₀ t p i q
            = Work.Diff.GE.GramM (I := I) G x₀ t p q i from
          Work.Diff.GE.mComp_comm (I := I) G x₀ i q t p]
    rw [hsw]
    exact cmfb_sum_cGam_mul_GramM_eq (I := I) G x₀ t hp m j i
  have hT1 : Work.Diff.GE.cGram (G t) x₀ p
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ p
          (Module.finBasis ℝ E i) (Module.finBasis ℝ E m))
        (Module.finBasis ℝ E j)
      = Work.Diff.GE.koszulPair (I := I) G x₀ m i j t p := by
    rw [Work.Diff.GE.cGram_chrB_eq_koszulPair (I := I) G x₀ hp t i m j]
    exact cmfb_koszulPair_comm (I := I) G x₀ p t i m j
  have hT2 : Work.Diff.GE.cGram (G t) x₀ p
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ p
          (Module.finBasis ℝ E j) (Module.finBasis ℝ E m))
        (Module.finBasis ℝ E i)
      = Work.Diff.GE.koszulPair (I := I) G x₀ m j i t p := by
    rw [Work.Diff.GE.cGram_chrB_eq_koszulPair (I := I) G x₀ hp t j m i]
    exact cmfb_koszulPair_comm (I := I) G x₀ p t j m i
  have hsum : (∑ q : Fin (Module.finrank ℝ E),
        (Work.Diff.GE.cGam (G t) x₀ p q m i * Work.Diff.GE.GramM G x₀ t p q j
          + Work.Diff.GE.cGam (G t) x₀ p q m j * Work.Diff.GE.GramM G x₀ t p i q))
      = Work.Diff.GE.cGram (G t) x₀ p
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ p
            (Module.finBasis ℝ E i) (Module.finBasis ℝ E m))
          (Module.finBasis ℝ E j)
        + Work.Diff.GE.cGram (G t) x₀ p
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ p
            (Module.finBasis ℝ E j) (Module.finBasis ℝ E m))
          (Module.finBasis ℝ E i) := by
    rw [Finset.sum_add_distrib, hS1, hS2]
  calc fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
        (Module.finBasis ℝ E m)
      = mvfderiv I (fun q : M => (G t).inner q
            (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E i))
            (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E j))) p
          (Submission.Geodesic.frameVector (I := I) x₀ p (Module.finBasis ℝ E m)) := hL
    _ = Work.Diff.GE.koszulPair (I := I) G x₀ m i j t p
          + Work.Diff.GE.koszulPair (I := I) G x₀ m j i t p := hK.symm
    _ = Work.Diff.GE.cGram (G t) x₀ p
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ p
            (Module.finBasis ℝ E i) (Module.finBasis ℝ E m))
          (Module.finBasis ℝ E j)
        + Work.Diff.GE.cGram (G t) x₀ p
          (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ p
            (Module.finBasis ℝ E j) (Module.finBasis ℝ E m))
          (Module.finBasis ℝ E i) := by rw [hT1, hT2]
    _ = ∑ q : Fin (Module.finrank ℝ E),
          (Work.Diff.GE.cGam (G t) x₀ p q m i * Work.Diff.GE.GramM G x₀ t p q j
            + Work.Diff.GE.cGam (G t) x₀ p q m j * Work.Diff.GE.GramM G x₀ t p i q) :=
        hsum.symm

end Work.Diff.EXT
