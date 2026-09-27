import Mathlib
import Submission.Work.Projection.TransverseDefs
import Submission.Work.Projection.dimH_badImmCharts

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

/-- The chart representation of a smooth map at `p` is continuous on the target of the chart at
`p`; this is `Work.Projection.contDiffOn_chartRep` (from
`Submission.Work.Projection.dimH_badImmCharts`) in the smooth (`C^∞`) regularity, which is the
regularity actually needed for continuity. -/
private lemma continuousOn_chartRep_of_contMDiff {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ⊤ M]
    (f : M → EuclideanSpace ℝ (Fin (k + 1)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ⊤ f) (p : M) :
    ContinuousOn (chartRep f p) (chartAt (EuclideanSpace ℝ (Fin n)) p).target := by
  -- An analytic (`⊤` = `ω`) structure is in particular smooth (`∞`).
  have : IsManifold (𝓡 n) ∞ M := IsManifold.of_le (m := ∞) (n := ⊤) le_top
  exact (contDiffOn_chartRep (n := n) (k := k) f (ContMDiff.of_le hf le_top) p).continuousOn

/-- `Work.Projection.pairDom e p q` (defined in `Submission.Work.Projection.TransverseDefs`) is
open: it is the set of pairs of chart coordinates whose induced difference has nonvanishing last
coordinate.  The smoothness hypothesis on `e` is available for the continuity of the chart
representations. -/
theorem isOpen_pairDom {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ⊤ M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ⊤ e) (p q : M) :
    IsOpen (pairDom e p q) := by
  -- The two chart representations are continuous on the respective chart targets.
  have hp : ContinuousOn (chartRep (n := n) (k := 2 * n) e p)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target :=
    continuousOn_chartRep_of_contMDiff (k := 2 * n) e he p
  have hq : ContinuousOn (chartRep (n := n) (k := 2 * n) e q)
      (chartAt (EuclideanSpace ℝ (Fin n)) q).target :=
    continuousOn_chartRep_of_contMDiff (k := 2 * n) e he q
  -- Hence their difference `pairZ` is continuous on the product of the chart targets.
  have hZ : ContinuousOn (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      chartRep (n := n) (k := 2 * n) e q ab.2 - chartRep (n := n) (k := 2 * n) e p ab.1)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).target ×ˢ
        (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :=
    (hq.comp continuousOn_snd (fun x hx => hx.2)).sub
      (hp.comp continuousOn_fst (fun x hx => hx.1))
  -- and so is its last coordinate.
  have hlast : ContinuousOn (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (chartRep (n := n) (k := 2 * n) e q ab.2 - chartRep (n := n) (k := 2 * n) e p ab.1)
        (Fin.last (2 * n)))
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).target ×ˢ
        (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (2 * n + 1)) (Fin.last (2 * n)) :
        EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] ℝ).continuous.comp_continuousOn hZ
  -- `pairDom` is exactly the intersection of the (open) product of the chart targets with the
  -- preimage of `{0}ᶜ` under that last coordinate.
  have hset : pairDom e p q =
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).target ×ˢ
        (chartAt (EuclideanSpace ℝ (Fin n)) q).target) ∩
      (fun ab : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (chartRep (n := n) (k := 2 * n) e q ab.2 - chartRep (n := n) (k := 2 * n) e p ab.1)
          (Fin.last (2 * n))) ⁻¹' ({0}ᶜ : Set ℝ) := by
    ext ab
    simp only [pairDom, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff, pairZ]
    tauto
  rw [hset]
  exact hlast.isOpen_inter_preimage
    ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_target.prod
      (chartAt (EuclideanSpace ℝ (Fin n)) q).open_target)
    (isOpen_compl_singleton (x := (0 : ℝ)))

end Work.Projection
