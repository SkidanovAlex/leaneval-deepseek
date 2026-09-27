import Mathlib
import Submission.Work.Projection.TransverseDefs

set_option linter.style.haveILetI false

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

/-- The canonical splitting `pairEquiv n : ℝ^{2n} ≃ ℝ^n × ℝ^n` is smooth (it is linear, hence
continuous). -/
private lemma contDiff_pairEquiv (n : ℕ) : ContDiff ℝ ∞ ⇑(pairEquiv n) := by
  have h : ContDiff ℝ ∞ ⇑((pairEquiv n).toContinuousLinearEquiv) :=
    ContinuousLinearEquiv.contDiff _
  simpa using h

/-- `Work.Projection.pairParam e p q` (defined in `Submission.Work.Projection.TransverseDefs`)
is `C^1` on its domain `Work.Projection.pairDom e p q`, where the last coordinate of
`chartRep e q b - chartRep e p a` does not vanish.  Compare `Work.Projection.contDiffOn_immParam`
in `Submission.Work.Projection.dimH_badImmCharts`, the analogous statement for `immParam`. -/
theorem contDiffOn_pairParam {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ⊤ M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ⊤ e) (p q : M) :
    ContDiffOn ℝ 1 (pairParam e p q) (pairDom e p q) := by
  -- `⊤` (analytic order) is above `∞` (smooth order), which is what the helpers use.
  haveI : IsManifold (𝓡 n) ∞ M := IsManifold.of_le (m := ∞) (n := ⊤) le_top
  have he' : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e := he.of_le le_top
  -- The chartwise difference `pairZ e p q ab = chartRep e q ab.2 - chartRep e p ab.1`.
  have hZ : ContDiffOn ℝ ∞ (pairZ e p q) (pairDom e p q) := by
    have h : ContDiffOn ℝ ∞
        (fun yz : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          -(chartRep e p yz.1 - chartRep e q yz.2))
        {yz | yz.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
              yz.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target} :=
      (contDiffOn_diff (n := n) (k := 2 * n) e he' p q).neg
    refine (h.mono ?_).congr ?_
    · intro ab hb; exact ⟨hb.1, hb.2.1⟩
    · intro ab _
      simp only [pairZ]
      rw [neg_sub]
  -- `extract` is smooth where the last coordinate does not vanish, so `pairDir` is smooth.
  have hD : ContDiffOn ℝ ∞ (pairDir e p q) (pairDom e p q) := by
    have h := (contDiffOn_extract_inj (2 * n)).comp hZ (fun ab hb => hb.2.2)
    refine h.congr fun ab _ => ?_
    simp only [Function.comp_apply, pairDir]
  -- `pairParam` is `pairEquiv n` composed with `pairDir`, and `pairEquiv n` is linear.
  have hP : ContDiffOn ℝ ∞ (pairParam e p q) (pairDom e p q) := by
    have h := (contDiff_pairEquiv n).contDiffOn.comp hD (fun _ _ => Set.mem_univ _)
    refine h.congr fun ab _ => ?_
    simp only [Function.comp_apply, pairParam]
  exact hP.of_le (by norm_num)

end Work.Projection
