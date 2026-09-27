import Mathlib
import Submission.Work.Projection.TransverseDefs
import Submission.Work.Projection.contDiffOn_pairParam

set_option linter.style.haveILetI false

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

/-- The canonical splitting `pairEquiv n : ℝ^{2n} ≃ ℝ^n × ℝ^n` is smooth (it is linear, hence
continuous). -/
private lemma contDiff_pairEquiv_smooth (n : ℕ) : ContDiff ℝ ∞ ⇑(pairEquiv n) := by
  have h : ContDiff ℝ ∞ ⇑((pairEquiv n).toContinuousLinearEquiv) :=
    ContinuousLinearEquiv.contDiff _
  simpa using h

/-- `Work.Projection.pairParam e p q` (defined in `Submission.Work.Projection.TransverseDefs`
with the *smooth* (`C^∞`) manifold structure, i.e. the order `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`) is
`C^1` on its domain `Work.Projection.pairDom e p q`.  This is identical to
`Work.Projection.contDiffOn_pairParam` in `Submission.Work.Projection.contDiffOn_pairParam` except
that the hypothesis is smoothness rather than analyticity, so no `of_le` downgrading is needed. -/
theorem contDiffOn_pairParam_smooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p q : M) :
    ContDiffOn ℝ 1 (pairParam e p q) (pairDom e p q) := by
  -- The chartwise difference `pairZ e p q ab = chartRep e q ab.2 - chartRep e p ab.1`.
  have hZ : ContDiffOn ℝ ∞ (pairZ e p q) (pairDom e p q) := by
    have h : ContDiffOn ℝ ∞
        (fun yz : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          -(chartRep e p yz.1 - chartRep e q yz.2))
        {yz | yz.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target ∧
              yz.2 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target} :=
      (contDiffOn_diff (n := n) (k := 2 * n) e he p q).neg
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
    have h := (contDiff_pairEquiv_smooth n).contDiffOn.comp hD (fun _ _ => Set.mem_univ _)
    refine h.congr fun ab _ => ?_
    simp only [Function.comp_apply, pairParam]
  exact hP.of_le (by norm_num)

end Work.Projection
