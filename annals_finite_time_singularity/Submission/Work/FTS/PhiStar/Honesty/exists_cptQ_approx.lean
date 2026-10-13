import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.FTS.PhiStar.Honesty.ellWeakPos_psiSeries_of_cptQ
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstFinal
import Submission.Work.FTS.PhiStar.Honesty.CptApp.approxSmoothCptQ
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Fstar_approx
import Submission.Work.FTS.PhiStar.ThetaTracesBdry

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `exists_cptQ_approx_th` — compact-source density under the *θ-traces* only

`cbc/fts_ellnode_ruling.md` §4.3 (R1).  The CptApp chain
(`CptApp.EstCrux` → `EstMain` → `EstHkMem` → `EstTendsto` → `EstFinal`) destructures its
boundary hypothesis `Work.FTS.Nonlin.BdryTraces α k F` in exactly one place, the localised
angular Hardy inequality `CptApp.Est.hardyShrink_slice`, and there only through the θ-limits of
`sin(2θ)^{1-γ}(D_z^s F)²`.  That is precisely `PhiStar.ThetaTraces α k F`, so the whole chain is
restated with the weaker hypothesis (a mechanical change, done in place in the `CptApp/` files:
the eight modules now take `ThetaTraces`).

`exists_cptQ_approx_th` is the resulting density statement; `exists_cptQ_approx` (the original
`BdryTraces` form) is recovered from it through `PhiStar.thetaTraces_of_bdryTraces`, so no
consumer of the old interface breaks.
-/

namespace Work.FTS.PhiStar.Honesty

/-- **R1: compact-source density with the θ-trace hypothesis.** -/
theorem exists_cptQ_approx_th (k : ℕ) {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (htr : Work.FTS.PhiStar.ThetaTraces α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∃ G : ℕ → ℝ → ℝ → ℝ,
      (∀ n : ℕ, Work.FTS.PhiStar.Honesty.SmoothCptQ (G n) ∧
        ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (G n) z = 0) ∧
      (∀ n : ℕ, Work.Spaces.HkMem α k (fun z θ => G n z θ - F z θ)) ∧
      Filter.Tendsto (fun n : ℕ => Work.Spaces.HkSq α k (fun z θ => G n z θ - F z θ))
        Filter.atTop (nhds 0) := by
  have hα1 : α ≤ 1 := by linarith
  refine ⟨fun n => Work.FTS.PhiStar.Honesty.CptApp.approx (n + 3) F, ?_, ?_, ?_⟩
  · intro n
    exact ⟨Work.FTS.PhiStar.Honesty.CptApp.approxSmoothCptQ hsm (n + 3) (by omega),
      Work.FTS.PhiStar.Honesty.CptApp.Fstar_approx hF (n + 3) (by omega)⟩
  · intro n
    exact Work.FTS.PhiStar.Honesty.CptApp.EstAlt.hkMem_err k α hα hα1 F (n + 3)
      (by omega) hsm hF hFs htr
  · exact (Work.FTS.PhiStar.Honesty.CptApp.tendsto_HkSq_err_final k α hα hα1 hsm hF htr hFs).comp
      (Filter.tendsto_add_atTop_nat 3)

/-- The original `BdryTraces` form, recovered from the θ-trace form. -/
theorem exists_cptQ_approx (k : ℕ) {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (htr : Work.FTS.Nonlin.BdryTraces α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∃ G : ℕ → ℝ → ℝ → ℝ,
      (∀ n : ℕ, Work.FTS.PhiStar.Honesty.SmoothCptQ (G n) ∧
        ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (G n) z = 0) ∧
      (∀ n : ℕ, Work.Spaces.HkMem α k (fun z θ => G n z θ - F z θ)) ∧
      Filter.Tendsto (fun n : ℕ => Work.Spaces.HkSq α k (fun z θ => G n z θ - F z θ))
        Filter.atTop (nhds 0) :=
  exists_cptQ_approx_th k hα hα4 hsm hF (Work.FTS.PhiStar.thetaTraces_of_bdryTraces htr) hFs

end Work.FTS.PhiStar.Honesty
