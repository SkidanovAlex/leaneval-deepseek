import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.approxSmoothCptQ
import Submission.Work.FTS.PhiStar.StarCoreInhabitant
import Submission.Work.FTS.StrongEps.E5G.slice_lip5_norm
import Submission.Work.FTS.StrongEps.EpsCorrTendsto4
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.H6Rows.NZzero6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.exists_cptQ_approx =====
section

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


end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarPkgo2Inhabitant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.StarPkgo2Inhabitant` — the packaged star node

`StarPkgo2 α Cs Φ_*` for every `0 < α ≤ α₀`, obtained by composing the analysis node
`StarCore_inhabitant` (the flat bound on `Ŷ = ((z+1)/z)·Φ̃_*/sin 2θ`) with the purely algebraic
conversion `StarPkgo2OfCore`.
-/

noncomputable section
open scoped Real Topology

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false



end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsHlim4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000


end Work.FTS.StrongEps
end
end
