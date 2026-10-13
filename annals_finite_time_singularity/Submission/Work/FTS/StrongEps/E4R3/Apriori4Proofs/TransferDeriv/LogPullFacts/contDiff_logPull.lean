import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts

/-- The log-coordinate map `Ψ(s,ζ) = (e^s, arctan (e^ζ))` is smooth of every finite order as a
map `ℝ × ℝ → ℝ × ℝ`. -/
theorem contDiff_logPsi (n : ℕ) :
    ContDiff ℝ n (fun x : ℝ × ℝ => (Real.exp x.1, Real.arctan (Real.exp x.2))) :=
  (Real.contDiff_exp.comp contDiff_fst).prodMk
    (Real.contDiff_arctan.comp (Real.contDiff_exp.comp contDiff_snd))

/-- The log-coordinate map lands in the open quadrant `Q0` (for every `y`, `e^{y.1} > 0` and
`0 < arctan (e^{y.2}) < π/2`). -/
theorem logPsi_mem_Q0 (x : ℝ × ℝ) :
    (Real.exp x.1, Real.arctan (Real.exp x.2)) ∈ Work.FTS.EllipticEst.Q0 :=
  Work.FTS.EllipticEst.mem_Q0.mpr
    ⟨Real.exp_pos x.1, Real.arctan_pos.mpr (Real.exp_pos x.2), Real.arctan_lt_pi_div_two _⟩

theorem contDiff_logPull {g : Work.FTS.Galerkin.Fn}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.EllipticEst.Q0) (n : ℕ) :
    ContDiff ℝ n (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g) := by
  -- `logPull g` is the composite `(uncurry g) ∘ Ψ` of the `C^n` map `Ψ` (whose image lies in the
  -- open quadrant `Q0`) with the function `uncurry g`, which is `C^n` *on* `Q0`.
  exact ContDiffOn.comp_contDiff (hg n) (contDiff_logPsi n) logPsi_mem_Q0

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.LogPullFacts
