/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Final.Level0` — the level-`0` (`η`-weighted) elliptic estimate, `TT.EllWeak0`

Target: `∃ C > 0, Work.FTS.EllipticEst.TT.EllWeak0 C`, i.e. for every `0 < α ≤ 1/4` and every
datum `(F, Ψ)` of the weak class `TT.EllWeakPos α 0 F Ψ`,

  `α⁴ HkSq α 0 (z² ∂_zz Ψ) + HkSq α 0 (∂_θθ Ψ) ≤ C HkSq α 0 F`

(Elgindi, Annals **194** (2021), `prop:L2` together with Steps 1–2 of `prop:H2`).

## The route (all inputs proved and axiom-clean)

The almost-everywhere class `H2W.Ae.AeData` carries the whole elliptic machinery.  With

* `hE := AeS1.unwEnergyD` — the **unweighted** first-order energy inequality
  `α²‖z∂_zu‖²_{w²} + ‖∂_θu‖²_{w²} ≤ C‖G‖²_ρ` (plus the two `L2Mem` conjuncts);
* `hU := Final.aeSigmaUpD` — the `σ`-Poincaré upgrade `HkSq α 0 u ≤ C L2Sq (∂_θu · w)`;
* `hD := Dispatch.aeSigmaEnergyD` — the `σ`-weighted radial inequality
  `α²‖z∂_zu‖²_ρ ≤ C(‖G‖²_ρ + ‖u‖²_ρ)`;
* `h2 := Dispatch.step2AeD` — Step 2, `‖∂_θθu‖_ρ ≤ C(‖G‖_ρ + α‖z∂_zu‖_ρ)`;
* `AeS1.step1_of hE hU hD` — Step 1 in the joined form `H2W.Ae.Step1`;
* `Dispatch.step3AeD` — Step 3, the radial second-order recovery `α²‖z²∂_zzu‖_ρ ≤ C(…)`,

the proved assembly `H2W.Ae.level0Ae_of` produces the estimate in the class `AeData`, and
`Final.aeData_of_ellWeakPos'` transfers it to `TT.EllWeakPos` (`Dispatch.ellWeak0_of_steps`
does exactly this; it is reproduced below so that the import cone of this module stays free of
the mutually inconsistent copies that `Dispatch/cores_level_zero.lean` drags in).
-/
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU
import Submission.Work.FTS.EllipticEst.AeS1.Assembly
import Submission.Work.FTS.EllipticEst.AeS1.unwEnergyD
import Submission.Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyD
import Submission.Work.FTS.EllipticEst.Dispatch.step2AeD
import Submission.Work.FTS.EllipticEst.Dispatch.step3AeD
import Submission.Work.FTS.EllipticEst.Final.AeSigmaUpD

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Final

set_option autoImplicit false

/-- The level-`0` estimate in the weak class from the three Steps of `prop:H2`. -/
theorem ellWeak0_of_steps (h1 : Work.FTS.EllipticEst.H2W.Ae.Step1)
    (h2 : Work.FTS.EllipticEst.H2W.Ae.Step2) (h3 : Work.FTS.EllipticEst.H2W.Ae.Step3) :
    ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C := by
  obtain ⟨C, hC, hmain⟩ := Work.FTS.EllipticEst.H2W.Ae.level0Ae_of h1 h2 h3
  refine ⟨C, hC, ?_⟩
  intro α F Ψ hα hα4 hW
  exact hmain α Ψ F (aeData_of_ellWeakPos' hα hα4 hW)

/-- **The level-`0` estimate** `∃ C > 0, TT.EllWeak0 C`. -/
theorem EllWeak0_exists : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C :=
  ellWeak0_of_steps
    (Work.FTS.EllipticEst.AeS1.step1_of Work.FTS.EllipticEst.AeS1.unwEnergyD aeSigmaUpD
      Work.FTS.EllipticEst.Dispatch.aeSigmaEnergyD)
    Work.FTS.EllipticEst.Dispatch.step2AeD
    Work.FTS.EllipticEst.Dispatch.step3AeD

end Work.FTS.EllipticEst.Final
