import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice dynLin)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The dissipative half of `hneg` at the barrier level.**

From the open-class coercivity of `𝓛_Γ^T` (`OpenLinear.IP_dynLin_le_open`, on `CoerAdmO`) and the
comparability clause `UnifIPO.up` — which, together with the barrier hypothesis `IP α x x = Y`,
gives `HkSq α 4 x ≥ Y / Cup` — the pairing of the linear part of the scheme with `x` is bounded by
`- cc (Y / Cup)`. -/
theorem IP_dynLin_le_of_eq {α α₂ cc clo Cup Ccs : ℝ} {IP : ℝ → Fn → Fn → ℝ} {g : Fam} {τ : ℝ}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂)
    (hcoer : CoerAdmO α (slice g τ))
    (hregL : RegQo α 4 (Work.Coercivity.LGammaT α (slice g τ)))
    {Y : ℝ} (hY : IP α (slice g τ) (slice g τ) = Y) :
    IP α (dynLin α g τ) (slice g τ) ≤ - cc * (Y / Cup) := by
  have hd := IP_dynLin_le_open (IP := IP) hIP hα hcoer hregL
  have hup := hIP.up α hα (slice g τ) hcoer
  have hCup : 0 < Cup := hIP.pos.2.2.2.1
  have hcc : 0 < cc := hIP.pos.2.1
  have hsq : Y / Cup ≤ Work.Spaces.HkSq α 4 (slice g τ) := by
    rw [div_le_iff₀ hCup]
    rw [← hY, mul_comm (Work.Spaces.HkSq α 4 (slice g τ)) Cup]
    exact hup
  have h2 : cc * (Y / Cup) ≤ cc * Work.Spaces.HkSq α 4 (slice g τ) :=
    mul_le_mul_of_nonneg_left hsq hcc.le
  linarith




/-! ## The explicit split of the energy derivative's vector field -/


end Work.FTS.StrongEps.EpsE4Thr
