import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenBarrier
import Submission.Work.FTS.StrongEps.EpsE4Thr.UnifIPOIP4
import Submission.Work.Spaces.SmoothCompact_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-! ## The level condition in the open class -/

/-- **The exact datum condition for `h0` of the level-four barrier, in the open class.**  If the
admissible datum `x` satisfies `Xn α x < √(clo/Cup) · r`, then its energy is strictly below the
level `clo · r²`.  The open-class twin of `BarrierThreshold.energy_lt_of_strict_norm` (which is
stated for the frozen `UnifIP`/`CoerAdm`). -/
theorem energy_lt_of_strict_norm_open {α α₂ cc clo Cup Ccs r : ℝ} {IP : ℝ → Fn → Fn → ℝ} {x : Fn}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂) (hx : CoerAdmO α x)
    (hX : Work.FTS.Nonlin.Xn α x < Real.sqrt (clo / Cup) * r) :
    IP α x x < clo * r ^ 2 := by
  have hCup : 0 < Cup := hIP.pos.2.2.2.1
  have hclo : 0 < clo := hIP.pos.2.2.1
  have hup := hIP.up α hα x hx
  have hsq : Work.Spaces.HkSq α 4 x = (Work.FTS.Nonlin.Xn α x) ^ 2 := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 x)]
  have hratio : (0 : ℝ) ≤ clo / Cup := div_nonneg hclo.le hCup.le
  have hXnn : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α x := Work.Spaces.HkNorm_nonneg α 4 x
  have hsqX : (Work.FTS.Nonlin.Xn α x) ^ 2 < (Real.sqrt (clo / Cup) * r) ^ 2 :=
    pow_lt_pow_left₀ hX hXnn (by norm_num)
  have hsqrt2 : (Real.sqrt (clo / Cup)) ^ 2 = clo / Cup := Real.sq_sqrt hratio
  calc IP α x x ≤ Cup * Work.Spaces.HkSq α 4 x := hup
    _ = Cup * (Work.FTS.Nonlin.Xn α x) ^ 2 := by rw [hsq]
    _ < Cup * (Real.sqrt (clo / Cup) * r) ^ 2 := mul_lt_mul_of_pos_left hsqX hCup
    _ = clo * r ^ 2 := by
        rw [mul_pow, hsqrt2]
        field_simp

/-- **`h0` of the level-four barrier from the sharp datum bound**, open class: at the barrier level
`clo · (C₀α²)²` the datum condition is `Xn α x < √(clo/Cup) · C₀ α²`. -/
theorem h0_of_datum_ratio_open {α α₂ cc clo Cup Ccs C₀ : ℝ} {IP : ℝ → Fn → Fn → ℝ} {x : Fn}
    (hIP : UnifIPO IP α₂ cc clo Cup Ccs) (hα : α ∈ Set.Ioc 0 α₂) (hx : CoerAdmO α x)
    (hX : Work.FTS.Nonlin.Xn α x < Real.sqrt (clo / Cup) * (C₀ * α ^ 2)) :
    IP α x x < clo * (C₀ * α ^ 2) ^ 2 :=
  energy_lt_of_strict_norm_open hIP hα hx hX

/-! ## The barrier with the Fatou/limsup condition -/



end Work.FTS.StrongEps.EpsE4Thr
