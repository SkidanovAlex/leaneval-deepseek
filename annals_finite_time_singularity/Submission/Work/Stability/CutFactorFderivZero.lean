import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Stability.Cutoff
import Submission.Work.Cyl.Frame

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.Stability

/-- Off the ball of radius `2L` the cut-off factor `x ↦ chi(ρ(x)/L)` vanishes identically on a
whole neighbourhood (because `chi` vanishes off `(-2,2)` and `ρ` is continuous), hence so does its
derivative: for `2L < ρ(x)`, `fderiv ℝ (fun y => chi(ρ(y)/L)) x = 0`. -/
theorem CutFactorFderivZero {L : ℝ} (hL : 0 < L) {x : Work.Cyl.R3}
    (hx : 2 * L < Work.Cyl.rho x) :
    fderiv ℝ (fun y : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho y / L)) x = 0 := by
  have hrho : Continuous (fun y : Work.Cyl.R3 => Work.Cyl.rho y) :=
    continuous_norm.congr (fun y => (Work.Cyl.rho_eq_norm y).symm)
  have hcont : Continuous (fun y : Work.Cyl.R3 => Work.Cyl.rho y / L) := hrho.div_const L
  have h2 : 2 < Work.Cyl.rho x / L := (lt_div_iff₀ hL).mpr hx
  have hev : (fun y : Work.Cyl.R3 => Work.Stability.chi (Work.Cyl.rho y / L)) =ᶠ[𝓝 x]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hcont.continuousAt.eventually (isOpen_Ioi.mem_nhds h2)] with y hy
    rw [chi_eq_zero]
    rw [abs_of_pos (by linarith)]
    exact le_of_lt hy
  rw [hev.fderiv_eq]
  simp

end Work.Stability
