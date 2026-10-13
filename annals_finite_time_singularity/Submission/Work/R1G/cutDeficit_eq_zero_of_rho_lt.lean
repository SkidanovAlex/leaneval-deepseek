import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.R1G.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- **The cut-off bump is locally constant where it equals one.**  For `|x| < 1` the bump is `1` on
the whole neighbourhood `(-1,1)` of `x`, hence `χ' = 0` there. -/
theorem deriv_chi_eq_zero_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    deriv Work.Stability.chi x = 0 := by
  have h : Work.Stability.chi =ᶠ[nhds x] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo (by rw [abs_lt] at hx; exact hx)] with y hy
    exact Work.Stability.chi_eq_one (abs_le.mpr ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
  rw [h.deriv_eq, deriv_const]

/-- **The cut-off deficit vanishes inside the cut-off region.**  For `ρ(r,z) < L` the argument
`ρ(r,z)/L` of the bump lies in `(-1,1)`, where the bump equals `1`; the radial derivative
`chiRad = χ'(ρ/L)/L` of the cut-off factor therefore vanishes, and with it the whole explicit
cut-off deficit `cutDeficit`. -/
theorem cutDeficit_eq_zero_of_rho_lt {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (ψ W : ℝ → ℝ → ℝ → ℝ) {r z t : ℝ} (h : Work.Cyl.rhoP r z < P.L) :
    Work.R1G.cutDeficit P ψ W r z t = 0 := by
  have hL : (0 : ℝ) < P.L := lt_of_le_of_lt (Work.Cyl.rhoP_nonneg r z) h
  have hx : |Work.Cyl.rhoP r z / P.L| < 1 := by
    rw [abs_of_nonneg (div_nonneg (Work.Cyl.rhoP_nonneg r z) hL.le), div_lt_one hL]
    exact h
  rw [cutDeficit_apply, chiRad, deriv_chi_eq_zero_of_abs_lt_one hx, zero_div, zero_mul,
    zero_mul]

end Work.R1G
