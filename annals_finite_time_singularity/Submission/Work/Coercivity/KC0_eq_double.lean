import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.CTDefs
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- `KC0 f = L₁₂(Transport f)(0)` evaluated directly: `L₁₂` of the transport term is the
iterated integral of `K(θ) · 3 D_θ f /((1+z) z)`, i.e. the double integral of
`D_θ f · 3K(θ)/(z(1+z))` over the quadrant.  (The radial set `Ioi 0` of `FM.L12` and the
closed half-line `Spaces.Iz` differ by the null set `{0}`.) -/
theorem KC0_eq_double (f : ℝ → ℝ → ℝ) :
    Work.Coercivity.CT.KC0 f = ∫ s in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.Dth f s θ * (3 * Work.Spaces.K θ) / (s * (1 + s)) := by
  have hpt : ∀ s : ℝ, Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport f) s
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.Dth f s θ * (3 * Work.Spaces.K θ)
          / (s * (1 + s)) := by
    intro s
    rw [Work.FM.L12dens]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ
    simp only [Work.Coercivity.Transport]
    rw [div_eq_mul_inv (3 * Work.Spaces.Dth f s θ) (1 + s),
        div_eq_mul_inv (Work.Spaces.Dth f s θ * (3 * Work.Spaces.K θ)) (s * (1 + s)),
        mul_inv_rev]
    ring
  simp only [Work.Coercivity.CT.KC0, Work.Coercivity.L12f, Work.FM.L12, Work.Spaces.Iz]
  rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  exact hpt s

end Work.Coercivity
