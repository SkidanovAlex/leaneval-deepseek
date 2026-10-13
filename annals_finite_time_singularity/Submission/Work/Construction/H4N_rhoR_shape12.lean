import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Construction.GammaTermAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction

open scoped Topology

/-- The elementary derivative of the radial factor `ρ(z) = z²/(1+z)⁴` away from `z = -1`. -/
private lemma deriv_rhoR (x : ℝ) (hx : x ≠ -1) :
    deriv rhoR x = (2*x*(1+x)^4 - x^2*(4*(1+x)^3))/((1+x)^4)^2 := by
  show deriv (fun z : ℝ => z^2/(1+z)^4) x = _
  have hden : (1+x)^4 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  have hd1 : DifferentiableAt ℝ (fun z : ℝ => z^2) x := by fun_prop
  have hd2 : DifferentiableAt ℝ (fun z : ℝ => (1+z)^4) x := by fun_prop
  have hv2 : deriv (fun z : ℝ => (1+z)^4) x = 4*(1+x)^3 := by
    change deriv ((fun z : ℝ => 1+z)^4) x = 4*(1+x)^3
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun z : ℝ => 1+z) x)]
    simp
  change deriv ((fun z : ℝ => z^2) / (fun z : ℝ => (1+z)^4)) x = _
  rw [deriv_div hd1 hd2 hden]
  rw [hv2]
  simp

/-- The closed form of `D_z ρ = Zop ρ` away from `z = -1`. -/
private lemma Zop_rhoR_eq (x : ℝ) (hx : x ≠ -1) :
    Work.Spaces.Zop rhoR x = x^2*(2-2*x)/(1+x)^5 := by
  rw [Zop_apply, deriv_rhoR x hx]
  have hden : (1+x)^4 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  have hden5 : (1+x)^5 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  field_simp
  ring

/-- The elementary derivative of `w ↦ w²(2-2w)/(1+w)⁵` away from `w = -1`. -/
private lemma deriv_g1 (x : ℝ) (hx : x ≠ -1) :
    deriv (fun w : ℝ => w^2*(2-2*w)/(1+w)^5) x = 2*(2*x - 6*x^2 + 2*x^3)/(1+x)^6 := by
  have hden : (1+x)^5 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  have hnum : DifferentiableAt ℝ (fun w : ℝ => w^2*(2-2*w)) x := by fun_prop
  have hden' : DifferentiableAt ℝ (fun w : ℝ => (1+w)^5) x := by fun_prop
  have hdnum : deriv (fun w : ℝ => w^2*(2-2*w)) x = 2*x*(2-2*x) - 2*x^2 := by
    have hd1 : DifferentiableAt ℝ (fun w : ℝ => w^2) x := by fun_prop
    have hd2 : DifferentiableAt ℝ (fun w : ℝ => 2-2*w) x := by fun_prop
    change deriv ((fun w : ℝ => w^2) * (fun w : ℝ => 2-2*w)) x = _
    rw [deriv_mul hd1 hd2]
    simp
    ring
  change deriv ((fun w : ℝ => w^2*(2-2*w)) / (fun w : ℝ => (1+w)^5)) x = _
  rw [deriv_div hnum hden' hden]
  rw [hdnum]
  have hv5 : deriv (fun w : ℝ => (1+w)^5) x = 5*(1+x)^4 := by
    change deriv ((fun w : ℝ => 1+w)^5) x = 5*(1+x)^4
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => 1+w) x)]
    simp
  rw [hv5]
  field_simp
  ring

/-- The derivative of `Zop ρ` away from `z = -1`, transported through the closed form of
`Zop ρ` on a neighbourhood of the point. -/
private lemma Zop_rhoR_deriv (x : ℝ) (hx : x ≠ -1) :
    deriv (Work.Spaces.Zop rhoR) x = 2*(2*x - 6*x^2 + 2*x^3)/(1+x)^6 := by
  have hev : (Work.Spaces.Zop rhoR) =ᶠ[𝓝 x] (fun w : ℝ => w^2*(2-2*w)/(1+w)^5) := by
    filter_upwards [eventually_ne_nhds hx] with w hw
    exact Zop_rhoR_eq w hw
  rw [hev.deriv_eq]
  exact deriv_g1 x hx

theorem H4N_rhoR_shape12 :
    (∀ z : ℝ, z ≠ -1 → (Work.Spaces.Zop^[1] Work.Construction.rhoR) z
        = z^2 * (2 - 2*z) / (1 + z)^5)
    ∧ (∀ z : ℝ, z ≠ -1 → (Work.Spaces.Zop^[2] Work.Construction.rhoR) z
        = z^2 * (4 - 12*z + 4*z^2) / (1 + z)^6) := by
  constructor
  · intro z hz
    rw [Function.iterate_one]
    exact Zop_rhoR_eq z hz
  · intro z hz
    rw [Function.iterate_succ_apply, Function.iterate_one]
    show Work.Spaces.Zop (Work.Spaces.Zop rhoR) z = z^2 * (4 - 12*z + 4*z^2) / (1 + z)^6
    rw [Zop_apply, Zop_rhoR_deriv z hz]
    have hden : (1+z)^6 ≠ 0 := pow_ne_zero _ (by intro h; exact hz (by linarith))
    field_simp
    ring

end Work.Construction
