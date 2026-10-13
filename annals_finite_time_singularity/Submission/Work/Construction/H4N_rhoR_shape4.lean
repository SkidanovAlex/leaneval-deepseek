import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Construction.GLop_Aux
import Submission.Work.Construction.H4N_rhoR_shape12

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Construction

noncomputable section

open scoped Topology

/-!
# The closed form of the fourth `D_z`-iterate of `ρ(z) = z²/(1+z)⁴`

`D_z` acts on functions of `z` alone as `Work.Spaces.Zop φ = fun z ↦ z·φ'(z)`
(`Work.Spaces.Zop`).  Writing `(Zop^[k] ρ)(z) = z²·N_k(z)/(1+z)^{4+k}`, one checks
that `N_0 = 1`, `N_1 = 2 - 2z`, `N_2 = 4 - 12z + 4z²` (the exact closed forms for
`k = 1, 2` are `H4N_rhoR_shape12`), and that the iterate obeys the elementary
recursion

`N_{k+1}(z) = (2·N_k(z) + z·N_k'(z))·(1+z) - (4+k)·z·N_k(z)`,

obtained by differentiating `z ↦ z²N_k(z)/(1+z)^{4+k}` and multiplying by `z`.
This yields `N_3 = 8 - 52z + 52z² - 8z³` and
`N_4 = 16 - 196z + 416z² - 196z³ + 16z⁴`, i.e. the statement below.
-/

/-- The derivative of the degree-`4` numerator `w ↦ w²(4-12w+4w²)` of `g₂`. -/
private lemma deriv_num2 (x : ℝ) :
    deriv (fun w : ℝ => w^2*(4 - 12*w + 4*w^2)) x = 8*x - 36*x^2 + 16*x^3 := by
  have hfun : (fun w : ℝ => w^2*(4 - 12*w + 4*w^2))
      = fun w : ℝ => 0 + 0*w + 4*w^2 + (-12)*w^3 + 4*w^4 + 0*w^5 := by
    funext w; ring
  rw [hfun, deriv_mono5 0 0 4 (-12) 4 0 x]
  ring

/-- The derivative of the degree-`5` numerator `w ↦ w²(8-52w+52w²-8w³)` of `g₃`. -/
private lemma deriv_num3 (x : ℝ) :
    deriv (fun w : ℝ => w^2*(8 - 52*w + 52*w^2 - 8*w^3)) x
      = 16*x - 156*x^2 + 208*x^3 - 40*x^4 := by
  have hfun : (fun w : ℝ => w^2*(8 - 52*w + 52*w^2 - 8*w^3))
      = fun w : ℝ => 0 + 0*w + 8*w^2 + (-52)*w^3 + 52*w^4 + (-8)*w^5 := by
    funext w; ring
  rw [hfun, deriv_mono5 0 0 8 (-52) 52 (-8) x]
  ring

/-- The closed form of `Zop²ρ = Zop (Zop ρ)`, restated as the function `g₂`. -/
private def g2 (w : ℝ) : ℝ := w^2*(4 - 12*w + 4*w^2)/(1+w)^6

/-- The closed form of `Zop³ρ`, written as the function `g₃`. -/
private def g3 (w : ℝ) : ℝ := w^2*(8 - 52*w + 52*w^2 - 8*w^3)/(1+w)^7

/-- The derivative of `g₂` away from `w = -1`. -/
private lemma deriv_g2 (x : ℝ) (hx : x ≠ -1) :
    deriv g2 x = x*(8 - 52*x + 52*x^2 - 8*x^3)/(1+x)^7 := by
  have hden : (1+x)^6 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  have hnum : DifferentiableAt ℝ (fun w : ℝ => w^2*(4 - 12*w + 4*w^2)) x := by fun_prop
  have hden' : DifferentiableAt ℝ (fun w : ℝ => (1+w)^6) x := by fun_prop
  have hdden : deriv (fun w : ℝ => (1+w)^6) x = 6*(1+x)^5 := by
    change deriv ((fun w : ℝ => 1+w)^6) x = 6*(1+x)^5
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => 1+w) x)]
    simp
  show deriv ((fun w : ℝ => w^2*(4 - 12*w + 4*w^2)) / (fun w : ℝ => (1+w)^6)) x = _
  rw [deriv_div hnum hden' hden, deriv_num2 x, hdden]
  have h7 : (1+x)^7 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  field_simp
  ring

/-- The derivative of `g₃` away from `w = -1`. -/
private lemma deriv_g3 (x : ℝ) (hx : x ≠ -1) :
    deriv g3 x = x*(16 - 196*x + 416*x^2 - 196*x^3 + 16*x^4)/(1+x)^8 := by
  have hden : (1+x)^7 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  have hnum : DifferentiableAt ℝ (fun w : ℝ => w^2*(8 - 52*w + 52*w^2 - 8*w^3)) x := by
    fun_prop
  have hden' : DifferentiableAt ℝ (fun w : ℝ => (1+w)^7) x := by fun_prop
  have hdden : deriv (fun w : ℝ => (1+w)^7) x = 7*(1+x)^6 := by
    change deriv ((fun w : ℝ => 1+w)^7) x = 7*(1+x)^6
    rw [deriv_pow (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => 1+w) x)]
    simp
  show deriv ((fun w : ℝ => w^2*(8 - 52*w + 52*w^2 - 8*w^3)) / (fun w : ℝ => (1+w)^7)) x = _
  rw [deriv_div hnum hden' hden, deriv_num3 x, hdden]
  have h8 : (1+x)^8 ≠ 0 := pow_ne_zero _ (by intro h; exact hx (by linarith))
  field_simp
  ring

/-- The closed form of `Zop³ρ` away from `z = -1`. -/
private lemma Zop3_rhoR (w : ℝ) (hw : w ≠ -1) :
    (Work.Spaces.Zop^[3] rhoR) w = g3 w := by
  have hev2 : (Work.Spaces.Zop^[2] rhoR) =ᶠ[𝓝 w] g2 := by
    filter_upwards [eventually_ne_nhds hw] with x hx
    exact (H4N_rhoR_shape12).2 x hx
  rw [show (3 : ℕ) = 2 + 1 by norm_num, Function.iterate_succ_apply']
  show Work.Spaces.Zop (Work.Spaces.Zop^[2] rhoR) w = g3 w
  rw [Zop_apply, hev2.deriv_eq, deriv_g2 w hw]
  show w * (w * (8 - 52*w + 52*w^2 - 8*w^3) / (1 + w)^7) = g3 w
  rw [g3]
  ring

theorem H4N_rhoR_shape4 :
    ∀ z : ℝ, z ≠ -1 → (Work.Spaces.Zop^[4] Work.Construction.rhoR) z
        = z^2 * (16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4) / (1 + z)^8 := by
  intro z hz
  have hev3 : (Work.Spaces.Zop^[3] rhoR) =ᶠ[𝓝 z] g3 := by
    filter_upwards [eventually_ne_nhds hz] with x hx
    exact Zop3_rhoR x hx
  rw [show (4 : ℕ) = 3 + 1 by norm_num, Function.iterate_succ_apply']
  show Work.Spaces.Zop (Work.Spaces.Zop^[3] rhoR) z
      = z^2 * (16 - 196*z + 416*z^2 - 196*z^3 + 16*z^4) / (1 + z)^8
  rw [Zop_apply, hev3.deriv_eq, deriv_g3 z hz]
  ring

end

end Work.Construction
