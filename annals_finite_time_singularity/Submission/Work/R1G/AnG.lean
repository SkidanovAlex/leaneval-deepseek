/-
# `Work.R1G.AnG` — the explicit **analytic** perturbation used to build `g ≠ 0`

Definitions and elementary facts for the perturbation

  `gA z θ = Zf z · Tf θ`,   `Zf z = z²/(1+z²)⁴`,   `Tf θ = sin (2θ)`.

**Why analytic?**  In this workspace `Work.Spaces.SmoothNbhd f` is
`ContDiffOn ℝ ⊤ (uncurry f) U` with `U = Ioi(-1) ×ˢ Ioo(-1)(π/2+1)` and `⊤ = ω` the *analytic*
order (see the warning in `Submission/Work/Stability/Cutoff.lean`).  The perturbation of
`Work.ConstructionInstance.ProfileData` must therefore be analytic on `U`; a compactly supported
bump is excluded.  `gA` is rational-times-trigonometric, hence analytic on all of `ℝ²`, is
*nonzero in the interior of the quadrant* (`gA (1/2) (π/4) > 0`), vanishes at `θ = 0`, `θ = π/2`
and at `z = 0` (to second order), decays like `z⁻⁶`, and satisfies the angular vanishing
`|gA z θ| ≤ 2·Γ(α,θ)` for `z ≥ 0`, `θ ∈ [0,π/2]`.

The elementary one-dimensional facts used by the estimates live here; the estimates themselves
(`HkMem`, `DecayInZ`, the uniform moduli, the weighted bounds, ...) are proved in the companion
modules.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology NNReal ENNReal
open MeasureTheory Set Filter

namespace Work.R1G

/-- The `C^∞` order (`∞`), as opposed to the analytic order `⊤`. -/
abbrev smOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ## The two one-dimensional factors -/

/-- The radial factor `z ↦ z²/(1+z²)⁴`: analytic everywhere, vanishing to second order at `0`,
decaying like `z⁻⁶` at infinity. -/
def Zf (z : ℝ) : ℝ := z ^ 2 / (1 + z ^ 2) ^ 4

/-- The angular factor `θ ↦ sin (2θ)`: entire, vanishing at `0` and `π/2`. -/
def Tf (θ : ℝ) : ℝ := Real.sin (2 * θ)

/-- The closed form of `z · Zf'(z)`. -/
def Zf1 (z : ℝ) : ℝ := (2 * z ^ 2 - 6 * z ^ 4) / (1 + z ^ 2) ^ 5

/-- The closed form of `z · (z · Zf'(z))'`. -/
def Zf2 (z : ℝ) : ℝ := (4 * z ^ 2 - 40 * z ^ 4 + 36 * z ^ 6) / (1 + z ^ 2) ^ 6

/-- The closed form of `D_θ Tf = sin(2θ)·Tf'`. -/
def Tf1 (θ : ℝ) : ℝ := Real.sin (2 * θ) * (2 * Real.cos (2 * θ))

/-- The closed form of `D_θ(D_θ Tf)`. -/
def Tf2 (θ : ℝ) : ℝ := Real.sin (2 * θ) * (4 * Real.cos (4 * θ))

/-- **The analytic perturbation** `gA z θ = Zf z · Tf θ`. -/
def gA (z θ : ℝ) : ℝ := Zf z * Tf θ

/-- The operator `f ↦ z ∂_z f` on one-variable functions. -/
def Dzop : (ℝ → ℝ) → (ℝ → ℝ) := fun f => fun z => z * deriv f z

/-- The operator `f ↦ sin(2θ) ∂_θ f` on one-variable functions. -/
def Dthop : (ℝ → ℝ) → (ℝ → ℝ) := fun f => fun θ => Real.sin (2 * θ) * deriv f θ

/-- The `j`-fold `D_z`-iterate of the radial factor. -/
def Zit (j : ℕ) (z : ℝ) : ℝ := (Dzop^[j] Zf) z

/-- The `i`-fold `D_θ`-iterate of the angular factor. -/
def Tit (i : ℕ) (θ : ℝ) : ℝ := (Dthop^[i] Tf) θ

/-! ## Smoothness -/

theorem contDiff_Zf : ContDiff ℝ ⊤ Zf := by
  change ContDiff ℝ ⊤ (fun z : ℝ => z ^ 2 / (1 + z ^ 2) ^ 4)
  exact ContDiff.div (by fun_prop) (by fun_prop) (fun z => by positivity)

theorem contDiff_Tf : ContDiff ℝ ⊤ Tf := by
  change ContDiff ℝ ⊤ (fun θ : ℝ => Real.sin (2 * θ))
  exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

theorem contDiff_smooth_Zf : ContDiff ℝ smOrder Zf := contDiff_Zf.of_le le_top

theorem contDiff_smooth_sin_two : ContDiff ℝ smOrder (fun θ : ℝ => Real.sin (2 * θ)) :=
  (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).of_le le_top

theorem contDiff_smooth_Tf : ContDiff ℝ smOrder Tf := contDiff_Tf.of_le le_top

theorem differentiableAt_Zf (z : ℝ) : DifferentiableAt ℝ Zf z :=
  (contDiff_Zf.differentiable (by simp)).differentiableAt

theorem differentiableAt_Tf (θ : ℝ) : DifferentiableAt ℝ Tf θ :=
  (contDiff_Tf.differentiable (by simp)).differentiableAt

/-- **`gA` is analytic on the box `U` of `Work.Spaces.SmoothNbhd`.** -/
theorem smoothNbhd_gA : Work.Spaces.SmoothNbhd gA := by
  show ContDiffOn ℝ ⊤ (Function.uncurry gA) _
  have h : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => gA p.1 p.2) := by
    rw [show (fun p : ℝ × ℝ => gA p.1 p.2) = fun p : ℝ × ℝ => Zf p.1 * Tf p.2 from rfl]
    exact (contDiff_Zf.comp contDiff_fst).mul (contDiff_Tf.comp (by fun_prop))
  exact h.contDiffOn

/-! ## Elementary values and bounds for the radial factor -/

theorem Zf_zero : Zf 0 = 0 := by
  change (0 : ℝ) ^ 2 / (1 + 0 ^ 2) ^ 4 = 0
  norm_num

theorem Zf_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Zf z := by
  change 0 ≤ z ^ 2 / (1 + z ^ 2) ^ 4
  positivity

theorem Zf_pos {z : ℝ} (hz : 0 < z) : 0 < Zf z := by
  change 0 < z ^ 2 / (1 + z ^ 2) ^ 4
  positivity

theorem one_add_sq_le_pow4 (z : ℝ) : 1 + z ^ 2 ≤ (1 + z ^ 2) ^ 4 := by
  have ht : (1 : ℝ) ≤ 1 + z ^ 2 := by linarith [sq_nonneg z]
  simpa using pow_le_pow_right₀ ht (by norm_num : (1:ℕ) ≤ 4)

theorem Zf_le_one {z : ℝ} (_hz : 0 ≤ z) : Zf z ≤ 1 := by
  change z ^ 2 / (1 + z ^ 2) ^ 4 ≤ 1
  rw [div_le_one (by positivity)]
  linarith [one_add_sq_le_pow4 z, sq_nonneg z]

/-- The decay of the radial factor: `Zf z ≤ 2/(1+z)²`. -/
theorem Zf_le_decay {z : ℝ} (_hz : 0 ≤ z) : Zf z ≤ 2 / (1 + z) ^ 2 := by
  change z ^ 2 / (1 + z ^ 2) ^ 4 ≤ 2 / (1 + z) ^ 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : (1 + z) ^ 2 ≤ 2 * (1 + z ^ 2) := by nlinarith [sq_nonneg (1 - z)]
  have hz2 : z ^ 2 ≤ 1 + z ^ 2 := by nlinarith [sq_nonneg z]
  have h1 : z ^ 2 * (1 + z) ^ 2 ≤ z ^ 2 * (2 * (1 + z ^ 2)) :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg z)
  have h2 : z ^ 2 * (2 * (1 + z ^ 2)) ≤ (1 + z ^ 2) * (2 * (1 + z ^ 2)) :=
    mul_le_mul_of_nonneg_right hz2 (by positivity)
  have h3 : (1 + z ^ 2) * (2 * (1 + z ^ 2)) = 2 * (1 + z ^ 2) ^ 2 := by ring
  have h4 : (2:ℝ) * (1 + z ^ 2) ^ 2 ≤ 2 * (1 + z ^ 2) ^ 4 := by
    have ht : (1 : ℝ) ≤ 1 + z ^ 2 := by linarith [sq_nonneg z]
    have hp := pow_le_pow_right₀ ht (show (2:ℕ) ≤ 4 by norm_num)
    linarith [hp]
  linarith [h1, h2, h3, h4]

theorem deriv_sq (z : ℝ) : deriv (fun y : ℝ => y ^ 2) z = 2 * z := by
  rw [deriv_fun_pow differentiableAt_id 2]
  simp

theorem deriv_one_add_sq (z : ℝ) : deriv (fun y : ℝ => 1 + y ^ 2) z = 2 * z := by
  rw [deriv_const_add, deriv_sq]

/-! ## Derivatives of the radial factor -/

/-- The derivative of the radial factor (valid for every `z`, since `1+z² ≠ 0`). -/
theorem deriv_Zf (z : ℝ) : deriv Zf z = (2 * z - 6 * z ^ 3) / (1 + z ^ 2) ^ 5 := by
  change deriv ((fun y : ℝ => y ^ 2) / (fun y : ℝ => (1 + y ^ 2) ^ 4)) z = _
  rw [deriv_div (by fun_prop) (by fun_prop) (by positivity)]
  have h2 : deriv (fun y : ℝ => (1 + y ^ 2) ^ 4) z = 4 * (1 + z ^ 2) ^ 3 * (2 * z) := by
    rw [deriv_fun_pow (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => 1 + y ^ 2) z) 4,
      deriv_one_add_sq]
    simp
  rw [deriv_sq, h2]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- `z · Zf'(z)` in closed form. -/
theorem Zf1_eq (z : ℝ) : z * deriv Zf z = Zf1 z := by
  rw [deriv_Zf]
  change z * ((2 * z - 6 * z ^ 3) / (1 + z ^ 2) ^ 5) = (2 * z ^ 2 - 6 * z ^ 4) / (1 + z ^ 2) ^ 5
  field_simp

theorem deriv_Zf1 (z : ℝ) :
    deriv Zf1 z = (4 * z - 40 * z ^ 3 + 36 * z ^ 5) / (1 + z ^ 2) ^ 6 := by
  change deriv ((fun y : ℝ => 2 * y ^ 2 - 6 * y ^ 4) / (fun y : ℝ => (1 + y ^ 2) ^ 5)) z = _
  rw [deriv_div (by fun_prop) (by fun_prop) (by positivity)]
  have hnum : deriv (fun y : ℝ => 2 * y ^ 2 - 6 * y ^ 4) z = 2 * (2 * z) - 6 * (4 * z ^ 3) := by
    change deriv ((fun y : ℝ => 2 * y ^ 2) - (fun y : ℝ => 6 * y ^ 4)) z = _
    rw [deriv_sub (by fun_prop) (by fun_prop),
      deriv_const_mul 2 (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => y ^ 2) z),
      deriv_const_mul 6 (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => y ^ 4) z)]
    rw [deriv_fun_pow differentiableAt_id 2, deriv_fun_pow differentiableAt_id 4]
    simp
  have hden : deriv (fun y : ℝ => (1 + y ^ 2) ^ 5) z = 5 * (1 + z ^ 2) ^ 4 * (2 * z) := by
    rw [deriv_fun_pow (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => 1 + y ^ 2) z) 5,
      deriv_one_add_sq]
    simp
  rw [hnum, hden]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem Zf2_eq (z : ℝ) : z * deriv Zf1 z = Zf2 z := by
  rw [deriv_Zf1]
  change z * ((4 * z - 40 * z ^ 3 + 36 * z ^ 5) / (1 + z ^ 2) ^ 6)
    = (4 * z ^ 2 - 40 * z ^ 4 + 36 * z ^ 6) / (1 + z ^ 2) ^ 6
  rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem deriv_ZD_Zf (z : ℝ) :
    deriv (fun w : ℝ => w * deriv Zf w) z = (4 * z - 40 * z ^ 3 + 36 * z ^ 5) / (1 + z ^ 2) ^ 6 := by
  have hev : (fun w : ℝ => w * deriv Zf w) = Zf1 := by
    funext w; rw [Zf1_eq]
  rw [hev, deriv_Zf1]

/-! ## Elementary values, derivatives and bounds for the angular factor -/

theorem Tf_zero : Tf 0 = 0 := by simp [Tf]

theorem Tf_pi_div_two : Tf (Real.pi / 2) = 0 := by
  change Real.sin (2 * (Real.pi / 2)) = 0
  rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]

theorem Tf_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Tf θ := by
  change 0 ≤ Real.sin (2 * θ)
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem abs_Tf_le_one (θ : ℝ) : |Tf θ| ≤ 1 := by
  change |Real.sin (2 * θ)| ≤ 1
  exact Real.abs_sin_le_one _

theorem deriv_Tf (θ : ℝ) : deriv Tf θ = 2 * Real.cos (2 * θ) := by
  change deriv (fun θ : ℝ => Real.sin (2 * θ)) θ = _
  rw [deriv_sin (by fun_prop : DifferentiableAt ℝ (fun θ : ℝ => 2 * θ) θ)]
  rw [show deriv (fun θ : ℝ => 2 * θ) θ = 2 by
    rw [deriv_const_mul 2 differentiableAt_id]; simp]
  ring

theorem Tf1_eq (θ : ℝ) : Real.sin (2 * θ) * deriv Tf θ = Tf1 θ := by
  rw [deriv_Tf]
  change Real.sin (2 * θ) * (2 * Real.cos (2 * θ)) = Tf1 θ
  rw [Tf1]

theorem deriv_Tf1 (θ : ℝ) : deriv Tf1 θ = 4 * Real.cos (4 * θ) := by
  have hev : Tf1 = fun θ : ℝ => Real.sin (4 * θ) := by
    funext θ
    rw [Tf1]
    have h2 : Real.sin (4 * θ) = 2 * (Real.sin (2 * θ) * Real.cos (2 * θ)) := by
      have := Real.sin_two_mul (2 * θ)
      rw [show (2:ℝ) * (2 * θ) = 4 * θ by ring] at this
      linarith [this]
    rw [h2]; ring
  rw [hev]
  change deriv (fun θ : ℝ => Real.sin (4 * θ)) θ = 4 * Real.cos (4 * θ)
  rw [deriv_sin (by fun_prop : DifferentiableAt ℝ (fun θ : ℝ => 4 * θ) θ)]
  rw [show deriv (fun θ : ℝ => 4 * θ) θ = 4 by
    rw [deriv_const_mul 4 differentiableAt_id]; simp]
  ring

theorem Tf2_eq (θ : ℝ) : Real.sin (2 * θ) * deriv Tf1 θ = Tf2 θ := by
  rw [deriv_Tf1]
  change Real.sin (2 * θ) * (4 * Real.cos (4 * θ)) = Tf2 θ
  rw [Tf2]

/-! ## The iterated operators on the one-dimensional factors -/

theorem Dzop_Zf : Dzop Zf = Zf1 := by
  funext z
  rw [Dzop, Zf1_eq]

theorem Dzop_Zf1 : Dzop Zf1 = Zf2 := by
  funext z
  rw [Dzop, Zf2_eq]

theorem Dthop_Tf : Dthop Tf = Tf1 := by
  funext θ
  rw [Dthop, Tf1_eq]

theorem Dthop_Tf1 : Dthop Tf1 = Tf2 := by
  funext θ
  rw [Dthop, Tf2_eq]

theorem Zit_zero (z : ℝ) : Zit 0 z = Zf z := rfl

theorem Zit_one (z : ℝ) : Zit 1 z = Zf1 z := by
  show (Dzop^[1]) Zf z = Zf1 z
  rw [Function.iterate_one, Dzop_Zf]

theorem Zit_two (z : ℝ) : Zit 2 z = Zf2 z := by
  show (Dzop^[2]) Zf z = Zf2 z
  rw [show (2:ℕ) = 1 + 1 by norm_num, Function.iterate_succ_apply',
    Function.iterate_one, Dzop_Zf, Dzop_Zf1]

theorem Tit_zero (θ : ℝ) : Tit 0 θ = Tf θ := rfl

theorem Tit_one (θ : ℝ) : Tit 1 θ = Tf1 θ := by
  show (Dthop^[1]) Tf θ = Tf1 θ
  rw [Function.iterate_one, Dthop_Tf]

theorem Tit_two (θ : ℝ) : Tit 2 θ = Tf2 θ := by
  show (Dthop^[2]) Tf θ = Tf2 θ
  rw [show (2:ℕ) = 1 + 1 by norm_num, Function.iterate_succ_apply',
    Function.iterate_one, Dthop_Tf, Dthop_Tf1]

theorem Zit_succ (j : ℕ) (z : ℝ) : Zit (j + 1) z = z * deriv (Zit j) z := by
  show (Dzop^[j+1]) Zf z = z * deriv (Zit j) z
  rw [Function.iterate_succ_apply']
  rfl

theorem Tit_succ (i : ℕ) (θ : ℝ) :
    Tit (i + 1) θ = Real.sin (2 * θ) * deriv (Tit i) θ := by
  show (Dthop^[i+1]) Tf θ = Real.sin (2 * θ) * deriv (Tit i) θ
  rw [Function.iterate_succ_apply']
  rfl

theorem contDiff_smooth_Zit (j : ℕ) : ContDiff ℝ smOrder (Zit j) := by
  induction j with
  | zero => rw [show Zit 0 = Zf from rfl]; exact contDiff_smooth_Zf
  | succ j ih =>
    have h : Zit (j + 1) = Dzop (Zit j) := by
      funext z
      show (Dzop^[j+1]) Zf z = Dzop (Zit j) z
      rw [Function.iterate_succ', Function.comp_apply]
      rfl
    rw [h]
    exact contDiff_id.mul (contDiff_infty_iff_deriv.mp ih).2

theorem contDiff_smooth_Tit (i : ℕ) : ContDiff ℝ smOrder (Tit i) := by
  induction i with
  | zero => rw [show Tit 0 = Tf from rfl]; exact contDiff_smooth_Tf
  | succ i ih =>
    have h : Tit (i + 1) = Dthop (Tit i) := by
      funext θ
      show (Dthop^[i+1]) Tf θ = Dthop (Tit i) θ
      rw [Function.iterate_succ', Function.comp_apply]
      rfl
    rw [h]
    show ContDiff ℝ smOrder (fun θ => Real.sin (2 * θ) * deriv (Tit i) θ)
    exact contDiff_smooth_sin_two.mul (contDiff_infty_iff_deriv.mp ih).2

/-! ## The two-dimensional perturbation `gA` -/

theorem gA_zero_z (θ : ℝ) : gA 0 θ = 0 := by
  rw [gA, Zf_zero, zero_mul]

theorem gA_zero_theta (z : ℝ) : gA z 0 = 0 := by
  rw [gA, Tf_zero, mul_zero]

theorem gA_pi_div_two (z : ℝ) : gA z (Real.pi / 2) = 0 := by
  rw [gA, Tf_pi_div_two, mul_zero]

theorem gA_nonneg {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ gA z θ :=
  mul_nonneg (Zf_nonneg hz) (Tf_nonneg hθ)

theorem gA_half_pi_div_four_pos : 0 < gA (1 / 2) (Real.pi / 4) := by
  rw [gA]
  refine mul_pos (Zf_pos (by norm_num)) ?_
  change 0 < Real.sin (2 * (Real.pi / 4))
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  norm_num

theorem pz_gA (z θ : ℝ) : Work.Spaces.pz gA z θ = deriv Zf z * Tf θ := by
  rw [Work.Spaces.pz]
  have hmul : (fun z' : ℝ => gA z' θ) = (fun z' : ℝ => Tf θ * Zf z') := by
    funext z'; rw [gA]; ring
  rw [hmul, deriv_const_mul _ (differentiableAt_Zf z)]
  ring

theorem pth_gA (z θ : ℝ) : Work.Spaces.pth gA z θ = Zf z * deriv Tf θ := by
  rw [Work.Spaces.pth]
  have hmul : (fun θ' : ℝ => gA z θ') = (fun θ' : ℝ => Zf z * Tf θ') := by
    funext θ'; rw [gA]
  rw [hmul, deriv_const_mul _ (differentiableAt_Tf θ)]

/-! ## Iterated plain derivatives of `gA` -/

theorem pzIter_gA (j : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j gA z θ = ((deriv^[j]) Zf) z * Tf θ := by
  induction j generalizing z with
  | zero => simp [Work.Spaces.pzIter, gA]
  | succ j ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pz, Function.iterate_succ_apply']
    have h1 : (fun z' : ℝ => Work.Spaces.pzIter j gA z' θ)
        = fun z' => Tf θ * (((deriv^[j]) Zf) z') := by
      funext z'; rw [ih z']; ring
    rw [h1, deriv_const_mul _ ((ContDiff.iterate_deriv j contDiff_smooth_Zf).differentiable
      (by simp)).differentiableAt]
    ring

theorem pthIter_gA (i : ℕ) (z θ : ℝ) :
    Work.Spaces.pthIter i gA z θ = Zf z * ((deriv^[i]) Tf) θ := by
  induction i generalizing θ with
  | zero => simp [Work.Spaces.pthIter, gA]
  | succ i ih =>
    rw [Work.Spaces.pthIter_succ, Work.Spaces.pth, Function.iterate_succ_apply']
    have h1 : (fun θ' : ℝ => Work.Spaces.pthIter i gA z θ')
        = fun θ' => Zf z * (((deriv^[i]) Tf) θ') := by
      funext θ'; rw [ih θ']
    rw [h1, deriv_const_mul _ ((ContDiff.iterate_deriv i contDiff_smooth_Tf).differentiable
      (by simp)).differentiableAt]

theorem DzIter_gA (j : ℕ) (z θ : ℝ) : Work.Spaces.DzIter j gA z θ = Zit j z * Tf θ := by
  induction j generalizing z with
  | zero => simp [Work.Spaces.DzIter, Zit, gA]
  | succ j ih =>
    have h1 : (fun z' : ℝ => Work.Spaces.DzIter j gA z' θ) = fun z' => Tf θ * Zit j z' := by
      funext z'; rw [ih z']; ring
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, h1,
      deriv_const_mul _ ((contDiff_smooth_Zit j).differentiable (by simp)).differentiableAt,
      Zit_succ]
    ring

theorem DthIter_gA (i : ℕ) (z θ : ℝ) : Work.Spaces.DthIter i gA z θ = Zf z * Tit i θ := by
  induction i generalizing θ with
  | zero => simp [Work.Spaces.DthIter, Tit, gA]
  | succ i ih =>
    have h1 : (fun θ' : ℝ => Work.Spaces.DthIter i gA z θ') = fun θ' => Zf z * Tit i θ' := by
      funext θ'; rw [ih θ']
    rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth, h1,
      deriv_const_mul _ ((contDiff_smooth_Tit i).differentiable (by simp)).differentiableAt,
      Tit_succ]
    ring

theorem mixed_gA (j i : ℕ) (z θ : ℝ) : Work.Spaces.mixed j i gA z θ = Zit j z * Tit i θ := by
  induction j generalizing z with
  | zero => rw [Work.Spaces.mixed, Work.Spaces.DzIter_zero, DthIter_gA, Zit_zero]
  | succ j ih =>
    have h1 : (fun z' : ℝ => Work.Spaces.mixed j i gA z' θ) = fun z' => Tit i θ * Zit j z' := by
      funext z'; rw [ih z']; ring
    rw [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [show (fun z' : ℝ => Work.Spaces.DzIter j (Work.Spaces.DthIter i gA) z' θ)
        = fun z' => Work.Spaces.mixed j i gA z' θ from rfl, h1,
      deriv_const_mul _ ((contDiff_smooth_Zit j).differentiable (by simp)).differentiableAt,
      Zit_succ]
    ring

end Work.R1G
