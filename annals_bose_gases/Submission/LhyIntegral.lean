import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Algebra.Order.Star.Real
import ChallengeDeps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The LHY sharp-constant model integral (Layer 5, "Bogoliubov integral")

Any derivation of the two-term Lee--Huang--Yang lower bound (the Fournais--
Solovej box theorem) evaluates, at the very end, the *model* Bogoliubov
integral (FS, `lem:BogIntegral`, eq. following `I_1'`):

    I_1' ≈ ∫_{ℝ³} [ t² + 8π − (8π)²/(2t²) − √((t²+8π)² − (8π)²) ] dt
         = − 64 π⁴ · 128/(15√π)

(an *improperly convergent* 3D integral: the `t⁻²` divergence at the origin
and the algebraic growth at infinity cancel inside the bracket).  Radially
this is

    T2 : 4π · ∫₀^∞ [ r⁴ + 8πr² − (8π)²/2 − r³√(r² + 16π) ] dr
         = − 64 π⁴ · 128/(15√π) ,

and by the change of variables `r = √(8π)·x` it is equivalent to the
dimensionless form

    T1 : ∫₀^∞ [ x⁴ + x² − 1/2 − x³√(x² + 2) ] dx = − 16/(15√2) .

Both identities are proved here from scratch (an explicit antiderivative
`G(x) = t/2 + t³/24 − t⁵/80` of the dimensionless integrand in the variable
`t = √(x²+2) − x`, FTC on the half line, and elementary limits at `0⁺` and
`∞`; T2 follows from T1 by the linear scaling `r = √(8π)·x`).

Notation: `√` is `Real.sqrt`; `∫ x in Set.Ioi (0:ℝ), f x` is the Lebesgue
integral over the positive half-line.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real Topology

set_option autoImplicit false

namespace Submission.BoseGases

private def s (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + 2)
private def t (x : ℝ) : ℝ := s x - x
private def integrand (x : ℝ) : ℝ := x ^ 4 + x ^ 2 - (1 / 2 : ℝ) - x ^ 3 * s x
private def ft (x : ℝ) : ℝ := (t x) ^ 2 * ((t x) ^ 2 - 4) / 8
private def tp (x : ℝ) : ℝ := x / s x - 1
private def dg (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * tp x + (1 / 24 : ℝ) * (3 * (t x) ^ 2 * tp x) - (1 / 80 : ℝ) * (5 * (t x) ^ 4 * tp x)
private def G (x : ℝ) : ℝ := (1 / 2 : ℝ) * t x + (1 / 24 : ℝ) * (t x) ^ 3 - (1 / 80 : ℝ) * (t x) ^ 5

private lemma s_sq (x : ℝ) : (s x) ^ 2 = x ^ 2 + 2 := by
  dsimp [s]
  rw [Real.sq_sqrt]
  nlinarith

private lemma s_pos (x : ℝ) : 0 < s x := by
  dsimp [s]
  exact Real.sqrt_pos.mpr (by nlinarith : 0 < x ^ 2 + 2)

private lemma s_ne_zero (x : ℝ) : s x ≠ 0 := ne_of_gt (s_pos x)

private lemma s_nonneg (x : ℝ) : 0 ≤ s x := le_of_lt (s_pos x)

private lemma hasDerivAt_sqrt_sq_add_two (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + 2)) (x / Real.sqrt (x ^ 2 + 2)) x := by
  have hu : HasDerivAt (fun y : ℝ => y ^ 2 + 2) (2 * x) x := by
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow (n := 2) (x := x)
    exact hpow.add_const 2
  have hne : x ^ 2 + 2 ≠ 0 := by positivity
  have h := HasDerivAt.sqrt hu hne
  convert h using 1
  field_simp

private lemma hasDerivAt_t_pointwise (x : ℝ) :
    HasDerivAt ((fun y : ℝ => Real.sqrt (y ^ 2 + 2)) - id) (tp x) x := by
  have h := (hasDerivAt_sqrt_sq_add_two x).sub (hasDerivAt_id x)
  simpa [tp, s] using h

private def Gfun : ℝ → ℝ :=
  ((fun y : ℝ => (1 / 2 : ℝ) * (Real.sqrt (y ^ 2 + 2) - y)) +
    fun y : ℝ => (1 / 24 : ℝ) * (Real.sqrt (y ^ 2 + 2) - y) ^ 3) -
    fun y : ℝ => (1 / 80 : ℝ) * (Real.sqrt (y ^ 2 + 2) - y) ^ 5

private lemma hasDerivAt_Gfun (x : ℝ) : HasDerivAt Gfun (dg x) x := by
  have ht := hasDerivAt_t_pointwise x
  have hA : HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * (Real.sqrt (y ^ 2 + 2) - y))
      ((1 / 2 : ℝ) * tp x) x := by
    simpa [tp] using ht.const_mul (1 / 2 : ℝ)
  have hB : HasDerivAt (fun y : ℝ => (1 / 24 : ℝ) * (Real.sqrt (y ^ 2 + 2) - y) ^ 3)
      ((1 / 24 : ℝ) * (3 * (Real.sqrt (x ^ 2 + 2) - x) ^ 2 * tp x)) x := by
    simpa [tp] using (ht.fun_pow 3).const_mul (1 / 24 : ℝ)
  have hC : HasDerivAt (fun y : ℝ => (1 / 80 : ℝ) * (Real.sqrt (y ^ 2 + 2) - y) ^ 5)
      ((1 / 80 : ℝ) * (5 * (Real.sqrt (x ^ 2 + 2) - x) ^ 4 * tp x)) x := by
    simpa [tp] using (ht.fun_pow 5).const_mul (1 / 80 : ℝ)
  have hsum := (hA.add hB).sub hC
  simpa [Gfun, dg, t, s, sub_eq_add_neg, add_assoc, mul_assoc] using hsum

private lemma t2_add_two (x : ℝ) : (t x) ^ 2 + 2 = 2 * s x * t x := by
  dsimp [t]
  have h := s_sq x
  nlinarith

private lemma dg_factor (x : ℝ) : dg x = tp x * ((1 / 2 : ℝ) + (t x) ^ 2 / 8 - (t x) ^ 4 / 16) := by
  dsimp [dg, tp]
  ring

private lemma tp_neg : ∀ x : ℝ, tp x = -(t x) / s x := by
  intro x
  dsimp [tp, t]
  field_simp [s_ne_zero x]
  ring

private lemma dg_eq_ft (x : ℝ) : dg x = ft x := by
  rw [dg_factor]
  rw [tp_neg]
  dsimp [ft]
  have hf : (1 / 2 : ℝ) + (t x) ^ 2 / 8 - (t x) ^ 4 / 16 = (4 - (t x) ^ 2) * ((t x) ^ 2 + 2) / 16 := by ring
  rw [hf]
  have h2 := t2_add_two x
  field_simp [s_ne_zero x]
  rw [h2]
  ring

private lemma ft_eq_f (x : ℝ) : ft x = integrand x := by
  dsimp [ft, integrand, t]
  have h := s_sq x
  nlinarith

private lemma dg_eq_f (x : ℝ) : dg x = integrand x := by
  exact (dg_eq_ft x).trans (ft_eq_f x)

private lemma G_eq_Gfun : G = Gfun := by
  funext y
  dsimp [G, Gfun, t, s]

private lemma hasDerivAt_G (x : ℝ) : HasDerivAt G (integrand x) x := by
  rw [G_eq_Gfun]
  have h := hasDerivAt_Gfun x
  rwa [dg_eq_f x] at h

private lemma s_ge_x (x : ℝ) (hx : 0 ≤ x) : x ≤ s x := by
  have hsq2 : x ^ 2 ≤ (s x) ^ 2 := by nlinarith [s_sq x]
  have habs := (sq_le_sq.mp hsq2)
  rwa [abs_of_nonneg hx, abs_of_nonneg (s_nonneg x)] at habs

private lemma t_sq_le_four (x : ℝ) (hx : 0 ≤ x) : (t x) ^ 2 ≤ 4 := by
  have h1 : 0 ≤ t x := by dsimp [t]; nlinarith [s_ge_x x hx]
  have h2 : t x ≤ 2 := by
    dsimp [t]
    have hlt : (s x) ^ 2 < (x + 2) ^ 2 := by nlinarith [s_sq x]
    have habs := (sq_lt_sq.mp hlt)
    have hx2 : 0 ≤ x + 2 := by nlinarith
    rw [abs_of_nonneg (s_nonneg x), abs_of_nonneg hx2] at habs
    nlinarith
  nlinarith

private lemma integrand_nonpos (x : ℝ) (hx : 0 ≤ x) : integrand x ≤ 0 := by
  rw [← ft_eq_f x]
  dsimp [ft]
  have ht2 : (t x) ^ 2 ≤ 4 := t_sq_le_four x hx
  have hsq : 0 ≤ (t x) ^ 2 := sq_nonneg _
  nlinarith

private lemma sqrt2_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
  rw [Real.sq_sqrt]; norm_num

private lemma sqrt2_cube : (Real.sqrt 2 : ℝ) ^ 3 = 2 * Real.sqrt 2 := by
  rw [pow_succ, sqrt2_sq]

private lemma sqrt2_fifth : (Real.sqrt 2 : ℝ) ^ 5 = 4 * Real.sqrt 2 := by
  calc
    (Real.sqrt 2 : ℝ) ^ 5 = ((Real.sqrt 2) ^ 2) ^ 2 * Real.sqrt 2 := by ring
    _ = 4 * Real.sqrt 2 := by rw [sqrt2_sq]; norm_num

private lemma G_zero : G 0 = 8 * Real.sqrt 2 / 15 := by
  dsimp [G, t, s]
  norm_num
  rw [sqrt2_cube, sqrt2_fifth]
  ring

private lemma scaled_value : (-16 : ℝ) / (15 * Real.sqrt 2) = -8 * Real.sqrt 2 / 15 := by
  have hsqn : Real.sqrt 2 ≠ 0 := by
    intro h
    have hsq := sqrt2_sq
    nlinarith
  field_simp [hsqn]
  nlinarith [sqrt2_sq]

private lemma t_eq_div (x : ℝ) (hx : 0 < x) : t x = 2 / (s x + x) := by
  dsimp [t]
  have hden : s x + x ≠ 0 := by nlinarith [s_pos x]
  field_simp [hden]
  nlinarith [s_sq x]

private lemma tendsto_s_add_x : Tendsto (fun x : ℝ => s x + x) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards with x
  dsimp
  nlinarith [s_nonneg x]

private lemma t_tendsto_zero : Tendsto t atTop (𝓝 0) := by
  have hden : Tendsto (fun x : ℝ => s x + x) atTop atTop := tendsto_s_add_x
  have hdiv := (tendsto_const_nhds (x := (2 : ℝ))).div_atTop hden
  refine hdiv.congr' ?_
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with x hx
  exact (t_eq_div x hx).symm

private def φ (u : ℝ) : ℝ := (1 / 2 : ℝ) * u + (1 / 24 : ℝ) * u ^ 3 - (1 / 80 : ℝ) * u ^ 5

private lemma G_tendsto_zero : Tendsto G atTop (𝓝 0) := by
  have ht := t_tendsto_zero
  have hc : ContinuousAt φ 0 := by
    change ContinuousAt (fun u : ℝ => (1 / 2 : ℝ) * u + (1 / 24 : ℝ) * u ^ 3 - (1 / 80 : ℝ) * u ^ 5) 0
    fun_prop
  have hcomp := (hc.tendsto).comp ht
  have hG : G = φ ∘ t := by
    rfl
  rw [hG]
  have hφ0 : φ 0 = 0 := by
    dsimp [φ]
    norm_num
  rw [hφ0] at hcomp
  exact hcomp

private lemma scaled_main : (∫ x in Set.Ioi (0 : ℝ), integrand x) = -16 / (15 * Real.sqrt 2) := by
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ), HasDerivAt G (integrand x) x := fun x hx => hasDerivAt_G x
  have hneg : ∀ x ∈ Set.Ioi (0 : ℝ), integrand x ≤ 0 := fun x hx => integrand_nonpos x (le_of_lt hx)
  have hlim : Tendsto G atTop (𝓝 0) := G_tendsto_zero
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos' (a := (0 : ℝ)) (g := G) (g' := integrand) hderiv hneg hlim
  rw [h]
  rw [G_zero]
  rw [scaled_value]
  ring

/-- **T1 (dimensionless).** -/
lemma lhy_model_integral_scaled :
    (∫ x in Set.Ioi (0 : ℝ),
      (x ^ 4 + x ^ 2 - (1 / 2 : ℝ) - x ^ 3 * Real.sqrt (x ^ 2 + 2))) =
      -16 / (15 * Real.sqrt 2) := by
  change (∫ x in Set.Ioi (0 : ℝ), integrand x) = -16 / (15 * Real.sqrt 2)
  exact scaled_main

/-! ## The FS (T2) form via the scaling `r = √(8π) · x` -/

private def fsIntegrand (r : ℝ) : ℝ :=
  r ^ 4 + (8 * Real.pi) * r ^ 2 - ((8 * Real.pi) ^ 2) / 2 - r ^ 3 * Real.sqrt (r ^ 2 + 16 * Real.pi)
private def cc : ℝ := Real.sqrt (8 * Real.pi)

private lemma sqrt2_sq' : (Real.sqrt 2 : ℝ)^2 = 2 := by rw [Real.sq_sqrt]; norm_num
private lemma sqrt_pi_sq' : (Real.sqrt Real.pi : ℝ)^2 = Real.pi := by rw [Real.sq_sqrt]; positivity

private lemma sqrt8pi_mul_sqrtpi :
    Real.sqrt (8 * Real.pi) * Real.sqrt Real.pi = 2 * Real.sqrt 2 * Real.pi := by
  have h8 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt (8 : ℝ) = Real.sqrt (4 * 2) := by norm_num
      _ = Real.sqrt (4 : ℝ) * Real.sqrt 2 := by
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)) 2]
      _ = 2 * Real.sqrt 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        rw [Real.sqrt_sq (by norm_num : 0 ≤ (2 : ℝ))]
  calc
    Real.sqrt (8 * Real.pi) * Real.sqrt Real.pi
        = Real.sqrt ((8 * Real.pi) * Real.pi) := by
          rw [Real.sqrt_mul (by positivity : 0 ≤ 8 * Real.pi) Real.pi]
    _ = Real.sqrt (8 * (Real.pi * Real.pi)) := by
          apply congrArg Real.sqrt
          ring
    _ = Real.sqrt (8 : ℝ) * Real.sqrt (Real.pi * Real.pi) := by
          rw [Real.sqrt_mul (by positivity : 0 ≤ (8 : ℝ)) (Real.pi * Real.pi)]
    _ = Real.sqrt (8 : ℝ) * Real.pi := by
          rw [show Real.pi * Real.pi = Real.pi ^ 2 by ring]
          rw [Real.sqrt_sq (by positivity : 0 ≤ Real.pi)]
    _ = 2 * Real.sqrt 2 * Real.pi := by rw [h8]

private lemma hc2_fs : (Real.sqrt (8 * Real.pi))^2 = 8 * Real.pi := by rw [Real.sq_sqrt]; positivity

private lemma fs_scaled (x : ℝ) : fsIntegrand (cc * x) = (8 * Real.pi) ^ 2 * integrand x := by
  dsimp [fsIntegrand, integrand, s, cc]
  rw [show (Real.sqrt (8 * Real.pi) * x)^2 + 16 * Real.pi = (8 * Real.pi) * (x ^ 2 + 2) by
    rw [mul_pow, hc2_fs]
    ring]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 8 * Real.pi) (x ^ 2 + 2)]
  set q : ℝ := Real.sqrt (8 * Real.pi)
  have hq2 : q ^ 2 = 8 * Real.pi := by dsimp [q]; rw [Real.sq_sqrt]; positivity
  have hq4 : q ^ 4 = (8 * Real.pi) ^ 2 := by
    calc q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = (8 * Real.pi) ^ 2 := by rw [hq2]
  ring_nf
  rw [hq4]
  rw [hq2]
  ring

private lemma fs_integral :
    (∫ r in Set.Ioi (0 : ℝ), fsIntegrand r) = cc * (8 * Real.pi)^2 * (-16 / (15 * Real.sqrt 2)) := by
  have hcpos : 0 < cc := by
    dsimp [cc]
    exact Real.sqrt_pos.mpr (by positivity : 0 < 8 * Real.pi)
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi (g := fsIntegrand) (a := (0 : ℝ)) (b := cc) hcpos
  -- ∫ x in Ioi 0, fsIntegrand (cc*x) = cc⁻¹ • ∫ x in Ioi (cc*0), fsIntegrand x
  have h1 : (∫ x in Set.Ioi (0 : ℝ), fsIntegrand (cc * x)) =
      cc⁻¹ * (∫ r in Set.Ioi (0 : ℝ), fsIntegrand r) := by
    simpa [smul_eq_mul] using hscale
  have h2 : (∫ x in Set.Ioi (0 : ℝ), fsIntegrand (cc * x)) =
      (8 * Real.pi) ^ 2 * (∫ x in Set.Ioi (0 : ℝ), integrand x) := by
    calc
      (∫ x in Set.Ioi (0 : ℝ), fsIntegrand (cc * x))
          = (∫ x in Set.Ioi (0 : ℝ), (8 * Real.pi) ^ 2 * integrand x) := by
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            exact fs_scaled x
      _ = (8 * Real.pi) ^ 2 * (∫ x in Set.Ioi (0 : ℝ), integrand x) := by
            rw [MeasureTheory.integral_const_mul]
  have hlin : cc⁻¹ * (∫ r in Set.Ioi (0 : ℝ), fsIntegrand r) =
      (8 * Real.pi) ^ 2 * (∫ x in Set.Ioi (0 : ℝ), integrand x) := by
    rw [← h1]
    exact h2
  calc
    (∫ r in Set.Ioi (0 : ℝ), fsIntegrand r)
        = cc * (cc⁻¹ * (∫ r in Set.Ioi (0 : ℝ), fsIntegrand r)) := by
          rw [← mul_assoc]
          rw [mul_inv_cancel₀ (ne_of_gt hcpos)]
          ring
    _ = cc * ((8 * Real.pi) ^ 2 * (∫ x in Set.Ioi (0 : ℝ), integrand x)) := by
          rw [hlin]
    _ = cc * (8 * Real.pi)^2 * (-16 / (15 * Real.sqrt 2)) := by
          rw [scaled_main]
          ring

private lemma fs_value_numeric :
    4 * Real.pi * cc * (8 * Real.pi)^2 * (16 / (15 * Real.sqrt 2)) =
      64 * Real.pi^4 * (128 / (15 * Real.sqrt Real.pi)) := by
  dsimp [cc]
  have hr : Real.sqrt 2 ≠ 0 := by positivity
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [hr, hp]
  ring_nf
  rw [show Real.pi * 8 = 8 * Real.pi by ring]
  rw [sqrt8pi_mul_sqrtpi]
  nlinarith [sqrt2_sq', sqrt_pi_sq']

private lemma fs_main :
    4 * Real.pi * (∫ r in Set.Ioi (0 : ℝ), fsIntegrand r) =
      -64 * Real.pi ^ 4 * (128 / (15 * Real.sqrt Real.pi)) := by
  rw [fs_integral]
  have hpos := fs_value_numeric
  calc
    4 * Real.pi * (cc * (8 * Real.pi)^2 * (-16 / (15 * Real.sqrt 2)))
        = -(4 * Real.pi * cc * (8 * Real.pi)^2 * (16 / (15 * Real.sqrt 2))) := by ring
    _ = -(64 * Real.pi ^ 4 * (128 / (15 * Real.sqrt Real.pi))) := by rw [hpos]
    _ = -64 * Real.pi ^ 4 * (128 / (15 * Real.sqrt Real.pi)) := by ring

/-- **T2 (FS form).** -/
lemma lhy_model_integral_fs :
    4 * π * (∫ r in Set.Ioi (0 : ℝ),
      (r ^ 4 + 8 * π * r ^ 2 - (8 * π) ^ 2 / 2 - r ^ 3 * Real.sqrt (r ^ 2 + 16 * π))) =
      -64 * π ^ 4 * (128 / (15 * Real.sqrt π)) := by
  change 4 * Real.pi * (∫ r in Set.Ioi (0 : ℝ), fsIntegrand r) =
      -64 * Real.pi ^ 4 * (128 / (15 * Real.sqrt Real.pi))
  exact fs_main


end Submission.BoseGases
