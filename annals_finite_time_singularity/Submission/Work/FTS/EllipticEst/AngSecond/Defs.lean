/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular-weight calculus of `angular_second_order_est`

This module owns the vocabulary of the weighted `L²` pairing used by
`Work.FTS.EllipticEst.angular_second_order_est` (Step 2 of `prop:H2`
of Elgindi, Annals 194 (3) 2021, the term `|∂_θθΨ|`).

The weight of that estimate is `W z θ = w z / sin(2θ)^{η/2}` with `w z = (1+z)²/z²` and
`η = 99/100`; its square is `w z² · σ θ` with the *angular* weight

  `σ θ = sin(2θ)^{-η}`,    `η = Work.Spaces.eta`.

All the estimates of Step 2 are statements about the iterated integral

  `IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ`,

the `L²` inner product w.r.t. the measure `w² σ dz dθ`; note `IP g g = L2Sq (g · W)`
(`L2Sq_mul_W`) and `sqrt (IP g g) = L2Norm (g · W)`, so the target inequality is
`sqrt (IP φ φ) ≤ C (sqrt (IP F F) + α * sqrt (IP U U))` with `φ = ∂_θθΨ` and `U = z ∂_zΨ`.

`IPMem g h` is the honesty of the pairing: the integrand is integrable, slicewise in `θ` and then
in `z` (this is the form in which the iterated integral is manipulated downstream).  Without it a
totalised integral can be the junk value `0`, and the Cauchy–Schwarz inequality for `IP` needs
both squares to be honest.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngSecond

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## The angular weight and the weighted pairing -/

/-- The angular weight `σ θ = sin(2θ)^{-η}`, `η = Work.Spaces.eta = 99/100`. -/
def sig (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

/-- The radial factor `w z²` of the weight `W²`. -/
def w2 (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- The weighted `L²` pairing `IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ`. -/
def IP (g h : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ

/-- Honesty of the pairing `IP g h`: the integrand is integrable, slicewise in `θ` and then in
`z`.  Under this hypothesis the iterated integral of `IP` is the honest value of the pairing. -/
def IPMem (g h : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => g z θ * h z θ * w2 z * sig θ) Work.Spaces.Iθ) ∧
    IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * sig θ) Work.Spaces.Iz

/-! ## Elementary pointwise facts -/

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem w2_nonneg (z : ℝ) : 0 ≤ w2 z := by rw [w2]; positivity

theorem sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sig_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sig θ := by
  rw [sig]
  exact Real.rpow_nonneg (sin_two_nonneg hθ) _

/-- On the *open* angular interval the angular weight is at least `1` (so `W ≥ w`). -/
theorem one_le_sig {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 1 ≤ sig θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hpos : 0 < (Real.sin (2 * θ)) ^ Work.Spaces.eta := Real.rpow_pos_of_pos hs0 _
  have hle : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 Work.Spaces.eta_nonneg
  rw [sig, Real.rpow_neg (le_of_lt hs0)]
  rw [← inv_mul_cancel₀ (ne_of_gt hpos)]
  simpa using mul_le_mul_of_nonneg_left hle (le_of_lt (inv_pos.mpr hpos))

/-! ## The pairing of `g` with itself is the square of the weighted `L²`-norm -/

/-- **Pointwise identity.**  `(g · W)² = g² · w² · σ` where `W = w / sin(2θ)^{η/2}`. -/
theorem sq_mul_W (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = g z θ * g z θ * w2 z * sig θ := by
  rcases eq_or_lt_of_le (sin_two_nonneg hθ) with hs | hs
  · -- endpoint of `Iθ`: both sides vanish
    have hzero : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [← hs]; exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    have hne : -(Work.Spaces.eta) ≠ 0 := by rw [Work.Spaces.eta]; norm_num
    rw [hzero, div_zero, mul_zero, zero_pow (by norm_num)]
    rw [sig, ← hs, Real.zero_rpow hne]
    ring
  · have hw : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
      rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hs)]
    rw [hw, mul_pow, mul_pow]
    have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [sq, ← Real.rpow_add hs]
      congr 1
      rw [Work.Spaces.eta]; ring
    rw [hsq]
    simp only [w2, sig, sq]
    ring

theorem L2Sq_mul_W (g : ℝ → ℝ → ℝ) :
    Work.Spaces.L2Sq
        (fun z θ => g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = IP g g := by
  rw [Work.Spaces.L2Sq, IP]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  exact setIntegral_congr_fun measurableSet_Icc fun θ hθ => sq_mul_W g hθ

theorem L2Norm_mul_W (g : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.L2Norm
        (fun z θ => g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      = Real.sqrt (IP g g) := by
  rw [Work.FTS.EllipticEst.L2Norm_eq_sqrt, L2Sq_mul_W]

/-! ## The bilinear form is symmetric, and monotone in the pointwise sense -/

theorem IP_symm (g h : ℝ → ℝ → ℝ) : IP g h = IP h g := by
  rw [IP, IP]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  ring

theorem IP_congr {g g' h h' : ℝ → ℝ → ℝ} (hg : ∀ z θ, g z θ = g' z θ)
    (hh : ∀ z θ, h z θ = h' z θ) : IP g h = IP g' h' := by
  rw [IP, IP]
  refine setIntegral_congr_fun measurableSet_Ici fun z _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  rw [hg z θ, hh z θ]

theorem IP_self_nonneg (g : ℝ → ℝ → ℝ) : 0 ≤ IP g g := by
  rw [← L2Sq_mul_W g, Work.Spaces.L2Sq]
  refine setIntegral_nonneg measurableSet_Ici fun z _ => ?_
  exact setIntegral_nonneg measurableSet_Icc fun θ _ => sq_nonneg _

/-- **Monotonicity on the diagonal**: a pointwise domination gives the domination of the
pairings, in the honest case. -/
theorem IP_self_le_of_sq_le {g h : ℝ → ℝ → ℝ}
    (hg : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => g z θ * g z θ * w2 z * sig θ) Work.Spaces.Iθ)
    (hh : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => h z θ * h z θ * w2 z * sig θ) Work.Spaces.Iθ)
    (hG : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, g z θ * g z θ * w2 z * sig θ)
      Work.Spaces.Iz)
    (hH : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, h z θ * h z θ * w2 z * sig θ)
      Work.Spaces.Iz)
    (hle : ∀ z θ, g z θ ^ 2 ≤ h z θ ^ 2) : IP g g ≤ IP h h := by
  rw [IP, IP]
  refine setIntegral_mono_on hG hH measurableSet_Ici fun z hz =>
    setIntegral_mono_on (hg z hz) (hh z hz) measurableSet_Icc fun θ hθ => ?_
  have h1 : g z θ * g z θ ≤ h z θ * h z θ := by
    simpa [sq] using hle z θ
  have h2 : g z θ * g z θ * w2 z ≤ h z θ * h z θ * w2 z :=
    mul_le_mul_of_nonneg_right h1 (w2_nonneg z)
  exact mul_le_mul_of_nonneg_right h2 (sig_nonneg hθ)

end Work.FTS.EllipticEst.AngSecond
