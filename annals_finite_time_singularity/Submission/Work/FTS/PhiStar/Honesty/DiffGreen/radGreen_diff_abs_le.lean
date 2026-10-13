/-
# `Work.FTS.PhiStar.Honesty.DiffGreen.radGreen_diff_abs_le`

**The sharp `L²` difference bound for the modal Green function.**  For `0 < α ≤ 1/4`,
`m : ℕ`, `z > 0` and two `L²((0,∞))` sources `c`, `c'` (a.e. strongly measurable),

  `(m+1)·|radGreen α m c' z - radGreen α m c z| ≤ (2/α)·√(∫_0^∞ (c'-c)²)·z^(-1/2)/√(m+1)`.

The proof has three steps.

1. *Additivity*: for a.e.-strongly-measurable `L²` sources both Green integrals are honest — on
   `(0,z)` the integrand `t ↦ c t · t^(q-1)` is dominated by `(c t² + t^(2q-2))/2` with
   `2q-2 > -1`, `q = rgQ α m ≥ 20`; on `(z,∞)` the integrand `t ↦ c t · t^(-p-1)` is dominated
   by `(c t² + t^(-2p-2))/2` with `2p+2 > 1`, `p = rgP α m ≥ 0` — so the interval/set integrals
   are additive in the source and
   `radGreen α m c' z - radGreen α m c z = radGreen α m (fun t => c' t - c t) z`.
   This step is exactly the (separately proved, and imported here)
   `Work.FTS.PhiStar.Honesty.DiffGreen.radGreen_sub`.

2. `IntegrableOn (fun t => (c' t - c t)²) (Ioi 0)` from `(a-b)² ≤ 2a² + 2b²`.

3. `green_value_le`: the sharp Green bound for a single source `d`,
   `(m+1)·|radGreen α m d z| ≤ (2/α)·√(∫ d²)·z^(-1/2)/√(m+1)`.  For `m ≥ 1` this is
   `Work.EllipticEst.ModalSolution.radGreen_abs_le` plus the arithmetic
   `(m+1)/((4m+5)√m) ≤ 2/√(m+1)` (equivalent to `(m+1)³ ≤ 4(4m+5)²m`, i.e. to
   `63m³ + 157m² + 97m - 1 ≥ 0` for `m ≥ 1`); for `m = 0` it is
   `Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all` (`rgP α 0 = 0`, the borderline
   tail exponent) together with `2·rgK α 0 = 2/(5α) ≤ 2/α`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all
import Submission.Work.FTS.PhiStar.Honesty.DiffGreen.radGreen_sub

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty.DiffGreen

/-- **The sharp `L²` Green bound for a single source.**  For `0 < α ≤ 1/4`, `m : ℕ`, `z > 0` and
`d` with `∫_0^∞ d² < ∞`,

  `(m+1)·|radGreen α m d z| ≤ (2/α)·√(∫_0^∞ d²)·z^(-1/2)/√(m+1)`.

The case `m = 0` is the borderline one (`rgP α 0 = 0`): the `m`-uniform bound
`radGreen_abs_le_all` gives `|radGreen α 0 d z| ≤ 2·rgK α 0·√(∫ d²)·z^(-1/2) = (2/(5α))·…`, and
`2/(5α) ≤ 2/α`.  For `m ≥ 1` the sharper `radGreen_abs_le` gives
`√(∫ d²)·z^(-1/2)/(α(4m+5)√m)`, and `(m+1)/((4m+5)√m) ≤ 2/√(m+1)` because
`(m+1)√(m+1) ≤ 2(4m+5)√m` (square both sides: `(m+1)³ ≤ 4(4m+5)²m`, i.e.
`63m³ + 157m² + 97m - 1 ≥ 0` for `m ≥ 1`). -/
private theorem green_value_le {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {d : ℝ → ℝ}
    (hd2 : IntegrableOn (fun t : ℝ => d t ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    ((m : ℝ) + 1) * |Work.FTS.PhiStar.Radial.radGreen α m d z|
      ≤ (2 / α) * Real.sqrt (∫ t in Set.Ioi 0, d t ^ 2) * z ^ (-(1 / 2) : ℝ)
          / Real.sqrt ((m : ℝ) + 1) := by
  have hα1 : α ≤ 1 := by linarith
  set S : ℝ := Real.sqrt (∫ t in Set.Ioi 0, d t ^ 2) with hSdef
  set Z : ℝ := z ^ (-(1 / 2) : ℝ) with hZdef
  have hS : 0 ≤ S := by rw [hSdef]; exact Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := by
    rw [hZdef]; exact le_of_lt (Real.rpow_pos_of_pos hz _)
  have hSZ : 0 ≤ S * Z := mul_nonneg hS hZ
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0
    have hone : ((0 : ℕ) : ℝ) + 1 = 1 := by norm_num
    rw [hone, Real.sqrt_one, div_one, one_mul]
    have hb := Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all (c := d) hα hα1 0 hd2 hz
    rw [← hSdef, ← hZdef] at hb
    have hK0 : Work.FTS.EllExist.rgK α 0 = 1 / (α * 5) := by
      rw [Work.FTS.EllExist.rgK]
      norm_num
    have hKle : 2 * Work.FTS.EllExist.rgK α 0 ≤ 2 / α := by
      rw [hK0, show 2 * (1 / (α * 5)) = 2 / (α * 5) by ring]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < α * 5) hα]
      linarith
    have hstep : 2 * Work.FTS.EllExist.rgK α 0 * S * Z ≤ (2 / α) * S * Z := by
      calc 2 * Work.FTS.EllExist.rgK α 0 * S * Z
          = (2 * Work.FTS.EllExist.rgK α 0) * (S * Z) := by ring
        _ ≤ (2 / α) * (S * Z) := mul_le_mul_of_nonneg_right hKle hSZ
        _ = (2 / α) * S * Z := by ring
    calc |Work.FTS.PhiStar.Radial.radGreen α 0 d z|
        ≤ 2 * Work.FTS.EllExist.rgK α 0 * S * Z := hb
      _ ≤ (2 / α) * S * Z := hstep
  · have hm1' : 1 ≤ m := hm1
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hb := Work.EllipticEst.ModalSolution.radGreen_abs_le α hα hα1 m hm1' (c := d) hd2 hz
    rw [← hSdef, ← hZdef] at hb
    have hnum : ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)
        ≤ 2 * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ) := by
      have hm1ℝ : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1'
      have hsq : ((m : ℝ) + 1) ^ 3 ≤ 4 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by
        have h4 : (m : ℝ) + 1 ≤ 4 * (m : ℝ) := by linarith
        have hcube : ((m : ℝ) + 1) ^ 3 ≤ (4 * (m : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h4 3
        have hfin : (4 * (m : ℝ)) ^ 3 ≤ 4 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by
          nlinarith [sq_nonneg (m : ℝ), sq_nonneg (4 * (m : ℝ) + 5), hmpos.le]
        linarith
      have e1 : ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)
          = Real.sqrt (((m : ℝ) + 1) ^ 3) := by
        rw [show ((m : ℝ) + 1) ^ 3 = ((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) by ring,
          Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ 2),
          Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
      have e2 : 2 * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)
          = Real.sqrt (4 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
        rw [show (4 : ℝ) * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)
              = (2 * (4 * (m : ℝ) + 5)) ^ 2 * (m : ℝ) by ring,
          Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 * (4 * (m : ℝ) + 5)) ^ 2),
          Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * (4 * (m : ℝ) + 5))]
      rw [e1, e2]
      exact Real.sqrt_le_sqrt hsq
    have hden1 : 0 < α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ) := by
      have h1 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos hmpos
      positivity
    have hden2 : 0 < α * Real.sqrt ((m : ℝ) + 1) := by
      have h1 : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos_of_pos (by positivity)
      positivity
    have hcoef : ((m : ℝ) + 1) / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))
        ≤ 2 / (α * Real.sqrt ((m : ℝ) + 1)) := by
      rw [div_le_div_iff₀ hden1 hden2]
      nlinarith [hnum, hα]
    calc ((m : ℝ) + 1) * |Work.FTS.PhiStar.Radial.radGreen α m d z|
        ≤ ((m : ℝ) + 1) * (S * Z / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (S * Z) * (((m : ℝ) + 1) / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))) := by ring
      _ ≤ (S * Z) * (2 / (α * Real.sqrt ((m : ℝ) + 1))) := mul_le_mul_of_nonneg_left hcoef hSZ
      _ = (2 / α) * S * Z / Real.sqrt ((m : ℝ) + 1) := by ring

/-- **The sharp `L²` difference bound for the modal Green function.**  For `0 < α ≤ 1/4`,
`m : ℕ`, `z > 0` and two `L²((0,∞))` sources `c`, `c'` (a.e. strongly measurable),

  `(m+1)·|radGreen α m c' z - radGreen α m c z| ≤ (2/α)·√(∫_0^∞ (c'-c)²)·z^(-1/2)/√(m+1)`.

The `m = 0` case is the borderline one: `radGreen α 0` has `rgP α 0 = 0` and does not decay, so
`Work.EllipticEst.ModalSolution.radGreen_abs_le` (which needs `m ≥ 1`) does not apply there; use
`Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all` for it.

Recipe. (1) *Additivity*: for a.e.-strongly-measurable `L²` sources the two Green integrals are
honest (on `(0,z)` the integrand `t ↦ c t · t^(q-1)` is dominated by `(c t² + t^(2q-2))/2` with
`2q-2 > -1`, `q = (2m+5)/α ≥ 5`; on `(z,∞)` the integrand `t ↦ c t · t^(-p-1)` is dominated by
`(c t² + t^(-2p-2))/2` with `2p+2 > 1`, `p = 2m/α ≥ 0`), so `∫₀^z` and `∫_z^∞` are additive and
`radGreen α m c' z - radGreen α m c z = radGreen α m (fun t => c' t - c t) z`.
(2) `IntegrableOn (fun t => (c' t - c t)²) (Ioi 0)` from `(a-b)² ≤ 2a²+2b²`.
(3) Apply `radGreen_abs_le` at `c' - c` for `m ≥ 1` and `radGreen_abs_le_all` for `m = 0`, and
use the arithmetic `(m+1)/((4m+5)√m) ≤ 2/√(m+1)` (`m ≥ 1`): it is equivalent to
`(m+1)³ ≤ 4(4m+5)²m`. -/
theorem radGreen_diff_abs_le {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ)
    {c c' : ℝ → ℝ}
    (hc : MeasureTheory.AEStronglyMeasurable c
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc' : MeasureTheory.AEStronglyMeasurable c'
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hc2 : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioi 0))
    (hc'2 : MeasureTheory.IntegrableOn (fun t : ℝ => c' t ^ 2) (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    ((m : ℝ) + 1) * |Work.FTS.PhiStar.Radial.radGreen α m c' z
        - Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ (2 / α) * Real.sqrt (∫ t in Set.Ioi 0, (c' t - c t) ^ 2)
          * z ^ (-(1 / 2) : ℝ) / Real.sqrt ((m : ℝ) + 1) := by
  have hdae : AEStronglyMeasurable (fun t : ℝ => c' t - c t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := hc'.sub hc
  have hd2 : IntegrableOn (fun t : ℝ => (c' t - c t) ^ 2) (Ioi 0) := by
    have hdom : IntegrableOn (fun t : ℝ => 2 * c' t ^ 2 + 2 * c t ^ 2) (Ioi 0) :=
      (hc'2.const_mul 2).add (hc2.const_mul 2)
    refine hdom.mono' (hdae.pow 2) ?_
    filter_upwards with t
    have hkey : (c' t - c t) ^ 2 ≤ 2 * c' t ^ 2 + 2 * c t ^ 2 := by
      nlinarith [sq_nonneg (c' t + c t)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (c' t - c t))]
    exact hkey
  rw [← Work.FTS.PhiStar.Honesty.DiffGreen.radGreen_sub (c := c) (c' := c')
    hα hα4 m hc hc' hc2 hc'2 hz]
  exact green_value_le (d := fun t => c' t - c t) hα hα4 m hd2 hz

end Work.FTS.PhiStar.Honesty.DiffGreen
