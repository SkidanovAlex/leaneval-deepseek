import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.approxEcal_end_in_imag_neg_small
import Submission.Work.PARIMPL2.approxEcal_end_in_small

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Complex
open Work.Implosion

namespace Work.PARIMPL2.Lavaurs

noncomputable section

/-! ## Adding principal logarithms

A companion of the delegated `Work.PARIMPL2.Lavaurs.log_add_log_of_re_pos`, proved here so
that this file is self-contained. -/

/-- **Principal logarithms add when the second factor and the product lie in the right
half-plane.**  For `x y : ℂ` with `x ≠ 0`, `y ≠ 0`, `0 < y.re` and `0 < (x*y).re` one has
`log x + log y = log (x*y)` for the principal branch.

`arg y ∈ (-π/2, π/2)` and `arg (x*y) ∈ (-π/2, π/2)` (from the positive real parts), while
`arg x ∈ (-π, π]` always; hence `θ = arg x + arg y ∈ (-3π/2, 3π/2)`, and `θ ≡ arg (x*y)`
mod `2π` by `arg_mul_coe_angle`, so `θ = arg (x*y) ∈ (-π, π]` and `Complex.log_mul`
applies. -/
private lemma log_add_log_of_re_pos_aux {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hyr : 0 < y.re) (hxyr : 0 < (x * y).re) :
    Complex.log x + Complex.log y = Complex.log (x * y) := by
  have hyarg : |y.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hyr)
  have hxyarg : |(x * y).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hxyr)
  have hang : ((x.arg + y.arg : ℝ) : Real.Angle) = ((x * y).arg : Real.Angle) := by
    rw [Real.Angle.coe_add, Complex.arg_mul_coe_angle hx hy]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlo : -(2 * Real.pi) < x.arg + y.arg - (x * y).arg := by
    have h1 := Complex.neg_pi_lt_arg x
    have h2 := (abs_lt.mp hyarg).1
    have h3 := (abs_lt.mp hxyarg).2
    linarith
  have hhi : x.arg + y.arg - (x * y).arg < 2 * Real.pi := by
    have h1 := Complex.arg_le_pi x
    have h2 := (abs_lt.mp hyarg).2
    have h3 := (abs_lt.mp hxyarg).1
    linarith
  have hkR : |(k : ℝ)| < 1 := by
    have h2 : |2 * Real.pi * (k : ℝ)| < 2 * Real.pi := by
      rw [abs_lt]
      exact ⟨by rw [← hk]; linarith, by rw [← hk]; linarith⟩
    rw [abs_mul, abs_of_pos h2pi] at h2
    have h3 : 2 * Real.pi * |(k : ℝ)| < 2 * Real.pi * 1 := by simpa using h2
    exact (mul_lt_mul_iff_right₀ h2pi).mp h3
  have hk0 : k = 0 := by
    have h1 : (0 : ℤ) ≤ k := by
      by_contra h
      have h' : k ≤ -1 := by omega
      have h'' : (k : ℝ) ≤ -1 := by exact_mod_cast h'
      have := (abs_lt.mp hkR).1
      linarith
    have h2 : k ≤ 0 := by
      by_contra h
      have h' : 1 ≤ k := by omega
      have h'' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h'
      have := (abs_lt.mp hkR).2
      linarith
    omega
  have hcond : x.arg + y.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hk' : x.arg + y.arg - (x * y).arg = 0 := by rw [hk, hk0]; ring
    have h1 : x.arg + y.arg = (x * y).arg := by linarith
    rw [h1]
    have h2 := abs_lt.mp hxyarg
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  exact (Complex.log_mul hx hy hcond).symm

/-! ## Elementary `cosh`/`log` bounds near `0` -/

private lemma cosh_sub_one_le' {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖Complex.cosh w - 1‖ ≤ ‖w‖ ^ 2 := by
  have h1 : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hw
  have h2 : ‖Complex.exp (-w) - 1 - (-w)‖ ≤ ‖w‖ ^ 2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le (x := -w) (by rwa [norm_neg])
    rwa [norm_neg] at h
  have hdecomp : Complex.cosh w - 1
      = ((Complex.exp w - 1 - w) + (Complex.exp (-w) - 1 - (-w))) / 2 := by
    rw [Complex.cosh]; ring
  rw [hdecomp, norm_div, Complex.norm_ofNat]
  have hsum : ‖(Complex.exp w - 1 - w) + (Complex.exp (-w) - 1 - (-w))‖ ≤ 2 * ‖w‖ ^ 2 := by
    calc ‖(Complex.exp w - 1 - w) + (Complex.exp (-w) - 1 - (-w))‖
        ≤ ‖Complex.exp w - 1 - w‖ + ‖Complex.exp (-w) - 1 - (-w)‖ := norm_add_le _ _
      _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := add_le_add h1 h2
      _ = 2 * ‖w‖ ^ 2 := by ring
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

private lemma re_cosh_pos' {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : 0 < (Complex.cosh w).re := by
  have h1 : ‖Complex.cosh w - 1‖ ≤ ‖w‖ ^ 2 := cosh_sub_one_le' (by linarith)
  have h2 : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w, hw]
  have h3 := Complex.abs_re_le_norm (Complex.cosh w - 1)
  have h4 : (Complex.cosh w).re = 1 + (Complex.cosh w - 1).re := by
    rw [Complex.sub_re, Complex.one_re]; ring
  rw [h4]
  have h5 : -‖Complex.cosh w - 1‖ ≤ (Complex.cosh w - 1).re := by
    have := (abs_le.mp h3).1; linarith
  linarith

private lemma norm_log_cosh_le' {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (Complex.cosh w)‖ ≤ 3 / 2 * ‖w‖ ^ 2 := by
  have h1 : ‖Complex.cosh w - 1‖ ≤ ‖w‖ ^ 2 := cosh_sub_one_le' (by linarith)
  have h2 : ‖w‖ ^ 2 ≤ 1 / 2 := by nlinarith [norm_nonneg w, hw]
  have hz : ‖Complex.cosh w - 1‖ ≤ 1 / 2 := le_trans h1 h2
  have h3 := Complex.norm_log_one_add_half_le_self hz
  have heq : Complex.log (Complex.cosh w) = Complex.log (1 + (Complex.cosh w - 1)) := by
    congr 1; ring
  rw [heq]
  calc ‖Complex.log (1 + (Complex.cosh w - 1))‖ ≤ 3 / 2 * ‖Complex.cosh w - 1‖ := h3
    _ ≤ 3 / 2 * ‖w‖ ^ 2 := by linarith

/-! ## From `sinh = 0` back to `e^{2w} = 1` -/

/-- `e^{2w} = 1` as soon as `sinh w = 0`: the identity `e^{2w} - 1 = 2 e^w sinh w` kills the
right-hand side. -/
private lemma exp_two_mul_eq_one_of_sinh_eq_zero {w : ℂ} (h : Complex.sinh w = 0) :
    Complex.exp (2 * w) = 1 := by
  have h1 : Complex.exp w * Complex.exp w = Complex.exp (2 * w) := by
    rw [show (2 : ℂ) * w = w + w by ring, Complex.exp_add]
  have h2 : Complex.exp w * Complex.exp (-w) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have h3 : 2 * Complex.exp w * Complex.sinh w = Complex.exp (2 * w) - 1 := by
    rw [Complex.sinh]
    have h4 : 2 * Complex.exp w * ((Complex.exp w - Complex.exp (-w)) / 2)
        = Complex.exp w * Complex.exp w - Complex.exp w * Complex.exp (-w) := by ring
    rw [h4, h2, h1]
  have hz : Complex.exp (2 * w) - 1 = 0 := by rw [← h3, h, mul_zero]
  exact sub_eq_zero.mp hz

/-! ## The main estimate, in the branch-free form -/

/-- The estimate is proved for an arbitrary `a ≠ 0` in the region `4‖a‖ ≤ ‖ζ‖`,
`ζ.re < 0`, `‖ζ‖ ≤ 4`; **no** hypothesis on the branch of `sinh (a·u)/a` is needed, because
both factors `-sinh (a·u)/a` and `-ζ` of the product `cosh (a·u)` have positive real part,
so their principal logarithms add (`log_add_log_of_re_pos_aux`). -/
private theorem approxEcal_end_in_small_sum_aux (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a κ ζ : ℂ), a ≠ 0 → ‖κ‖ ≤ K → ζ.re < 0 → ‖ζ‖ ≤ 4 →
      4 * ‖a‖ ≤ ‖ζ‖ →
      ‖approxEcal a κ (ecalCoord a ζ + Real.pi * I / a)
        - (Real.pi * I / a + ((1 / ζ) - κ * Complex.log (-ζ)))‖
      ≤ C * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by
  refine ⟨4 / 9 + 24 * K, by linarith, ?_⟩
  intro a κ ζ ha hκ hre hζle haζ
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hζpos : 0 < ‖ζ‖ := by linarith
  have hζne : ζ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hζpos)
  have hlt : ‖a‖ < ‖ζ‖ := by linarith
  have hza : ζ ≠ a := by intro h; rw [h] at hlt; exact absurd hlt (lt_irrefl _)
  have hzna : ζ ≠ -a := by intro h; rw [h, norm_neg] at hlt; exact absurd hlt (lt_irrefl _)
  set u : ℂ := ecalCoord a ζ with hudef
  have hu_sub : ‖u - 1/ζ‖ ≤ 4/9 * ‖a‖^2/‖ζ‖^3 := by
    rw [hudef]; exact ecalCoord_sub_inv_le_small a ζ ha hζne haζ
  have hhalf : ‖a * u‖ ≤ 1/2 := by
    rw [hudef]; exact a_mul_ecalCoord_le_half a ζ ha hζne haζ
  have hu_le : ‖u‖ ≤ 2/‖ζ‖ := by
    rw [hudef]; exact ecalCoord_norm_le_small a ζ ha hζne haζ
  have hau_le : ‖a * u‖ ≤ 2 * ‖a‖/‖ζ‖ := by
    rw [norm_mul]
    calc ‖a‖ * ‖u‖ ≤ ‖a‖ * (2/‖ζ‖) := mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ = 2 * ‖a‖/‖ζ‖ := by ring
  -- the multiplier coordinate `e^{2au}` is the Möbius coordinate of `ζ`
  have hmob_ne : mobius a ζ ≠ 0 := (mobius_ne_zero_iff a ζ).mpr ⟨hzna, hza⟩
  have hmob_ne_one : mobius a ζ ≠ 1 := by
    intro h
    have hden : ζ - a ≠ 0 := sub_ne_zero.mpr hza
    rw [mobius, div_eq_one_iff_eq hden] at h
    have h2a : (2 : ℂ) * a = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2a with h2 | ha0
    · exact absurd h2 (by norm_num)
    · exact ha ha0
  have hE : ecalE a u = mobius a ζ := by
    rw [hudef, ecalE, ecalCoord]
    have h2 : 2 * a * (Complex.log (mobius a ζ) / (2 * a)) = Complex.log (mobius a ζ) := by
      field_simp
    rw [h2, Complex.exp_log hmob_ne]
  have hEne : ecalE a u ≠ 1 := by rw [hE]; exact hmob_ne_one
  have hsinh_ne : Complex.sinh (a * u) ≠ 0 := by
    intro hcon
    have h2 : Complex.exp (2 * (a * u)) = 1 := exp_two_mul_eq_one_of_sinh_eq_zero hcon
    have h3 : ecalE a u = 1 := by
      rw [ecalE, show (2 : ℂ) * a * u = 2 * (a * u) by ring]
      exact h2
    rw [hE] at h3
    exact hmob_ne_one h3
  -- the coth identity gives `(sinh (a·u)/a) · ζ = cosh (a·u)`
  have hpt : ecalPt a u = ζ := by
    rw [hudef]; exact ecalPt_ecalCoord a ζ ha hza hzna
  have hcoth : ecalPt a u = a * coth (a * u) := Ecalle.ecallePt_eq_coth a u hEne
  have hζeq : ζ = a * (Complex.cosh (a * u) / Complex.sinh (a * u)) := by
    rw [← hpt, hcoth, coth]
  have hmul : ζ * Complex.sinh (a * u) = a * Complex.cosh (a * u) := by
    rw [hζeq]; field_simp; try ring
  have hwζ : (Complex.sinh (a * u)/a) * ζ = Complex.cosh (a * u) := by
    rw [div_mul_eq_mul_div, mul_comm (Complex.sinh (a * u)) ζ, hmul, mul_div_cancel_left₀ _ ha]
  have hcpos : 0 < (Complex.cosh (a * u)).re := re_cosh_pos' hhalf
  have hcne : Complex.cosh (a * u) ≠ 0 := by
    intro h; rw [h] at hcpos; exact absurd hcpos (by simp)
  have hw0 : Complex.sinh (a * u)/a ≠ 0 := by
    intro h; refine hcne ?_
    rw [← hwζ, h, zero_mul]
  -- the branch-free logarithm identity
  have hlogid : Complex.log (-(Complex.sinh (a * u)/a)) + Complex.log (-ζ)
      = Complex.log (Complex.cosh (a * u)) := by
    have hx : -(Complex.sinh (a * u)/a) ≠ 0 := neg_ne_zero.mpr hw0
    have hy : -ζ ≠ 0 := neg_ne_zero.mpr hζne
    have hyr : 0 < (-ζ).re := by rw [Complex.neg_re]; linarith
    have hxyr : 0 < ((-(Complex.sinh (a * u)/a)) * (-ζ)).re := by
      rw [neg_mul_neg, hwζ]; exact hcpos
    have := log_add_log_of_re_pos_aux hx hy hyr hxyr
    simpa [neg_mul_neg, hwζ] using this
  -- the bound on `log (cosh (a·u))`
  have hlogc : ‖Complex.log (Complex.cosh (a * u))‖ ≤ 24 * ‖a‖^2/‖ζ‖^3 := by
    have h1 : ‖Complex.log (Complex.cosh (a * u))‖ ≤ 3/2 * ‖a * u‖^2 :=
      norm_log_cosh_le' hhalf
    have h2 : ‖a * u‖^2 ≤ 4 * ‖a‖^2/‖ζ‖^2 := by
      calc ‖a * u‖^2 ≤ (2 * ‖a‖/‖ζ‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hau_le 2
        _ = 4 * ‖a‖^2/‖ζ‖^2 := by ring
    have h3 : (3/2 : ℝ) * ‖a * u‖^2 ≤ 6 * ‖a‖^2/‖ζ‖^2 := by
      calc (3/2 : ℝ) * ‖a * u‖^2 ≤ (3/2) * (4 * ‖a‖^2/‖ζ‖^2) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = 6 * ‖a‖^2/‖ζ‖^2 := by ring
    have h4 : 6 * ‖a‖^2/‖ζ‖^2 ≤ 24 * ‖a‖^2/‖ζ‖^3 := by
      have hζp3 : 0 < ‖ζ‖^3 := pow_pos hζpos 3
      have hcoef : 0 ≤ 6 * ‖a‖^2/‖ζ‖^3 :=
        div_nonneg (mul_nonneg (by norm_num) (sq_nonneg ‖a‖)) (le_of_lt hζp3)
      have heq : 6 * ‖a‖^2/‖ζ‖^2 = (6 * ‖a‖^2/‖ζ‖^3) * ‖ζ‖ := by field_simp
      have hle : (6 * ‖a‖^2/‖ζ‖^3) * ‖ζ‖ ≤ (6 * ‖a‖^2/‖ζ‖^3) * 4 :=
        mul_le_mul_of_nonneg_left hζle hcoef
      have hrt : (6 * ‖a‖^2/‖ζ‖^3) * 4 = 24 * ‖a‖^2/‖ζ‖^3 := by ring
      linarith
    linarith
  -- the translate `u + πi/a` of the coordinate, with no branch hypothesis
  have hshift : approxEcal a κ (u + Real.pi * I / a)
      = u + Real.pi * I / a + κ * Complex.log (-(Complex.sinh (a * u)/a)) := by
    have ha' : a * (Real.pi * I / a) = Real.pi * I := by field_simp
    have harg : a * (u + Real.pi * I / a) = a * u + Real.pi * I := by rw [mul_add, ha']
    rw [approxEcal_apply, harg, Approx.sinh_add_pi_I (a * u), neg_div]
  have hmain : approxEcal a κ (u + Real.pi * I / a)
      - (Real.pi * I / a + ((1 / ζ) - κ * Complex.log (-ζ)))
      = (u - 1/ζ) + κ * (Complex.log (-(Complex.sinh (a * u)/a)) + Complex.log (-ζ)) := by
    rw [hshift]; ring
  rw [hmain, hlogid]
  calc ‖(u - 1/ζ) + κ * Complex.log (Complex.cosh (a * u))‖
      ≤ ‖u - 1/ζ‖ + ‖κ‖ * ‖Complex.log (Complex.cosh (a * u))‖ := by
        calc ‖(u - 1/ζ) + κ * Complex.log (Complex.cosh (a * u))‖
            ≤ ‖u - 1/ζ‖ + ‖κ * Complex.log (Complex.cosh (a * u))‖ := norm_add_le _ _
          _ = ‖u - 1/ζ‖ + ‖κ‖ * ‖Complex.log (Complex.cosh (a * u))‖ := by rw [norm_mul]
    _ ≤ 4/9 * ‖a‖^2/‖ζ‖^3 + K * (24 * ‖a‖^2/‖ζ‖^3) :=
        add_le_add hu_sub (mul_le_mul hκ hlogc (norm_nonneg _) hK)
    _ = (4/9 + 24 * K) * ‖a‖^2/‖ζ‖^3 := by ring

/-- **The incoming small-`ζ` asymptotics in the branch-free sum form.**  For `a = iλ`, `λ > 0`,
`ζ` in the left half-plane with `4λ ≤ ‖ζ‖ ≤ 4`, the incoming approximate coordinate satisfies

  `approxEcal (iλ) κ (ecalCoord (iλ) ζ + πi/(iλ))  =  π/λ + 1/ζ - κ log(-ζ) + O(λ²/‖ζ‖³)`,

with `log` the principal branch (fine, since `Re (-ζ) > 0`), *without* any branch hypothesis.

**Proof route (verified by a reviewer).**  With `a = iλ`, `u = ecalCoord a ζ`,
`w = sinh (a·u)/a`, the identity `w · ζ = cosh (a·u)` holds, and
`sinh (a·(u + πi/a))/a = -w`.  Since `Re c > 0` for `c = cosh (a·u)` (as `‖a·u‖ ≤ 1/2` follows from
`4λ ≤ ‖ζ‖`) and `arg (-ζ) ∈ (-π/2, π/2)`, `arg (-w) + arg (-ζ) ∈ (-3π/2, 3π/2)` is congruent to
`arg c ∈ (-π/2, π/2)` mod `2π`, hence equal to it: so `Complex.log_mul` gives
`log (-w) + log (-ζ) = log c` for *every* `ζ` in the region, including `Im ζ = 0`.  Therefore
LHS − RHS `= (u − 1/ζ) + κ log c`, with `‖u − 1/ζ‖ ≤ (4/9)λ²/‖ζ‖³`
(`Work.PARIMPL2.ecalCoord_sub_inv_le_small`, in `approxEcal_end_in_small`) and
`‖log c‖ ≤ (3/2)‖a u‖² ≤ 24·λ²/‖ζ‖³` using `‖ζ‖ ≤ 4`.  Constant `4/9 + 24K` works. -/
theorem approxEcal_end_in_small_sum (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℝ) (κ ζ : ℂ), 0 < lam → ‖κ‖ ≤ K → ζ.re < 0 →
      ‖ζ‖ ≤ 4 → 4 * lam ≤ ‖ζ‖ →
      ‖Work.Implosion.approxEcal ((lam : ℂ) * I) κ
          (Work.Implosion.ecalCoord ((lam : ℂ) * I) ζ + Real.pi * I / ((lam : ℂ) * I))
        - (Real.pi * I / ((lam : ℂ) * I) + ((1 / ζ) - κ * Complex.log (-ζ)))‖
      ≤ C * lam ^ 2 / ‖ζ‖ ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := approxEcal_end_in_small_sum_aux K hK
  refine ⟨C, hC0, ?_⟩
  intro lam κ ζ hlam hκ hre hζle hlamζ
  have ha : ((lam : ℂ) * I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero
  have hnorma : ‖((lam : ℂ) * I)‖ = lam := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    exact abs_of_pos hlam
  have h4 : 4 * ‖((lam : ℂ) * I)‖ ≤ ‖ζ‖ := by rw [hnorma]; exact hlamζ
  have h := hC ((lam : ℂ) * I) κ ζ ha hκ hre hζle h4
  rwa [hnorma] at h

end

end Work.PARIMPL2.Lavaurs
