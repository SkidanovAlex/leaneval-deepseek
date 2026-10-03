/-
# The sharp denominator bound `T ≤ 2^{2^{2ρl} - 2}` for the Ionescu–Wainger set `P_{≤l}`

Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial averages*,
Annals of Math. 195 (2022), Appendix A.  In the second regime `l > iwC0 ρ` every element of the
Ionescu–Wainger denominator set `P_{≤l}` is of the form `Q · w` with `Q ∣ Q_0^{(l)}` and
`w ∈ W_{≤l}`, and

  `Q_0^{(l)} ≤ (N_0^{(l)})^{N_0^{(l)} D_ρ}`,  `w ≤ (2^l)^{D_ρ²}`,

so that the "denominator size"

  `T := Q_0^{(l)} · (2^l)^{D_ρ²}`

is an upper bound for every element of `P_{≤l}` (and, being a natural number contained in `[1, T]`,
`P_{≤l}` has both its cardinality and its largest element at most `T`).

The lemma proved here is the *sharp* form of `Work.KMTAreas.A7.lp_T_le`: instead of
`4 T² ≤ 2^{2·2^{2ρl}}` (which only gives `T ≤ 2^{2^{2ρl}-1}` after taking square roots) we prove
the linear bound

  `T ≤ 2^{2^{2ρl} - 2}`

for **every** `0 < ρ ≤ 1` (the sibling `lp_T_le` is only proved for `ρ ≤ 1/8`).

## The estimate

Writing `x := ρ l / 2`, so that `2^{4x} = 2^{2ρl}`, and using `ρ ≤ 1` together with
`l > iwC0 ρ ≥ max(4/ρ² + 2/ρ, 10/ρ + 100)` (the sharpened bounds `lp_iwC0_ge_sharp`,
`lp_iwC0_ge_lin`):

* `x > 2/ρ + 1 > 4` (whence `x ≥ 4`), and `1/ρ < x/2`;
* `D_ρ ≤ 3x/2` and `l ≤ x²`;
* `N_0^{(l)} ≤ 2^{x+1}`;

hence `T ≤ 2^K` with `K := (x+1)·N_0^{(l)}·D_ρ + l·D_ρ² ≤ 6x²2^x + 2.25x⁴`, and the elementary
numeric core `lp_core_sharp` (`6x²2^x + 2.25x⁴ + 2 ≤ 2^{4x}` for `x ≥ 4`, proved from
`v² ≤ 2^v`) gives `K + 2 ≤ 2^{4x} = 2^{2ρl}`, i.e. `T ≤ 2^{2^{2ρl}-2}`.

## Main result

* `Work.KMTAreas.A7.lp_T_le_sharp`
-/
import Mathlib
import Submission.Work.KMTAreas.A7.uRepNonAliasAux

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open scoped BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- `v² ≤ 2^v` for `v ≥ 4` (equality at `v = 4`).  This is the elementary exponential-domination
estimate underlying the whole estimate; it is a copy of the `private` lemma
`Work.Analysis.IonescuWainger.sq_le_two_rpow` of `iw_height_card_le`. -/
private lemma lp_sq_le_two_rpow {v : ℝ} (hv : 4 ≤ v) : v ^ 2 ≤ (2 : ℝ) ^ v := by
  set s : ℝ := v / 4 - 1 with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hveq : v = 4 * (1 + s) := by rw [hs]; ring
  have h1 : (1 + s) ^ 2 ≤ Real.exp (2 * s) := by
    have h := Real.add_one_le_exp s
    have h2 : (1 + s) ^ 2 ≤ (Real.exp s) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h3 : (Real.exp s) ^ 2 = Real.exp (2 * s) := by
      rw [show (2 : ℝ) * s = (2 : ℕ) * s by norm_num, Real.exp_nat_mul]
    rwa [h3] at h2
  have he2 : (Real.exp 1) ^ 2 ≤ 16 := by
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have h4 : Real.exp (2 * s) ≤ (2 : ℝ) ^ (4 * s) := by
    have hexp : Real.exp (2 * s) = ((Real.exp 1) ^ 2) ^ s := by
      rw [Real.exp_mul]
      have h2 : Real.exp 2 = (Real.exp 1) ^ 2 := by simpa using Real.exp_nat_mul 1 2
      rw [h2]
    rw [hexp]
    have h16 : (16 : ℝ) ^ s = (2 : ℝ) ^ (4 * s) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [← h16]
    exact Real.rpow_le_rpow (by positivity) he2 hs0
  calc v ^ 2 = 16 * (1 + s) ^ 2 := by rw [hveq]; ring
    _ ≤ 16 * Real.exp (2 * s) := by linarith
    _ ≤ 16 * (2 : ℝ) ^ (4 * s) := by linarith
    _ = (2 : ℝ) ^ (4 * (1 + s)) := by
        rw [show (4 : ℝ) * (1 + s) = 4 + 4 * s by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
    _ = (2 : ℝ) ^ v := by rw [hveq]

/-- **The elementary numeric core of the sharp estimate.**  For `x ≥ 4`,

  `6x²2^x + 2.25x⁴ + 2 ≤ 2^{4x}`.

This is the sharpened form of `lp_numeric_core` / `lp_numeric_core2` (which are stated for
`x ≥ 16`, the threshold forced by the auxiliary estimate `lp_two_rpow_ge` used there): the
argument here uses only `x² ≤ 2^x` and hence applies at the much smaller threshold `x ≥ 4`,
which is what the general regime `0 < ρ ≤ 1` provides. -/
private lemma lp_core_sharp {x : ℝ} (hx : 4 ≤ x) :
    6 * x ^ 2 * (2 : ℝ) ^ x + 2.25 * x ^ 4 + 2 ≤ (2 : ℝ) ^ (4 * x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxsq : x ^ 2 ≤ (2 : ℝ) ^ x := lp_sq_le_two_rpow hx
  have h2xpos : (0 : ℝ) < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
  have hx2nn : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have hpow4 : (2 : ℝ) ^ (4 * x) = (2 : ℝ) ^ (4 * x - 1) * 2 := by
    have e : (4 : ℝ) * x = (4 * x - 1) + 1 := by ring
    conv_lhs => rw [e]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hhalve : (2 : ℝ) ^ (4 * x) / 2 = (2 : ℝ) ^ (4 * x - 1) := by
    rw [hpow4]; ring
  have hA : 6 * x ^ 2 * (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (4 * x) / 2 := by
    have h12 : 12 * x ^ 2 ≤ (2 : ℝ) ^ (3 * x) := by
      have hs : 12 * x ^ 2 ≤ 16 * x ^ 2 := by nlinarith [hx2nn]
      have hs' : 16 * x ^ 2 ≤ 16 * (2 : ℝ) ^ x := by linarith [hxsq]
      have h16 : (16 : ℝ) * (2 : ℝ) ^ x = (2 : ℝ) ^ (x + 4) := by
        have e : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
        rw [e, ← Real.rpow_natCast (2 : ℝ) 4, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1; push_cast; ring
      have hle : (2 : ℝ) ^ (x + 4) ≤ (2 : ℝ) ^ (3 * x) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      linarith [hs, hs', h16.le, hle]
    have hmul : 12 * x ^ 2 * (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (4 * x) := by
      have h1 := mul_le_mul_of_nonneg_right h12 (le_of_lt h2xpos)
      have h2 : (2 : ℝ) ^ (3 * x) * (2 : ℝ) ^ x = (2 : ℝ) ^ (4 * x) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      linarith [h1, h2.le, h2.ge]
    calc 6 * x ^ 2 * (2 : ℝ) ^ x = (12 * x ^ 2 * (2 : ℝ) ^ x) / 2 := by ring
      _ ≤ (2 : ℝ) ^ (4 * x) / 2 := div_le_div_of_nonneg_right hmul (by norm_num)
  have hB : 2.25 * x ^ 4 + 2 ≤ (2 : ℝ) ^ (4 * x) / 2 := by
    have hx4 : x ^ 4 ≤ (2 : ℝ) ^ (2 * x) := by
      have h := pow_le_pow_left₀ (sq_nonneg x) hxsq 2
      have e1 : (x ^ 2) ^ 2 = x ^ 4 := by ring
      have e2 : ((2 : ℝ) ^ x) ^ 2 = (2 : ℝ) ^ (2 * x) := by
        rw [lp_rpow_pow (2 : ℝ) x (by norm_num) 2]
        congr 1; ring
      linarith [h, e1.le, e1.ge, e2.le, e2.ge]
    have h1 : 2.25 * x ^ 4 ≤ (2 : ℝ) ^ (2 * x + 2) := by
      have h2 : 2.25 * x ^ 4 ≤ 2.25 * (2 : ℝ) ^ (2 * x) := by linarith [hx4]
      have h3 : 2.25 * (2 : ℝ) ^ (2 * x) ≤ 4 * (2 : ℝ) ^ (2 * x) := by
        have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (2 * x)
        nlinarith
      have h4 : (4 : ℝ) * (2 : ℝ) ^ (2 * x) = (2 : ℝ) ^ (2 * x + 2) := by
        have e : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
        rw [e, ← Real.rpow_natCast (2 : ℝ) 2, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1; push_cast; ring
      linarith [h2, h3, h4.le, h4.ge]
    have h2 : (2 : ℝ) ^ (2 * x + 2) + 2 ≤ (2 : ℝ) ^ (2 * x + 3) := by
      have h3 : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * x + 2) := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (show (1 : ℝ) ≤ 2 * x + 2 by linarith)
        simpa using h
      have h4 : (2 : ℝ) ^ (2 * x + 3) = (2 : ℝ) ^ (2 * x + 2) * 2 := by
        have e : (2 : ℝ) * x + 3 = (2 * x + 2) + 1 := by ring
        conv_lhs => rw [e]
        rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
      linarith [h3, h4.le, h4.ge]
    have h5 : (2 : ℝ) ^ (2 * x + 3) ≤ (2 : ℝ) ^ (4 * x - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [hhalve]
    linarith [h1, h2, h5]
  linarith [hA, hB]

/-- **The sharp denominator bound** for the Ionescu–Wainger set `P_{≤l}`:
for `0 < ρ ≤ 1` and `l > iwC0 ρ`,

  `Q_0^{(l)} · (2^l)^{D_ρ²} ≤ 2^{2^{2ρl} - 2}`. -/
theorem lp_T_le_sharp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ} (hl : Work.Analysis.IonescuWainger.iwC0 ρ < l) :
    ((Work.Analysis.IonescuWainger.iwQ0 ρ l * (2 ^ l) ^ (Work.Analysis.IonescuWainger.iwD ρ * Work.Analysis.IonescuWainger.iwD ρ) : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (2 * ρ * (l : ℝ)) - 2) := by
  have hρne : ρ ≠ 0 := hρ.ne'
  set x : ℝ := ρ * (l : ℝ) / 2 with hx
  have hlR : (iwC0 ρ : ℝ) < (l : ℝ) := by exact_mod_cast hl
  -- lower bounds on `x`
  have hxgt : 2 / ρ + 1 < x := by
    have h2 : 4 / ρ ^ 2 + 2 / ρ < (l : ℝ) :=
      lt_of_le_of_lt (lp_iwC0_ge_sharp hρ) hlR
    have h3 : 4 / ρ + 2 < ρ * (l : ℝ) := by
      have h := mul_lt_mul_of_pos_left h2 hρ
      have h4 : ρ * (4 / ρ ^ 2 + 2 / ρ) = 4 / ρ + 2 := by field_simp <;> ring
      linarith [h, h4.le, h4.ge]
    have h5 : (4 / ρ + 2) / 2 < ρ * (l : ℝ) / 2 := div_lt_div_of_pos_right h3 (by norm_num)
    have h6 : (4 / ρ + 2) / 2 = 2 / ρ + 1 := by ring_nf
    rw [hx]
    linarith [h5, h6.le, h6.ge]
  have hxlin : 5 + 50 * ρ < x := by
    have h2 : 10 / ρ + 100 < (l : ℝ) :=
      lt_of_le_of_lt (lp_iwC0_ge_lin hρ) hlR
    have h3 : 10 + 100 * ρ < ρ * (l : ℝ) := by
      have h := mul_lt_mul_of_pos_left h2 hρ
      have h4 : ρ * (10 / ρ + 100) = 10 + 100 * ρ := by field_simp <;> ring
      linarith [h, h4.le, h4.ge]
    have h5 : (10 + 100 * ρ) / 2 < ρ * (l : ℝ) / 2 := div_lt_div_of_pos_right h3 (by norm_num)
    have h6 : (10 + 100 * ρ) / 2 = 5 + 50 * ρ := by ring
    rw [hx]
    linarith [h5, h6.le, h6.ge]
  -- the numeric core applies at `x ≥ 4`
  have hx4 : 4 ≤ x := by
    rcases le_or_gt ρ (1 / 4) with hρq | hρq
    · have h2 : 8 ≤ 2 / ρ := by
        rw [le_div_iff₀ hρ]
        nlinarith
      linarith
    · have h2 : 17 ≤ 5 + 50 * ρ := by nlinarith
      linarith
  have hρx : 2 < x * ρ := by
    have h : 1 / ρ < x / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hid : (2 : ℝ) / ρ = 1 / ρ * 2 := by ring
      linarith [hxgt]
    have h2 : 1 / ρ * ρ < x / 2 * ρ := mul_lt_mul_of_pos_right h hρ
    rw [div_mul_cancel₀ 1 (ne_of_gt hρ)] at h2
    linarith
  have hD : (iwD ρ : ℝ) ≤ 3 * x / 2 := by
    have h1 := lp_iwD_le ρ hρ
    have h2 : (1 : ℝ) ≤ x / 2 := by linarith
    have h3 : 2 / ρ + 1 < x + 1 := by linarith
    have h4 : x + 1 ≤ 3 * x / 2 := by linarith
    linarith
  have hl_le : (l : ℝ) ≤ x ^ 2 := by
    have h2x : (l : ℝ) = 2 * x / ρ := by rw [hx]; field_simp
    rw [h2x, div_le_iff₀ hρ]
    nlinarith [hρx, le_of_lt (by positivity : (0 : ℝ) < x)]
  have hn0 : ((iwN0 ρ l : ℕ) : ℝ) ≤ (2 : ℝ) ^ (x + 1) := by
    have h := lp_iwN0_le_two ρ hρ.le l
    have hy : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) = (2 : ℝ) ^ x := by rw [hx]
    rw [hy] at h
    calc (iwN0 ρ l : ℝ) ≤ 2 * (2 : ℝ) ^ x := h
      _ = (2 : ℝ) ^ (x + 1) := by
          rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
          ring
  have hQ : (iwQ0 ρ l : ℝ) ≤ ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ) := by
    have := lp_iwQ0_le ρ l
    exact_mod_cast this
  set T : ℝ := ((iwQ0 ρ l * (2 ^ l) ^ (iwD ρ * iwD ρ) : ℕ) : ℝ) with hTdef
  have hT1 : T ≤ ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ)
      * ((2 : ℝ) ^ l) ^ (iwD ρ * iwD ρ) := by
    rw [hTdef]
    push_cast
    exact mul_le_mul hQ le_rfl (by positivity) (by positivity)
  set K : ℝ := (x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ)
    + (l : ℝ) * ((iwD ρ : ℝ)) ^ 2 with hK
  have hDnn : (0 : ℝ) ≤ (iwD ρ : ℝ) := by positivity
  have hT2 : ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ)
        * ((2 : ℝ) ^ l) ^ (iwD ρ * iwD ρ) ≤ (2 : ℝ) ^ K := by
    have h1 : ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ)
        ≤ (2 : ℝ) ^ ((x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ)) := by
      have hstep : ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ)
          ≤ ((2 : ℝ) ^ (x + 1)) ^ (iwN0 ρ l * iwD ρ) :=
        pow_le_pow_left₀ (by positivity) hn0 _
      have hp := lp_rpow_pow (2 : ℝ) (x + 1) (by norm_num) (iwN0 ρ l * iwD ρ)
      rw [hp] at hstep
      refine hstep.trans ?_
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hcast : (((iwN0 ρ l) * iwD ρ : ℕ) : ℝ)
          = ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ) := by push_cast; ring
      rw [hcast]
      nlinarith [hn0, hDnn, hx4]
    have h2 : ((2 : ℝ) ^ l) ^ (iwD ρ * iwD ρ)
        = (2 : ℝ) ^ ((l : ℝ) * (iwD ρ : ℝ) ^ 2) := by
      rw [← Real.rpow_natCast (2 : ℝ) l]
      rw [lp_rpow_pow (2 : ℝ) (l : ℝ) (by norm_num) (iwD ρ * iwD ρ)]
      congr 1
      push_cast
      ring
    have hmul : ((iwN0 ρ l : ℕ) : ℝ) ^ (iwN0 ρ l * iwD ρ) * ((2 : ℝ) ^ l) ^ (iwD ρ * iwD ρ)
        ≤ (2 : ℝ) ^ ((x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ))
          * (2 : ℝ) ^ ((l : ℝ) * (iwD ρ : ℝ) ^ 2) := by
      refine mul_le_mul h1 ?_ (by positivity) (by positivity)
      rw [h2]
    rw [hK]
    refine hmul.trans (le_of_eq ?_)
    exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2)
      ((x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ)) ((l : ℝ) * (iwD ρ : ℝ) ^ 2)).symm
  have hTle : T ≤ (2 : ℝ) ^ K := hT1.trans hT2
  have hKbound : K + 2 ≤ (2 : ℝ) ^ (4 * x) := by
    have h3 : (x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ) ≤ 6 * x ^ 2 * (2 : ℝ) ^ x := by
      have h2x : (2 : ℝ) ^ (x + 1) = 2 * (2 : ℝ) ^ x := by
        rw [Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
        ring
      have hstep : (x + 1) * ((iwN0 ρ l : ℕ) : ℝ) * (iwD ρ : ℝ)
          ≤ (x + 1) * (2 : ℝ) ^ (x + 1) * (iwD ρ : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hn0 (by positivity : (0 : ℝ) ≤ (iwD ρ : ℝ))
        nlinarith
      have hkey : (x + 1) * (iwD ρ : ℝ) ≤ 3 * x ^ 2 := by
        have h1 : (x + 1) * (iwD ρ : ℝ) ≤ (x + 1) * (3 * x / 2) :=
          mul_le_mul_of_nonneg_left hD (by linarith)
        nlinarith [h1, hx4]
      rw [h2x] at hstep
      nlinarith [hstep, hkey, show (0 : ℝ) < (2 : ℝ) ^ x from Real.rpow_pos_of_pos (by norm_num) _]
    have h4 : (l : ℝ) * ((iwD ρ : ℝ)) ^ 2 ≤ 2.25 * x ^ 4 := by
      have hD2 : ((iwD ρ : ℝ)) ^ 2 ≤ (3 * x / 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hD 2
      have h := mul_le_mul hl_le hD2 (by positivity) (by positivity)
      nlinarith [h]
    have hcore := lp_core_sharp hx4
    rw [hK]
    linarith
  have h4x : (2 : ℝ) ^ (4 * x) = (2 : ℝ) ^ (2 * ρ * (l : ℝ)) := by
    congr 1
    rw [hx]; ring
  refine hTle.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  rw [← h4x]
  linarith

end

end Work.KMTAreas.A7
