import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.WinAuxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.winAux_geom` — the separation bound behind the image-sum estimate

The design `LEAD_DESIGN_formrowkin.md` §3 estimates the `m ≠ 0` image terms of the lattice sum by
the kernel `‖x + ℓ•m − y‖⁻⁶`, weighted by the window decay factor `(winD ℓ · / ℓ)³`.  This file
supplies the purely geometric inequality that makes that estimate summable:

    (winD ℓ x/ℓ)³ (winD ℓ y/ℓ)³ / ‖x + ℓ•latVec m − y‖⁶
      ≤ (ℓ⁶)⁻¹ 2⁻⁶ 3⁶ (1 + ‖latVec m‖)⁻⁶          (0 < ℓ, m ≠ 0).

**Proof.**  Let `a = winD ℓ x`, `b = winD ℓ y` (so `a ≤ ℓ/2`, `b ≤ ℓ/2`), `R = ‖latVec m‖ ≥ 1` and
`D = ‖x + ℓ•latVec m − y‖`.

* If `a = 0` or `b = 0` the left side vanishes.
* Otherwise `a, b > 0`, hence `‖x‖ = ℓ/2 − a` and `‖y‖ = ℓ/2 − b` (`winD` is the distance to the
  sphere), and the reverse triangle inequality gives the *key separation*

      D ≥ ‖ℓ•latVec m‖ − ‖x − y‖ ≥ ℓ R − (‖x‖ + ‖y‖) = ℓ (R − 1 + a/ℓ + b/ℓ) > 0.

  Writing `s = a/ℓ`, `t = b/ℓ ∈ (0, 1/2]` and `X = R − 1 + s + t`, monotonicity of `·⁻⁶` gives

      s³t³/D⁶ ≤ s³t³/(ℓ X)⁶ = ℓ⁻⁶ (st/X²)³,

  and the elementary two-variable bound (`winAux_st_core`, via `4st ≤ (s+t)²` and
  `(1+R)(s+t) ≤ 3X` — the latter being `3(R−1) + (s+t)(2−R) = (R−1)(3−(s+t)) + (s+t) ≥ 0`)

      st/X² ≤ 9/(4(1+R)²)

  closes it, since `(9/(4(1+R)²))³ = 2⁻⁶ 3⁶ (1+R)⁻⁶`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The elementary core.**  For `R ≥ 1` and `0 ≤ s, t ≤ 1/2`,

    s t / (R − 1 + s + t)² ≤ 9 / (4 (1 + R)²).

(This is the sharp `1/(4R²)` bound `st ≤ ((s+t)/2)²` combined with
`(1+R)(s+t) ≤ 3(R−1+s+t)`, which holds on `R ≥ 1`, `s+t ≤ 1`.) -/
lemma winAux_st_core {R s t : ℝ} (hR : 1 ≤ R) (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hs : s ≤ 1 / 2) (ht : t ≤ 1 / 2) :
    s * t / (R - 1 + s + t) ^ 2 ≤ 9 / (4 * (1 + R) ^ 2) := by
  have hX0 : 0 ≤ R - 1 + s + t := by linarith
  rcases eq_or_lt_of_le hX0 with h | h
  · -- the degenerate case `R = 1`, `s = t = 0`: both sides vanish/nonnegative
    have hs' : s = 0 := by linarith
    rw [← h, hs']
    norm_num
    positivity
  · rw [div_le_div_iff₀ (pow_pos h 2) (by positivity)]
    have h1 : 4 * s * t ≤ (s + t) ^ 2 := by nlinarith [sq_nonneg (s - t)]
    have h2 : (1 + R) * (s + t) ≤ 3 * (R - 1 + s + t) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) (by linarith : (0 : ℝ) ≤ 3 - (s + t))]
    have hA : (1 + R) ^ 2 * (4 * s * t) ≤ (1 + R) ^ 2 * (s + t) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have hB : ((1 + R) * (s + t)) ^ 2 ≤ (3 * (R - 1 + s + t)) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) h2 2
    nlinarith [hA, hB]

/-- **The algebraic core of the geometric bound**, with the three parameters `s, t ∈ (0, 1/2]`
(i.e. `winD ℓ x/ℓ`, `winD ℓ y/ℓ`), `R ≥ 1` (i.e. `‖latVec m‖`) and a lower bound `D` for the
separation `‖x + ℓ•latVec m − y‖`. -/
lemma winAux_geom_core {ℓ R s t D : ℝ} (hℓ : 0 < ℓ) (hR : 1 ≤ R)
    (hs0 : 0 < s) (ht0 : 0 < t) (hs : s ≤ 1 / 2) (ht : t ≤ 1 / 2)
    (hD : ℓ * (R - 1 + s + t) ≤ D) :
    s ^ 3 * t ^ 3 / D ^ 6
      ≤ (ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * ((1 + R) ^ 6)⁻¹ := by
  have hX : 0 < ℓ * (R - 1 + s + t) := by
    have : 0 < R - 1 + s + t := by linarith
    positivity
  have hD6 : (ℓ * (R - 1 + s + t)) ^ 6 ≤ D ^ 6 := pow_le_pow_left₀ hX.le hD 6
  have hkey : s ^ 3 * t ^ 3 / D ^ 6 ≤ s ^ 3 * t ^ 3 / (ℓ * (R - 1 + s + t)) ^ 6 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hX 6) hD6
  have hcore := winAux_st_core hR hs0.le ht0.le hs ht
  have h3 : (s * t / (R - 1 + s + t) ^ 2) ^ 3 ≤ (9 / (4 * (1 + R) ^ 2)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcore 3
  have hsplit : s ^ 3 * t ^ 3 / (ℓ * (R - 1 + s + t)) ^ 6
      = (ℓ ^ 6)⁻¹ * (s * t / (R - 1 + s + t) ^ 2) ^ 3 := by
    field_simp
  have hconst : (9 / (4 * (1 + R) ^ 2)) ^ 3
      = ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * ((1 + R) ^ 6)⁻¹ := by
    field_simp
    ring
  calc s ^ 3 * t ^ 3 / D ^ 6
      ≤ s ^ 3 * t ^ 3 / (ℓ * (R - 1 + s + t)) ^ 6 := hkey
    _ = (ℓ ^ 6)⁻¹ * (s * t / (R - 1 + s + t) ^ 2) ^ 3 := hsplit
    _ ≤ (ℓ ^ 6)⁻¹ * (9 / (4 * (1 + R) ^ 2)) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (ℓ ^ 6)⁻¹ * (((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * ((1 + R) ^ 6)⁻¹) := by rw [hconst]
    _ = (ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * ((1 + R) ^ 6)⁻¹ := by ring

/-- **The separation inequality.**  If `winD ℓ x > 0` and `winD ℓ y > 0` then `x` and `y` lie in the
*interior* of the `ℓ/2`-sphere, so `‖x‖ = ℓ/2 − winD ℓ x`, `‖y‖ = ℓ/2 − winD ℓ y`, and the reverse
triangle inequality gives

    ‖x + ℓ•latVec m − y‖ ≥ ℓ (‖latVec m‖ − 1 + winD ℓ x/ℓ + winD ℓ y/ℓ). -/
lemma winAux_sep {ℓ : ℝ} (hℓ : 0 < ℓ) (x y : E3) (m : Fin 3 → ℤ)
    (hax : 0 < winD ℓ x) (hby : 0 < winD ℓ y) :
    ℓ * (‖latVec m‖ - 1 + winD ℓ x / ℓ + winD ℓ y / ℓ)
      ≤ ‖x + ℓ • latVec m - y‖ := by
  have hnormx : ‖x‖ = ℓ / 2 - winD ℓ x := by
    have h1 : 0 < ℓ / 2 - ‖x‖ := by
      have := (winD_pos_iff hℓ x).mp hax
      linarith
    rw [winD, max_eq_right (le_of_lt h1)]
    ring
  have hnormy : ‖y‖ = ℓ / 2 - winD ℓ y := by
    have h1 : 0 < ℓ / 2 - ‖y‖ := by
      have := (winD_pos_iff hℓ y).mp hby
      linarith
    rw [winD, max_eq_right (le_of_lt h1)]
    ring
  have hsplit : ℓ * (‖latVec m‖ - 1 + winD ℓ x / ℓ + winD ℓ y / ℓ)
      = ℓ * ‖latVec m‖ - (‖x‖ + ‖y‖) := by
    rw [hnormx, hnormy]
    field_simp
    ring
  rw [hsplit, show x + ℓ • latVec m - y = ℓ • latVec m + (x - y) from by abel]
  have hrev : ℓ * ‖latVec m‖ - ‖x - y‖ ≤ ‖ℓ • latVec m + (x - y)‖ := by
    have := norm_sub_le_norm_add (ℓ • latVec m) (x - y)
    rwa [norm_smul_of_nonneg hℓ.le] at this
  linarith [norm_sub_le x y]

/-- **The geometric assembly.**  The same inequality as `winAux_geom_core`, with the three
parameters specialised to `a = winD ℓ x`, `b = winD ℓ y` and `D = ‖x + ℓ•latVec m − y‖` — the exact
shape of the requested bound. -/
lemma winAux_core {ℓ R a b D : ℝ} (hℓ : 0 < ℓ) (hR : 1 ≤ R) (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a ≤ ℓ / 2) (hb : b ≤ ℓ / 2)
    (hD : ℓ * (R - 1 + a / ℓ + b / ℓ) ≤ D) :
    (a / ℓ) ^ 3 * (b / ℓ) ^ 3 / D ^ 6
      ≤ (ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6 * ((1 + R) ^ 6)⁻¹ :=
  winAux_geom_core (s := a / ℓ) (t := b / ℓ) hℓ hR (by positivity) (by positivity)
    (by rw [div_le_iff₀ hℓ]; linarith) (by rw [div_le_iff₀ hℓ]; linarith) hD

theorem winAux_geom {ℓ : ℝ} (hℓ : 0 < ℓ) (x y : EuclideanSpace ℝ (Fin 3)) (m : Fin 3 → ℤ) (hm : m ≠ 0) :
    (Work.BoseBoxFock.winD ℓ x / ℓ) ^ 3 * (Work.BoseBoxFock.winD ℓ y / ℓ) ^ 3
        / ‖x + ℓ • Work.BoseBoxFock.latVec m - y‖ ^ 6
      ≤ (ℓ ^ 6)⁻¹ * ((2 : ℝ) ^ 6)⁻¹ * (3 : ℝ) ^ 6
        * ((1 + ‖Work.BoseBoxFock.latVec m‖) ^ 6)⁻¹ := by
  have hR : 1 ≤ ‖latVec m‖ := norm_latVec_ge_one hm
  rcases le_or_gt (winD ℓ x) 0 with hax | hax
  · -- `winD ℓ x = 0`: the left side vanishes
    have h0 : winD ℓ x = 0 := le_antisymm hax (winD_nonneg ℓ x)
    rw [h0, zero_div, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul, zero_div]
    positivity
  · rcases le_or_gt (winD ℓ y) 0 with hby | hby
    · have h0 : winD ℓ y = 0 := le_antisymm hby (winD_nonneg ℓ y)
      rw [h0, zero_div, zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero, zero_div]
      positivity
    · exact winAux_core hℓ hR hax hby (winD_le_half hℓ x) (winD_le_half hℓ y)
        (winAux_sep hℓ x y m hax hby)

end Work.BoseBoxFock
