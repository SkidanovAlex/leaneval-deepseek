import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.discretise
import Submission.Work.BMF.wgun_block_sum
import Submission.Work.BMF.wgun_integral_block2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N12 `corollary_of_uniform`: from `Y^{θ₁} ≤ H ≤ Y^{1−θ₁}` to `H = X^θ`, `0 < θ < 1`

Subdivision argument: for `θ < 1/2` apply the hypothesis directly with `θ₁ = θ`. For
`θ ≥ 1/2` split `[x, x+X^θ]` into blocks of length `H' = X^{1/4}`; the resulting block bound
`F_H(x) ≤ (H'/H) Σ_j F_{H'}(x + jH') + (m + H' + 2)/H` is integrated over `x ∈ [X, 2X]` and the
hypothesis is applied at `Y = X` and `Y = 2X` with `θ₁ = 1/5`.
-/

namespace Work.BMF

open Polynomial Filter BoundedMultiplicativeFunctions
open MeasureTheory Real Complex
open scoped Topology

/-! ### Elementary asymptotics -/

/-- `X ^ a ≤ c * X` eventually, for `a < 1` and `c > 0`. -/
lemma eventually_rpow_le_mul_self {a c : ℝ} (ha : a < 1) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, X ^ a ≤ c * X := by
  have hmem : Set.Iio c ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds (by simpa using hc)
  have h0 : ∀ᶠ X : ℝ in atTop, X ^ (a - 1) < c := by
    have h := (_root_.tendsto_rpow_neg_atTop (show 0 < 1 - a by linarith)).eventually hmem
    filter_upwards [h] with X hX
    rwa [show -(1 - a) = a - 1 by ring] at hX
  filter_upwards [h0, eventually_gt_atTop (0 : ℝ)] with X hX hX0
  have h1 : X ^ a = X * X ^ (a - 1) := by
    have h := Real.rpow_add hX0 (1 : ℝ) (a - 1)
    rw [Real.rpow_one] at h
    rw [show (1 : ℝ) + (a - 1) = a by ring] at h
    exact h
  rw [h1]
  calc X * X ^ (a - 1) ≤ X * c := mul_le_mul_of_nonneg_left (le_of_lt hX) (le_of_lt hX0)
    _ = c * X := by ring

/-! ### Integrability of the norm on compact intervals -/

/-- The `u^{k+1}`-norm is bounded by `(H+1)/H`. -/
lemma weakGowers_le_div (k : ℕ) (H : ℝ) (hH : 0 < H) (g : ℤ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (x : ℝ) : weakGowersUniformityNorm k x H g ≤ (H + 1) / H := by
  have hcard : ((Finset.Icc ⌈x⌉ ⌊x + H⌋).card : ℝ) ≤ H + 1 := by
    rw [Int.card_Icc]
    have h3 : ((⌊x + H⌋ + 1 - ⌈x⌉ : ℤ) : ℝ) ≤ H + 1 := by
      push_cast
      linarith [Int.floor_le (x + H), Int.le_ceil x]
    have h5 : (⌊x + H⌋ + 1 - ⌈x⌉ : ℤ) ≤ ((⌊H⌋₊ : ℤ) + 1) := by
      have h6 : (⌊x + H⌋ + 1 - ⌈x⌉ : ℤ) ≤ ⌊H⌋ + 1 := by
        have h7 := (Int.le_floor).mpr h3
        rwa [Int.floor_add_one] at h7
      rwa [← Int.natCast_floor_eq_floor (le_of_lt hH)] at h6
    have h8 := Int.toNat_le.mpr h5
    have h10 : ((⌊H⌋₊ + 1 : ℕ) : ℝ) ≤ H + 1 := by
      have := Nat.floor_le (le_of_lt hH)
      push_cast
      linarith
    exact le_trans (by exact_mod_cast h8) h10
  rw [weakGowersUniformityNorm]
  refine iSup_Poly_le (by positivity) (fun P _ => ?_)
  have h1 := norm_sum_cexp_le_card g hg P ⌈x⌉ ⌊x + H⌋
  calc 1 / H * ‖∑ n ∈ Finset.Icc ⌈x⌉ ⌊x + H⌋, g n * cexp (2 * π * I * -P.eval (n : ℝ))‖
      ≤ 1 / H * ((Finset.Icc ⌈x⌉ ⌊x + H⌋).card : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (H + 1) / H := by
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right hH]
        exact hcard

lemma intervalIntegrable_wgu (k : ℕ) (H : ℝ) (hH : 1 ≤ H) (g : ℤ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (a b : ℝ) : IntervalIntegrable (fun x : ℝ => weakGowersUniformityNorm k x H g) volume a b := by
  have hH0 : 0 < H := lt_of_lt_of_le one_pos hH
  refine IntegrableOn.intervalIntegrable ?_
  refine IntegrableOn.of_bound ?_ ?_ 3 ?_
  · rw [Set.uIcc, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  · exact (measurable_weakGowers k H g).aestronglyMeasurable.restrict
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (weakGowers_nonneg k H hH0 g hg x)]
    exact weakGowers_le_three k H hH g hg x

/-! ### The case `1/2 ≤ θ < 1` -/

/-- For `1/2 ≤ θ < 1` the integral over `[X, 2X]` at length `X^θ` is `o(X)`, given the uniform
hypothesis at scale `θ₁ = 1/5`. -/
lemma integral_le_of_ge_half (k : ℕ) (g : ℤ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (hU5 : ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y H : ℝ, Y₀ ≤ Y → Y ^ (1 / 5 : ℝ) ≤ H →
      H ≤ Y ^ (4 / 5 : ℝ) →
      ∫ x in Y..(2 * Y), weakGowersUniformityNorm k x H g < η * Y)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ12 : 1 / 2 ≤ θ) (hθ1 : θ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop,
      ‖∫ x in X..(2 * X), weakGowersUniformityNorm k x (X ^ θ) g‖ ≤ ε * ‖X‖ := by
  obtain ⟨Y0, hY0⟩ := hU5 (ε / 64) (by positivity)
  filter_upwards [eventually_ge_atTop (max (max Y0 1) 16),
    eventually_rpow_le_mul_self (show (3 : ℝ) / 4 < 1 by norm_num)
      (show (0 : ℝ) < ε / 64 by positivity),
    eventually_rpow_le_mul_self (show (1 : ℝ) / 2 < 1 by norm_num)
      (show (0 : ℝ) < ε / 64 by positivity)]
    with X hX hpow34 hpow12
  set H : ℝ := X ^ θ with hHdef
  set H' : ℝ := X ^ (1 / 4 : ℝ) with hH'def
  set m : ℕ := ⌊H / H'⌋₊ + 1 with hmdef
  have hX1 : 1 ≤ X := le_trans (le_trans (le_max_right Y0 1) (le_max_left (max Y0 1) 16)) hX
  have hX16 : 16 ≤ X := le_trans (le_max_right (max Y0 1) 16) hX
  have hXY0 : Y0 ≤ X := le_trans (le_trans (le_max_left Y0 1) (le_max_left (max Y0 1) 16)) hX
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  have hH0 : 0 < H := by rw [hHdef]; exact Real.rpow_pos_of_pos hX0 θ
  have hH'0 : 0 < H' := by rw [hH'def]; exact Real.rpow_pos_of_pos hX0 _
  have hH'1 : 1 ≤ H' := by rw [hH'def]; exact Real.one_le_rpow hX1 (by norm_num)
  have hH1 : 1 ≤ H := by rw [hHdef]; exact Real.one_le_rpow hX1 (le_of_lt hθ₀)
  have hH'leH : H' ≤ H := by
    rw [hHdef, hH'def]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hHleX : H ≤ X := by
    rw [hHdef]
    have h := Real.rpow_le_rpow_of_exponent_le (x := X) hX1 (le_of_lt hθ1)
    rwa [Real.rpow_one] at h
  -- the number of blocks `m`
  have hmval : (m : ℝ) = (⌊H / H'⌋₊ : ℝ) + 1 := by rw [hmdef]; push_cast; ring
  have hm₁ : H < (m : ℝ) * H' := by
    have hlt : H / H' < (⌊H / H'⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hmul := mul_lt_mul_of_pos_right hlt hH'0
    rw [div_mul_cancel₀ H (ne_of_gt hH'0)] at hmul
    rwa [hmval]
  have hm₂ : (m : ℝ) * H' ≤ H + H' := by
    have hfl : (⌊H / H'⌋₊ : ℝ) ≤ H / H' :=
      Nat.floor_le (div_nonneg (le_of_lt hH0) (le_of_lt hH'0))
    have h2 : (⌊H / H'⌋₊ : ℝ) * H' ≤ H := by
      have := mul_le_mul_of_nonneg_right hfl (le_of_lt hH'0)
      rwa [div_mul_cancel₀ H (ne_of_gt hH'0)] at this
    rw [hmval, add_mul, one_mul]
    linarith
  -- measurability and boundedness
  have hmeasH : Measurable (fun x : ℝ => weakGowersUniformityNorm k x H g) :=
    measurable_weakGowers k H g
  have hmeasH' : Measurable (fun x : ℝ => weakGowersUniformityNorm k x H' g) :=
    measurable_weakGowers k H' g
  have hbddH : ∀ x : ℝ, weakGowersUniformityNorm k x H g ≤ (H + 1) / H :=
    fun x => weakGowers_le_div k H hH0 g hg x
  have hbddH' : ∀ x : ℝ, weakGowersUniformityNorm k x H' g ≤ (H' + 1) / H' :=
    fun x => weakGowers_le_div k H' hH'0 g hg x
  have hpt : ∀ x : ℝ, weakGowersUniformityNorm k x H g ≤
      (H' / H) * ∑ j ∈ Finset.range m, weakGowersUniformityNorm k (x + (j : ℝ) * H') H' g
      + ((m : ℝ) + H' + 2) / H := fun x => wgun_block_sum k g hg x H H' hH0 hH'0 m hm₁ hm₂
  -- scale conditions
  have hscale1a : X ^ (1 / 5 : ℝ) ≤ H' := by
    rw [hH'def]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hscale1b : H' ≤ X ^ (4 / 5 : ℝ) := by
    rw [hH'def]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hscale2a : (2 * X) ^ (1 / 5 : ℝ) ≤ H' := by
    rw [hH'def, Real.mul_rpow (by norm_num) (le_of_lt hX0)]
    have h2 : (2 : ℝ) ^ (1 / 5 : ℝ) ≤ X ^ (1 / 20 : ℝ) := by
      have hb : ((2 : ℝ) ^ (4 : ℝ)) ^ (1 / 20 : ℝ) ≤ X ^ (1 / 20 : ℝ) :=
        Real.rpow_le_rpow (by positivity)
          (by rw [show (2 : ℝ) ^ (4 : ℝ) = 16 by norm_num]; exact hX16) (by norm_num)
      rwa [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        show (4 : ℝ) * (1 / 20) = 1 / 5 by norm_num] at hb
    calc (2 : ℝ) ^ (1 / 5 : ℝ) * X ^ (1 / 5 : ℝ)
        ≤ X ^ (1 / 20 : ℝ) * X ^ (1 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt hX0) _)
      _ = X ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_add hX0]
          congr 1
          norm_num
  have hscale2b : H' ≤ (2 * X) ^ (4 / 5 : ℝ) := by
    rw [hH'def]
    calc X ^ (1 / 4 : ℝ) ≤ X ^ (4 / 5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
      _ ≤ (2 * X) ^ (4 / 5 : ℝ) :=
          Real.rpow_le_rpow (le_of_lt hX0) (by linarith) (by norm_num)
  -- the three integrals
  have hint1 : ∫ x in X..(2 * X), weakGowersUniformityNorm k x H' g < (ε / 64) * X :=
    hY0 X H' hXY0 hscale1a hscale1b
  have hY02X : Y0 ≤ 2 * X := by linarith
  have hint2 : ∫ x in 2 * X..(4 * X), weakGowersUniformityNorm k x H' g < (ε / 64) * (2 * X) := by
    have h := hY0 (2 * X) H' hY02X hscale2a hscale2b
    rwa [show 2 * (2 * X) = 4 * X by ring] at h
  have hint : ∫ x in X..(3 * X), weakGowersUniformityNorm k x H' g ≤ 3 * (ε / 64) * X := by
    have hI12 := intervalIntegrable_wgu k H' hH'1 g hg X (2 * X)
    have hI23 := intervalIntegrable_wgu k H' hH'1 g hg (2 * X) (3 * X)
    have hsplit : ∫ x in X..(3 * X), weakGowersUniformityNorm k x H' g
        = (∫ x in X..(2 * X), weakGowersUniformityNorm k x H' g)
          + (∫ x in 2 * X..(3 * X), weakGowersUniformityNorm k x H' g) :=
      (intervalIntegral.integral_add_adjacent_intervals hI12 hI23).symm
    have hmono : ∫ x in 2 * X..(3 * X), weakGowersUniformityNorm k x H' g
        ≤ ∫ x in 2 * X..(4 * X), weakGowersUniformityNorm k x H' g := by
      refine intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith) ?_
        (intervalIntegrable_wgu k H' hH'1 g hg (2 * X) (4 * X))
      filter_upwards with x
      exact weakGowers_nonneg k H' hH'0 g hg x
    rw [hsplit]
    have hnum : (ε / 64) * X + (ε / 64) * (2 * X) ≤ 3 * (ε / 64) * X := by
      have h : (ε / 64) * X + (ε / 64) * (2 * X) = 3 * (ε / 64) * X := by ring
      linarith [h]
    linarith [hint1, hmono, hint2, hnum]
  -- arithmetic bounds on the coefficients
  have hcoef : (m : ℝ) * H' / H ≤ 2 := by
    have h1 : (m : ℝ) * H' ≤ 2 * H := by linarith [hm₂, hH'leH]
    rw [div_le_iff₀ hH0]
    linarith
  have hA : X / H' ≤ (ε / 64) * X := by
    have heq : X / H' = X ^ (3 / 4 : ℝ) := by
      have h := Real.rpow_sub hX0 (1 : ℝ) (1 / 4)
      rw [Real.rpow_one] at h
      rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at h
      rw [hH'def]
      exact h.symm
    rw [heq]
    exact hpow34
  have hB : X / H ≤ (ε / 64) * X := by
    have heq : X / H = X ^ (1 - θ) := by
      have h := Real.rpow_sub hX0 (1 : ℝ) θ
      rw [Real.rpow_one] at h
      rw [hHdef]
      exact h.symm
    rw [heq]
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hpow12
  have hC : X * H' / H ≤ (ε / 64) * X := by
    have heq : X * H' / H = X ^ (5 / 4 - θ) := by
      have h1 : X * H' = X ^ (5 / 4 : ℝ) := by
        have h := Real.rpow_add hX0 (1 / 4 : ℝ) (1 : ℝ)
        rw [Real.rpow_one] at h
        rw [show (1 : ℝ) / 4 + 1 = 5 / 4 by norm_num] at h
        rw [hH'def, mul_comm X]
        exact h.symm
      rw [h1, hHdef]
      exact (Real.rpow_sub hX0 (5 / 4 : ℝ) θ).symm
    rw [heq]
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hpow34
  have hD : 2 * X / H ≤ 2 * ((ε / 64) * X) := by
    rw [show 2 * X / H = 2 * (X / H) by ring]
    exact mul_le_mul_of_nonneg_left hB (by norm_num)
  have hmul : X * (m : ℝ) / H ≤ 2 * ((ε / 64) * X) := by
    have hmle : (m : ℝ) / H ≤ 2 / H' := by
      rw [div_le_div_iff₀ hH0 hH'0]
      linarith [hm₂, hH'leH]
    calc X * (m : ℝ) / H = X * ((m : ℝ) / H) := by ring
      _ ≤ X * (2 / H') := mul_le_mul_of_nonneg_left hmle (le_of_lt hX0)
      _ = 2 * (X / H') := by ring
      _ ≤ 2 * ((ε / 64) * X) := mul_le_mul_of_nonneg_left hA (by norm_num)
  have herr : X * (((m : ℝ) + H' + 2) / H) ≤ 5 * (ε / 64) * X := by
    have hkey : X * (((m : ℝ) + H' + 2) / H)
        = X * (m : ℝ) / H + X * H' / H + 2 * (X / H) := by ring
    rw [hkey]
    nlinarith [hmul, hC, hD]
  -- assembly
  have hmain := wgun_integral_block2 k g X H H' m hX0 hH0 hH'0 hHleX hm₂ hmeasH hmeasH'
    hbddH hbddH' hpt
  have hI3nn : 0 ≤ ∫ x in X..(3 * X), weakGowersUniformityNorm k x H' g :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => weakGowers_nonneg k H' hH'0 g hg x)
  have hcomb : ((m : ℝ) * H' / H) * (∫ x in X..(3 * X), weakGowersUniformityNorm k x H' g)
      ≤ 2 * (3 * (ε / 64) * X) :=
    mul_le_mul hcoef hint hI3nn (by norm_num)
  have hbound : ∫ x in X..(2 * X), weakGowersUniformityNorm k x H g ≤ ε * X := by
    have hnum : 2 * (3 * (ε / 64) * X) + 5 * (ε / 64) * X ≤ ε * X := by
      have h1 : 2 * (3 * (ε / 64) * X) + 5 * (ε / 64) * X = 11 * ((ε / 64) * X) := by ring
      have h2 : ε * X = 64 * ((ε / 64) * X) := by ring
      have h3 : 0 ≤ (ε / 64) * X := mul_nonneg (by positivity) (le_of_lt hX0)
      linarith [h1, h2, h3]
    calc ∫ x in X..(2 * X), weakGowersUniformityNorm k x H g
        ≤ ((m : ℝ) * H' / H) * (∫ x in X..(3 * X), weakGowersUniformityNorm k x H' g)
            + X * (((m : ℝ) + H' + 2) / H) := hmain
      _ ≤ 2 * (3 * (ε / 64) * X) + 5 * (ε / 64) * X := add_le_add hcomb herr
      _ ≤ ε * X := hnum
  rw [Real.norm_eq_abs, abs_of_nonneg
    (intervalIntegral.integral_nonneg (by linarith) (fun x _ => weakGowers_nonneg k H hH0 g hg x)),
    Real.norm_eq_abs, abs_of_nonneg (le_of_lt hX0)]
  exact hbound

/-! ### The main theorem -/

/-- **N12. Subdivision: from the range `Y^{θ₁} ≤ H ≤ Y^{1-θ₁}` to `H = X^θ`, `0 < θ < 1`.**
For `θ < 1/2` take `θ₁ = θ`. For `θ ≥ 1/2` split `[x, x+X^θ]` into blocks of length `X^{1/4}`:
`‖g‖_{u^{k+1}[x,x+H]} ≤ (H'/H) Σ_j ‖g‖_{u^{k+1}[x+jH', x+(j+1)H']} + O(1/H' + H'/H)`, and use the
hypothesis at the scales `X` and `2X` with `θ₁ = 1/5`. -/
theorem corollary_of_uniform (k : ℕ) (g : ℤ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1)
    (hU : ∀ θ₁ : ℝ, 0 < θ₁ → θ₁ < 1 / 2 → ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y H : ℝ, Y₀ ≤ Y →
      Y ^ θ₁ ≤ H → H ≤ Y ^ (1 - θ₁) →
      ∫ x in Y..(2 * Y), weakGowersUniformityNorm k x H g < η * Y)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    (fun X ↦ ∫ x in X..(2 * X), weakGowersUniformityNorm k x (X ^ θ) g) =o[atTop]
      (fun X ↦ X) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  rcases lt_or_ge θ (1 / 2) with hlt | hge
  · obtain ⟨Y0, hY0⟩ := hU θ hθ₀ hlt ε hε
    filter_upwards [eventually_ge_atTop (max Y0 1)] with X hX
    have hX1 : 1 ≤ X := le_trans (le_max_right Y0 1) hX
    have hXY0 : Y0 ≤ X := le_trans (le_max_left Y0 1) hX
    have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
    have hH0 : 0 < X ^ θ := Real.rpow_pos_of_pos hX0 θ
    have hle : X ^ θ ≤ X ^ (1 - θ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have h := hY0 X (X ^ θ) hXY0 le_rfl hle
    have hnn : 0 ≤ ∫ x in X..(2 * X), weakGowersUniformityNorm k x (X ^ θ) g :=
      intervalIntegral.integral_nonneg (by linarith)
        (fun x _ => weakGowers_nonneg k (X ^ θ) hH0 g hg x)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hX0)]
    linarith
  · have hU5 : ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y H : ℝ, Y₀ ≤ Y → Y ^ (1 / 5 : ℝ) ≤ H →
        H ≤ Y ^ (4 / 5 : ℝ) →
        ∫ x in Y..(2 * Y), weakGowersUniformityNorm k x H g < η * Y := by
      intro η hη
      obtain ⟨Y0, hY0⟩ := hU (1 / 5) (by norm_num) (by norm_num) η hη
      refine ⟨Y0, fun Y H h1 h2 h3 => hY0 Y H h1 h2 ?_⟩
      rw [show (1 : ℝ) - 1 / 5 = 4 / 5 by norm_num]
      exact h3
    exact integral_le_of_ge_half k g hg hU5 θ hθ₀ hge hθ₁ ε hε

end Work.BMF
