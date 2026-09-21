import Mathlib
import Submission.Work.OddCurve.LowSlope.RadSharpDefs
import Submission.Work.OddCurve.LowSlope.RadialLogDefs
import Submission.Work.OddCurve.LowSlope.RadialLogConstruction

/-!
# The sharp box and value bounds for the low-slope odd radial pair

The normalised solution `(R, r)` of the two-power radial system is built in
`Work.OddCurve.LowSlope.RadialLogConstruction` as
`R = (x u)^{1/m}`, `r = ((1-x) u)^{1/m}` with `m = 2n+2`, `u = 2 + A α` and
`x = solX n A B α` the normalised first `m`-th power.

Here we prove that the sharp control `|x - 1/2| ≤ 5σ/12` on the normalised power `x`
(of the transition-window/Glue step) upgrades the crude box `3/8 ≤ R^m, r^m ≤ 15/8` of
`RadialLogConstruction` to the *sharp* box `SharpBox n R r` in which `R, r` and their
`2n`-th and `(2n+2)`-nd powers lie in `[5/6, 6/5]`, and simultaneously gives the sharp
*value* bounds `|R - 1| ≤ 3σ/(n+1)`, `|r - 1| ≤ 3σ/(n+1)`.

The three ingredients are elementary:

* `x u` and `(1-x) u` lie in `[5/6, 6/5]` (from `|x - 1/2| ≤ 5σ/12`, `|A α| ≤ σ ≤ 1/8`);
* a number `a ∈ [5/6, 6/5]` has `a^t ∈ [5/6, 6/5]` for every `t ∈ [0,1]`, and its `m`-th
  root satisfies `|a^{1/m} - 1| ≤ 6|a-1|/(5m)` (geometric sum, each of the `m` terms is `≥ 5/6`);
* `(r/R)^{2n} = ((1-x)/x)^{n/(n+1)}` and `(R/r)^{2n} = (x/(1-x))^{n/(n+1)}`, both bounded by
  `53/43 ≤ 3/2` because `x ∈ [43/96, 53/96]`.
-/

namespace Work.OddCurve.LowSlope

set_option linter.unusedVariables false

noncomputable section

open Set Filter
open scoped Topology ContDiff

/-! ## Elementary one-dimensional bounds -/

/-- A number in `[5/6, 6/5]` raised to a power in `[0,1]` stays in `[5/6, 6/5]`. -/
lemma rpow_mem_box {a t : ℝ} (ha : a ∈ Set.Icc (5 / 6 : ℝ) (6 / 5))
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : a ^ t ∈ Set.Icc (5 / 6 : ℝ) (6 / 5) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨ht1, ht2⟩ := ht
  have ha0 : 0 < a := by linarith
  refine ⟨?_, ?_⟩
  · rcases lt_or_ge a 1 with h | h
    · have hh := Real.rpow_le_rpow_of_exponent_ge ha0 (le_of_lt h) ht2
      rw [Real.rpow_one] at hh
      linarith
    · have hh := Real.one_le_rpow h ht1
      linarith
  · rcases lt_or_ge a 1 with h | h
    · have hh := Real.rpow_le_one ha0.le (le_of_lt h) ht1
      linarith
    · have hh := Real.rpow_le_rpow_of_exponent_le h ht2
      rw [Real.rpow_one] at hh
      linarith

/-- The `m`-th root of a number in `[5/6, 6/5]` again lies in `[5/6, 6/5]`. -/
lemma rpow_inv_mem_box {a : ℝ} (ha1 : 5 / 6 ≤ a) (ha2 : a ≤ 6 / 5) {m : ℕ}
    (hm : 0 < m) : 5 / 6 ≤ a ^ ((m : ℝ)⁻¹) ∧ a ^ ((m : ℝ)⁻¹) ≤ 6 / 5 := by
  have ha0 : 0 < a := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hminv0 : 0 ≤ ((m : ℝ))⁻¹ := by positivity
  have hminv1 : ((m : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hmpos]
    exact_mod_cast hm
  constructor
  · have h1 : (5 / 6 : ℝ) ^ ((m : ℝ)⁻¹) ≤ a ^ ((m : ℝ)⁻¹) :=
      Real.rpow_le_rpow (by norm_num) ha1 hminv0
    have h2 : (5 / 6 : ℝ) ≤ (5 / 6 : ℝ) ^ ((m : ℝ)⁻¹) := by
      have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ) < 5/6) (by norm_num) hminv1
      rwa [Real.rpow_one] at h
    linarith
  · have h1 : a ^ ((m : ℝ)⁻¹) ≤ (6 / 5 : ℝ) ^ ((m : ℝ)⁻¹) :=
      Real.rpow_le_rpow (le_of_lt ha0) ha2 hminv0
    have h2 : (6 / 5 : ℝ) ^ ((m : ℝ)⁻¹) ≤ 6 / 5 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 6/5) hminv1
      rwa [Real.rpow_one] at h
    linarith

/-- `c ^ e ≤ 3/2` for `0 < c ≤ 53/43` and `e ∈ [0,1]`. -/
lemma rpow_le_three_halves {c e : ℝ} (hc : 0 < c) (hc' : c ≤ 53 / 43)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) : c ^ e ≤ 3 / 2 := by
  rcases lt_or_ge c 1 with h | h
  · have hh := Real.rpow_le_one hc.le (le_of_lt h) he0
    linarith
  · have hh := Real.rpow_le_rpow_of_exponent_le h he1
    rw [Real.rpow_one] at hh
    linarith

/-- **The `m`-th root bound.**  For `a ∈ [5/6, 6/5]` and `m ≥ 1`, the geometric sum
`∑_{i<m} a^{i/m}` has all its `m` terms `≥ 5/6`, whence `|a^{1/m} - 1| ≤ 6 |a-1| / (5m)`. -/
lemma abs_rpow_inv_sub_one_le_of_half {a : ℝ} (ha : 5 / 6 ≤ a) {m : ℕ} (hm : 0 < m) :
    |a ^ ((m : ℝ)⁻¹) - 1| ≤ 6 * |a - 1| / (5 * (m : ℝ)) := by
  have ha0 : 0 < a := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hminv1 : ((m : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hmpos]; exact_mod_cast hm
  set R : ℝ := a ^ ((m : ℝ)⁻¹) with hR
  have hRnonneg : 0 ≤ R := Real.rpow_nonneg ha0.le _
  have hRm : R ^ m = a := by
    rw [hR]; exact Real.rpow_inv_natCast_pow ha0.le (by omega)
  have hS : (5 / 6 : ℝ) * (m : ℝ) ≤ ∑ i ∈ Finset.range m, R ^ i := by
    have hterm : ∀ i ∈ Finset.range m, (5 / 6 : ℝ) ≤ R ^ i := by
      intro i hi
      have hi' : i ≤ m := le_of_lt (Finset.mem_range.mp hi)
      rcases lt_or_ge R 1 with h | h
      · have h2 : R ^ m ≤ R ^ i := pow_le_pow_of_le_one hRnonneg (le_of_lt h) hi'
        rw [hRm] at h2
        linarith
      · have h1 : 1 ≤ R ^ i := one_le_pow₀ h
        linarith
    calc (5 / 6 : ℝ) * (m : ℝ) = ∑ _i ∈ Finset.range m, (5 / 6 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ Finset.range m, R ^ i := Finset.sum_le_sum hterm
  have hSnn : 0 ≤ ∑ i ∈ Finset.range m, R ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg hRnonneg i)
  have hgeo := mul_geom_sum R m
  rw [hRm] at hgeo
  have hkey : |R - 1| * ((5 / 6 : ℝ) * (m : ℝ)) ≤ |a - 1| := by
    calc |R - 1| * ((5 / 6 : ℝ) * (m : ℝ))
        ≤ |R - 1| * (∑ i ∈ Finset.range m, R ^ i) :=
          mul_le_mul_of_nonneg_left hS (abs_nonneg _)
      _ = |a - 1| := by rw [← abs_of_nonneg hSnn, ← abs_mul, hgeo]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 5 * (m : ℝ))]
  nlinarith [hkey]

/-! ## Bounds for the products `x u` and `(1-x) u` -/

/-- If `|x - 1/2| ≤ 5σ/12` and `|A α| ≤ σ ≤ 1/8`, then `x (2 + A α) ∈ [5/6, 6/5]` and
`|x (2 + A α) - 1| ≤ 133 σ / 96`. -/
lemma mul_solU_bounds {A : ℝ → ℝ} {σ x α : ℝ} (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8)
    (hx : |x - 1 / 2| ≤ 5 * σ / 12) (hAα : |A α| ≤ σ) :
    0 < x ∧ 0 < solU A α ∧ 5 / 6 ≤ x * solU A α ∧ x * solU A α ≤ 6 / 5 ∧
      |x * solU A α - 1| ≤ 133 * σ / 96 := by
  obtain ⟨hA1, hA2⟩ := abs_le.mp hAα
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  have hxlo : 1 / 2 - 5 * σ / 12 ≤ x := by linarith
  have hxhi : x ≤ 1 / 2 + 5 * σ / 12 := by linarith
  have hulo : 2 - σ ≤ solU A α := by rw [solU_apply]; linarith
  have huhi : solU A α ≤ 2 + σ := by rw [solU_apply]; linarith
  have hxpos : 0 < x := by
    have : (0 : ℝ) < 1 / 2 - 5 * σ / 12 := by nlinarith [hσ8]
    linarith
  have hupos : 0 < solU A α := by linarith
  refine ⟨hxpos, hupos, ?_, ?_, ?_⟩
  · have h := mul_le_mul hxlo hulo (by linarith) (le_of_lt hxpos)
    nlinarith [h, hσ, hσ8]
  · have h := mul_le_mul hxhi huhi (le_of_lt hupos) (by linarith)
    nlinarith [h, hσ, hσ8]
  · have heq : x * solU A α - 1 = (x - 1 / 2) * solU A α + A α / 2 := by
      rw [solU_apply]; ring
    rw [heq]
    have h1 : |(x - 1 / 2) * solU A α + A α / 2| ≤ |x - 1 / 2| * solU A α + |A α| / 2 := by
      have h := abs_add_le ((x - 1 / 2) * solU A α) (A α / 2)
      rw [abs_mul, abs_of_pos hupos, abs_div, abs_two] at h
      exact h
    have h2 : |x - 1 / 2| * solU A α ≤ (5 * σ / 12) * (2 + σ) :=
      mul_le_mul hx huhi (le_of_lt hupos) (by positivity)
    have h3 : |A α| / 2 ≤ σ / 2 := by linarith
    nlinarith [h1, h2, h3, hσ, hσ8]

/-! ## The sharp value bound and box for a single radial function

Both `solR` and `solr` have the form `(y u)^{1/m}` with `y` the normalised `m`-th power and
`u = solU A α`: `y = solX n A B α` for `R` and `y = 1 - solX n A B α` for `r`.  Since `hX`
bounds `|solX - 1/2|`, the same estimate applies to both `y`. -/

/-- The sharp value bound for a quantity `(y u)^{1/m}` with `|y - 1/2| ≤ 5σ/12`. -/
lemma rpow_inv_sharp_value {A : ℝ → ℝ} {σ y α : ℝ} {m : ℕ} (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8)
    (hy : |y - 1 / 2| ≤ 5 * σ / 12) (hAα : |A α| ≤ σ) (hm : 0 < m) :
    |(y * solU A α) ^ ((m : ℝ)⁻¹) - 1| ≤ 6 * (133 * σ / 96) / (5 * (m : ℝ)) := by
  obtain ⟨hypos, hupos, hb1, hb2, hb3⟩ := mul_solU_bounds hσ hσ8 hy hAα
  have hmain := abs_rpow_inv_sub_one_le_of_half hb1 hm
  calc |(y * solU A α) ^ ((m : ℝ)⁻¹) - 1|
      ≤ 6 * |y * solU A α - 1| / (5 * (m : ℝ)) := hmain
    _ ≤ 6 * (133 * σ / 96) / (5 * (m : ℝ)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith

/-- The two `2n`-th power identities: `R^{2n} = (x u)^{n/(n+1)}` (and the version for `r`). -/
lemma solR_pow_two_mul (n : ℕ) {A B : ℝ → ℝ} {α : ℝ}
    (hx : 0 < solX n A B α) (hu : 0 < solU A α) :
    (solR n A B α) ^ (2 * n) = (solX n A B α * solU A α) ^ ((n : ℝ) / ((n : ℝ) + 1)) := by
  rw [solR_apply, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (mul_pos hx hu))]
  congr 1
  push_cast
  field_simp
  try ring

lemma solr_pow_two_mul (n : ℕ) {A B : ℝ → ℝ} {α : ℝ}
    (hx : 0 < 1 - solX n A B α) (hu : 0 < solU A α) :
    (solr n A B α) ^ (2 * n) = ((1 - solX n A B α) * solU A α) ^ ((n : ℝ) / ((n : ℝ) + 1)) := by
  rw [solr_apply, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (mul_pos hx hu))]
  congr 1
  push_cast
  field_simp
  try ring

/-! ## The sharp value bounds -/

lemma solR_sub_one_sharp (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hX : |solX n A B α - 1 / 2| ≤ 5 * σ / 12)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |solR n A B α - 1| ≤ 3 * σ / ((n : ℝ) + 1) := by
  rw [solR_apply]
  have hm : 0 < 2 * n + 2 := by omega
  refine le_trans (rpow_inv_sharp_value hσ hσ8 hX (hA α hα) hm) ?_
  have hacast : (((2 * n + 2 : ℕ)) : ℝ) = 2 * (n : ℝ) + 2 := by push_cast; ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 5 * (((2 * n + 2 : ℕ)) : ℝ)),
    div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  rw [hacast]
  nlinarith [hσ]

lemma solr_sub_one_sharp (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hX : |solX n A B α - 1 / 2| ≤ 5 * σ / 12)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |solr n A B α - 1| ≤ 3 * σ / ((n : ℝ) + 1) := by
  have hX' : |(1 - solX n A B α) - 1 / 2| ≤ 5 * σ / 12 := by
    have h := hX
    rw [abs_sub_comm] at h
    convert h using 2
    ring
  rw [solr_apply]
  have hm : 0 < 2 * n + 2 := by omega
  refine le_trans (rpow_inv_sharp_value hσ hσ8 hX' (hA α hα) hm) ?_
  have hacast : (((2 * n + 2 : ℕ)) : ℝ) = 2 * (n : ℝ) + 2 := by push_cast; ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 5 * (((2 * n + 2 : ℕ)) : ℝ)),
    div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  rw [hacast]
  nlinarith [hσ]

/-! ## The sharp box -/

lemma solR_box_sharp (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hX : |solX n A B α - 1 / 2| ≤ 5 * σ / 12)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    5 / 6 ≤ solR n A B α ∧ solR n A B α ≤ 6 / 5 ∧
      5 / 6 ≤ (solR n A B α) ^ (2 * n) ∧ (solR n A B α) ^ (2 * n) ≤ 6 / 5 ∧
      5 / 6 ≤ (solR n A B α) ^ (2 * n + 2) ∧ (solR n A B α) ^ (2 * n + 2) ≤ 6 / 5 := by
  obtain ⟨hxpos, hupos, hb1, hb2, hb3⟩ := mul_solU_bounds (A := A) hσ hσ8 hX (hA α hα)
  have hm : 0 < 2 * n + 2 := by omega
  have htp0 : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have htp1 : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hroot := rpow_inv_mem_box hb1 hb2 hm
  have hp := rpow_mem_box (show (solX n A B α * solU A α) ∈ Set.Icc (5 / 6 : ℝ) (6 / 5) from
    ⟨hb1, hb2⟩) ⟨htp0, htp1⟩
  have hpow := solR_pow_m n (le_of_lt hxpos) (le_of_lt hupos)
  have hpow2 := solR_pow_two_mul n hxpos hupos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [solR_apply]; exact hroot.1
  · rw [solR_apply]; exact hroot.2
  · rw [hpow2]; exact hp.1
  · rw [hpow2]; exact hp.2
  · rw [hpow]; exact hb1
  · rw [hpow]; exact hb2

lemma solr_box_sharp (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hX : |solX n A B α - 1 / 2| ≤ 5 * σ / 12)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    5 / 6 ≤ solr n A B α ∧ solr n A B α ≤ 6 / 5 ∧
      5 / 6 ≤ (solr n A B α) ^ (2 * n) ∧ (solr n A B α) ^ (2 * n) ≤ 6 / 5 ∧
      5 / 6 ≤ (solr n A B α) ^ (2 * n + 2) ∧ (solr n A B α) ^ (2 * n + 2) ≤ 6 / 5 := by
  have hX' : |(1 - solX n A B α) - 1 / 2| ≤ 5 * σ / 12 := by
    have h := hX
    rw [abs_sub_comm] at h
    convert h using 2
    ring
  obtain ⟨h1mxpos, hupos, hb1, hb2, hb3⟩ :=
    mul_solU_bounds (A := A) (x := 1 - solX n A B α) hσ hσ8 hX' (hA α hα)
  have hm : 0 < 2 * n + 2 := by omega
  have htp0 : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have htp1 : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hroot := rpow_inv_mem_box hb1 hb2 hm
  have hp := rpow_mem_box
    (show ((1 - solX n A B α) * solU A α) ∈ Set.Icc (5 / 6 : ℝ) (6 / 5) from ⟨hb1, hb2⟩)
    ⟨htp0, htp1⟩
  have hpow := solr_pow_m n (le_of_lt h1mxpos) (le_of_lt hupos)
  have hpow2 := solr_pow_two_mul n h1mxpos hupos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [solr_apply]; exact hroot.1
  · rw [solr_apply]; exact hroot.2
  · rw [hpow2]; exact hp.1
  · rw [hpow2]; exact hp.2
  · rw [hpow]; exact hb1
  · rw [hpow]; exact hb2

/-! ## The ratio bounds -/

lemma sol_ratio_sharp (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hX : |solX n A B α - 1 / 2| ≤ 5 * σ / 12)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (solr n A B α / solR n A B α) ^ (2 * n) ≤ 3 / 2 ∧
      (solR n A B α / solr n A B α) ^ (2 * n) ≤ 3 / 2 := by
  obtain ⟨hxpos, hupos, hb1, hb2, hb3⟩ := mul_solU_bounds (A := A) hσ hσ8 hX (hA α hα)
  have hx43 : 43 / 96 ≤ solX n A B α := by
    have := (abs_le.mp hX).1
    nlinarith [this, hσ8]
  have hx53 : solX n A B α ≤ 53 / 96 := by
    have := (abs_le.mp hX).2
    nlinarith [this, hσ8]
  have h1mxpos : 0 < 1 - solX n A B α := by linarith
  have hxu : 0 ≤ solX n A B α * solU A α := le_of_lt (mul_pos hxpos hupos)
  have h1xu : 0 ≤ (1 - solX n A B α) * solU A α := le_of_lt (mul_pos h1mxpos hupos)
  have hcpos : 0 < (1 - solX n A B α) / solX n A B α := div_pos h1mxpos hxpos
  have hc2pos : 0 < solX n A B α / (1 - solX n A B α) := div_pos hxpos h1mxpos
  have he0 : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have he1 : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hexp : (((2 * n + 2 : ℕ)) : ℝ)⁻¹ * (((2 * n : ℕ)) : ℝ) = (n : ℝ) / ((n : ℝ) + 1) := by
    push_cast; field_simp; try ring
  constructor
  · have hbase : (1 - solX n A B α) * solU A α / (solX n A B α * solU A α)
        = (1 - solX n A B α) / solX n A B α := by
      field_simp; try ring
    have hId : solr n A B α / solR n A B α
        = (((1 - solX n A B α) * solU A α) / (solX n A B α * solU A α))
            ^ (((2 * n + 2 : ℕ)) : ℝ)⁻¹ := by
      rw [solr_apply, solR_apply, ← Real.div_rpow h1xu hxu]
    rw [hId, hbase, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hcpos), hexp]
    refine rpow_le_three_halves hcpos ?_ he0 he1
    rw [div_le_iff₀ hxpos]
    nlinarith [hx43, hx53]
  · have hbase : solX n A B α * solU A α / ((1 - solX n A B α) * solU A α)
        = solX n A B α / (1 - solX n A B α) := by
      field_simp; try ring
    have hId : solR n A B α / solr n A B α
        = ((solX n A B α * solU A α) / ((1 - solX n A B α) * solU A α))
            ^ (((2 * n + 2 : ℕ)) : ℝ)⁻¹ := by
      rw [solr_apply, solR_apply, ← Real.div_rpow hxu h1xu]
    rw [hId, hbase, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hc2pos), hexp]
    refine rpow_le_three_halves hc2pos ?_ he0 he1
    rw [div_le_iff₀ h1mxpos]
    nlinarith [hx43, hx53]

/-! ## The main statement -/

theorem sol_box_value_sharp (n : ℕ) (hn : 1 ≤ n) {A B : ℝ → ℝ} {σ α : ℝ}
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8)
    (hA : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |A β| ≤ σ)
    (hB : ∀ β ∈ Set.Icc (0 : ℝ) (Real.pi / 2), |B β| ≤ σ)
    (hX : |solX n A B α - 1 / 2| ≤ 5 * σ / 12)
    (hα : α ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    SharpBox n (solR n A B α) (solr n A B α) ∧
      |solR n A B α - 1| ≤ 3 * σ / ((n : ℝ) + 1) ∧
      |solr n A B α - 1| ≤ 3 * σ / ((n : ℝ) + 1) := by
  obtain ⟨hR1, hR2, hR3, hR4, hR5, hR6⟩ := solR_box_sharp n hn hσ hσ8 hA hX hα
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6⟩ := solr_box_sharp n hn hσ hσ8 hA hX hα
  obtain ⟨hRr, hrR⟩ := sol_ratio_sharp n hn hσ hσ8 hA hX hα
  exact ⟨⟨hR1, hR2, hR3, hR4, hR5, hR6, hr1, hr2, hr3, hr4, hr5, hr6, hRr, hrR,
      by linarith⟩,
    solR_sub_one_sharp n hn hσ hσ8 hA hX hα, solr_sub_one_sharp n hn hσ hσ8 hA hX hα⟩

end

end Work.OddCurve.LowSlope
