import Mathlib
import Submission.Work.FatouCoord.Setup

namespace Work.FatouCoord.Estimate

open scoped Topology
open Set Filter Metric Function

open Work.FatouCoord

/-- Numerical core of the growth estimate: for small `z` the pull-back
`w ↦ -1 / f (-1/w)` differs from the translation `w + 1` by at most `1/2` in modulus.

Concretely, writing `u = -1/w`, we show

* `‖h u - 1 - u * h u‖ ≤ 1/4` (the numerator of the defect), and
* `1/2 ≤ ‖1 + u * h u‖` (a lower bound for the denominator),

which together give `‖wMap f w - w - 1‖ ≤ 1/2`. -/
private lemma local_bound {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A')
    {C ε : ℝ} (hAC : A ≤ C) (haC : ‖a‖ ≤ C) (hC2 : 2 ≤ C) (hCε : C * ε = 1 / 32)
    (hεpos : 0 < ε) {z : ℂ} (hzr : ‖z‖ < r) (hze : ‖z‖ < ε) :
    ‖h z - 1 - z * h z‖ ≤ 1 / 4 ∧ (1 / 2 : ℝ) ≤ ‖1 + z * h z‖ := by
  have hzmem : z ∈ ball 0 r := by simpa [mem_ball_zero_iff] using hzr
  have hclose := hb.h_close z hzmem
  have hbound := hb.h_bound z hzmem
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hzε : ‖z‖ ≤ ε := le_of_lt hze
  have hA0 : 0 ≤ A := hb.hA
  have ha0 : 0 ≤ ‖a‖ := norm_nonneg a
  have hnum : ‖h z - 1 - z * h z‖ ≤ 1 / 4 := by
    have hsplit : h z - 1 - z * h z = (h z - 1 - a * z) + (a * z - z * h z) := by ring
    rw [hsplit]
    have h1 : ‖h z - 1 - a * z‖ ≤ A * ‖z‖ ^ 2 := hclose
    have h4 : ‖z * h z‖ ≤ ‖z‖ * 2 := by
      rw [norm_mul]
      nlinarith
    have h2 : ‖a * z - z * h z‖ ≤ ‖a‖ * ‖z‖ + ‖z‖ * 2 := by
      calc ‖a * z - z * h z‖ ≤ ‖a * z‖ + ‖z * h z‖ := norm_sub_le _ _
        _ ≤ ‖a‖ * ‖z‖ + ‖z‖ * 2 := by rw [norm_mul]; linarith
    have hz2 : ‖z‖ ^ 2 ≤ ε ^ 2 := by nlinarith
    have hAe : A * ε ≤ 1 / 32 := by nlinarith
    have hae : ‖a‖ * ε ≤ 1 / 32 := by nlinarith
    have he64 : ε ≤ 1 / 64 := by nlinarith
    have hle1 : A * ‖z‖ ^ 2 ≤ A * ε ^ 2 := mul_le_mul_of_nonneg_left hz2 hA0
    have hle2 : ‖a‖ * ‖z‖ ≤ ‖a‖ * ε := mul_le_mul_of_nonneg_left hzε ha0
    have hle3 : ‖z‖ * 2 ≤ ε * 2 := by linarith
    have hle4 : A * ε ^ 2 ≤ 1 / 2048 := by nlinarith
    have hmain : A * ‖z‖ ^ 2 + (‖a‖ * ‖z‖ + ‖z‖ * 2) ≤ 1 / 4 := by
      nlinarith
    calc ‖(h z - 1 - a * z) + (a * z - z * h z)‖
        ≤ ‖h z - 1 - a * z‖ + ‖a * z - z * h z‖ := norm_add_le _ _
      _ ≤ A * ‖z‖ ^ 2 + (‖a‖ * ‖z‖ + ‖z‖ * 2) := by linarith
      _ ≤ 1 / 4 := hmain
  have hden : (1 / 2 : ℝ) ≤ ‖1 + z * h z‖ := by
    have habs := abs_norm_sub_norm_le (1 : ℂ) (-(z * h z))
    have he : (1 : ℂ) - -(z * h z) = 1 + z * h z := by ring
    rw [he, norm_one, norm_neg] at habs
    have hle : (1 : ℝ) - ‖z * h z‖ ≤ ‖1 + z * h z‖ := by
      have := (abs_le.mp habs).2
      linarith
    have hz2 : ‖z * h z‖ ≤ 2 * ε := by
      rw [norm_mul]
      nlinarith [norm_nonneg (h z)]
    have h2eps : 2 * ε ≤ 1 / 4 := by nlinarith
    linarith
  exact ⟨hnum, hden⟩

theorem iterate_re_growth {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') : ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧ ∀ w : ℂ, N < w.re → ∀ k : ℕ, N + k / 2 ≤ ((wMap f)^[k] w).re := by
  have hr : 0 < r := hb.hr
  have hA0 : 0 ≤ A := hb.hA
  set C : ℝ := A + ‖a‖ + 2 with hCdef
  have hC2 : 2 ≤ C := by
    rw [hCdef]
    have : 0 ≤ A + ‖a‖ := add_nonneg hA0 (norm_nonneg a)
    linarith
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC2
  have hAC : A ≤ C := by rw [hCdef]; linarith [norm_nonneg a]
  have haC : ‖a‖ ≤ C := by rw [hCdef]; linarith
  set ε : ℝ := 1 / (32 * C) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hCε : C * ε = 1 / 32 := by
    rw [hεdef]
    have hCne : C ≠ 0 := ne_of_gt hCpos
    field_simp
  set N : ℝ := max (32 * C) (1 / r + 1) with hNdef
  have hN32 : 32 * C ≤ N := le_max_left _ _
  have hNr : 1 / r < N := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity : (0:ℝ) < 32 * C) hN32
  have hNeps : 1 / N ≤ ε := by
    have h := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 32 * C) hN32
    simpa [hεdef] using h
  have hNinv_r : 1 / N < r := by
    rw [div_lt_iff₀ hNpos]
    have := (div_lt_iff₀ hr).mp hNr
    linarith
  refine ⟨N, hNpos, hNr, ?_⟩
  have hstep : ∀ v : ℂ, N < v.re → v.re + 1 / 2 ≤ (wMap f v).re := by
    intro v hv
    have hvpos : 0 < v.re := lt_of_lt_of_le hNpos hv.le
    have hv0 : v ≠ 0 := fun hc => by rw [hc] at hvpos; simp at hvpos
    have hvn : v.re ≤ ‖v‖ := Complex.re_le_norm v
    have hNv : 1 / r < ‖v‖ := lt_of_lt_of_le (lt_trans hNr hv) hvn
    have hu1 : ‖-1 / v‖ = 1 / ‖v‖ := by rw [norm_div, norm_neg, norm_one]
    have h2 : 1 / ‖v‖ ≤ 1 / v.re := one_div_le_one_div_of_le hvpos hvn
    have h3 : 1 / v.re < 1 / N := one_div_lt_one_div_of_lt hNpos hv
    have hu_eps : ‖-1 / v‖ < ε := by
      rw [hu1]; linarith
    have hu_r : ‖-1 / v‖ < r := by
      rw [hu1]; linarith
    have hlb := local_bound hb hAC haC hC2 hCε hεpos hu_r hu_eps
    have hnum := hlb.1
    have hden := hlb.2
    have hne : 1 + -1 / v * h (-1 / v) ≠ 0 := by
      intro hc
      have : ‖1 + -1 / v * h (-1 / v)‖ = 0 := by rw [hc, norm_zero]
      linarith
    have hsub := wMap_sub_eq hr hb.f_eq hvpos hNv hne
    have hkey : h (-1 / v) / (1 + -1 / v * h (-1 / v)) - 1
        = (h (-1 / v) - 1 - (-1 / v) * h (-1 / v)) / (1 + -1 / v * h (-1 / v)) := by
      rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne, one_mul]
      ring
    have hupper : ‖h (-1 / v) / (1 + -1 / v * h (-1 / v)) - 1‖ ≤ 1 / 2 := by
      rw [hkey, norm_div]
      have h4 : 0 < ‖1 + -1 / v * h (-1 / v)‖ := lt_of_lt_of_le (by norm_num) hden
      rw [div_le_iff₀ h4]
      nlinarith
    have hfin : ‖(wMap f v - v) - 1‖ ≤ 1 / 2 := by rw [hsub]; exact hupper
    have habs := Complex.abs_re_le_norm ((wMap f v - v) - 1)
    have hle := (abs_le.mp (le_trans habs hfin)).1
    simp only [Complex.sub_re, Complex.one_re] at hle
    linarith
  intro w hw k
  have hmain : ∀ k : ℕ, w.re + k / 2 ≤ ((wMap f)^[k] w).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : N < ((wMap f)^[k] w).re := by
        have hk0 : (0:ℝ) ≤ k / 2 := by positivity
        linarith
      rw [Function.iterate_succ_apply']
      have hs := hstep ((wMap f)^[k] w) hk
      push_cast
      linarith
  have := hmain k
  linarith

end Work.FatouCoord.Estimate
