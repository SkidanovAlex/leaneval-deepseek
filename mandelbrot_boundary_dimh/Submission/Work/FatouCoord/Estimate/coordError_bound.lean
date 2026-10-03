import Mathlib
import Submission.Work.FatouCoord.Setup

/-!
# The defect `coordError` of the approximate Abel coordinate is `O(1/w^2)`

For a parabolic germ `f z = z + z ^ 2 * h z` with `h 0 = 1`, `h'(0) = a` the approximate
Abel coordinate in the chart `w = -1/z` is `w - c log w` with `c = 1 - a`.  Its defect
`coordError f c w = approxCoord c (wMap f w) - approxCoord c w - 1` is the obstruction to
`w - c log w` being an exact Abel coordinate, and it satisfies `coordError f (1 - a) w = O(1/w^2)`
as `Re w → +∞`.  Concretely

`‖coordError f (1 - a) w‖ ≤ B / ‖w‖ ^ 2` for `Re w > N`,

with `N` and `B ≥ 0` depending only on the quantitative data `r, A, a` of `ParabolicBounds`.
-/

namespace Work.FatouCoord.Estimate

open Work.FatouCoord
open Metric

set_option maxHeartbeats 1600000

noncomputable section

/-! ## Elementary logarithm facts -/

/-- Principal logarithm of a product of two numbers with positive real part. -/
lemma log_mul_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Complex.log (x * y) = Complex.log x + Complex.log y := by
  have hx0 : x ≠ 0 := fun h => by rw [h] at hx; simp at hx
  have hy0 : y ≠ 0 := fun h => by rw [h] at hy; simp at hy
  refine Complex.log_mul hx0 hy0 ?_
  have hxa : |x.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have hya : |y.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy)
  rw [abs_lt] at hxa hya
  have hpi : (Real.pi : ℝ) / 2 + Real.pi / 2 = Real.pi := by ring
  constructor <;> linarith [hxa.1, hxa.2, hya.1, hya.2, hpi]

/-- `1 + S ≠ 0` as soon as `‖S‖ < 1/2`. -/
lemma one_add_ne_zero_of_norm_lt_half {S : ℂ} (hS : ‖S‖ < 1 / 2) : (1 : ℂ) + S ≠ 0 := by
  intro h
  have hz : ((1 : ℂ) + S).re = 0 := by rw [h]; simp
  simp only [Complex.add_re, Complex.one_re] at hz
  have := Complex.abs_re_le_norm S
  rw [abs_le] at this
  linarith [this.1, hS]

/-- `Re (1 + S) > 0` as soon as `‖S‖ < 1/2`. -/
lemma re_one_add_pos {S : ℂ} (hS : ‖S‖ < 1 / 2) : 0 < (1 + S).re := by
  have := Complex.abs_re_le_norm S
  rw [abs_le] at this
  simp only [Complex.add_re, Complex.one_re]
  linarith [this.1, hS]

/-- For `‖S‖ < 1/2` and `Re w > 0`, the principal logarithm satisfies
`log (w * (1 + S)⁻¹) - log w = - log (1 + S)`. -/
lemma log_one_add_inv {w S : ℂ} (hw : 0 < w.re) (hS : ‖S‖ < 1 / 2) :
    Complex.log (w * (1 / (1 + S))) - Complex.log w = - Complex.log (1 + S) := by
  have h1Sne : (1 : ℂ) + S ≠ 0 := one_add_ne_zero_of_norm_lt_half hS
  have h1Sre : 0 < (1 + S).re := re_one_add_pos hS
  have hqre : 0 < (1 / (1 + S)).re := by
    rw [one_div, Complex.inv_re]
    exact div_pos h1Sre (Complex.normSq_pos.mpr h1Sne)
  have hlogmul : Complex.log (w * (1 / (1 + S))) = Complex.log w + Complex.log (1 / (1 + S)) :=
    log_mul_of_re_pos hw hqre
  have harg : (1 + S).arg ≠ Real.pi := by
    have h := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl h1Sre)
    intro hc; rw [hc] at h; linarith [Real.pi_pos]
  have hloginv : Complex.log (1 / (1 + S)) = - Complex.log (1 + S) := by
    rw [one_div]; exact Complex.log_inv (1 + S) harg
  rw [hlogmul, hloginv]; ring

/-! ## The algebraic identity for the defect -/

/-- Closed form of the defect: for `Re w` large enough that `-1/w` is in the disc of radius
`r`, the defect equals `(h u - 1 - u h u)/(1 + u h u) + (1 - a) log (1 + u h u)` with
`u = -1/w`. -/
lemma coordError_eq_form {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A')
    {w : ℂ} (hw : 0 < w.re) (hN : 1 / r < ‖w‖) (hS : ‖(-1 / w) * h (-1 / w)‖ < 1 / 2) :
    coordError f (1 - a) w =
      (h (-1 / w) - 1 - (-1 / w) * h (-1 / w)) / (1 + (-1 / w) * h (-1 / w))
        + (1 - a) * Complex.log (1 + (-1 / w) * h (-1 / w)) := by
  have hSne : (1 : ℂ) + (-1 / w) * h (-1 / w) ≠ 0 := one_add_ne_zero_of_norm_lt_half hS
  have hwsub := wMap_sub_eq hb.hr hb.f_eq hw hN hSne
  have hweq := wMap_eq hb.hr hb.f_eq hw hN
  have hlog : Complex.log (wMap f w) - Complex.log w
      = - Complex.log (1 + (-1 / w) * h (-1 / w)) := by
    rw [show wMap f w = w * (1 / (1 + (-1 / w) * h (-1 / w))) from by rw [hweq, mul_one_div]]
    exact log_one_add_inv hw hS
  rw [coordError_eq, hwsub, hlog]
  have hkey : h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) - 1
      = (h (-1 / w) - 1 - (-1 / w) * h (-1 / w)) / (1 + (-1 / w) * h (-1 / w)) := by
    rw [div_sub_one hSne]
    congr 1
    ring
  rw [hkey]
  ring

/-! ## The quantitative estimate -/

/-- Pointwise estimate: if `u` lies in the disc of radius `r` and both `‖u‖ < 1` and
`‖u h u‖ < 1/2`, then the closed form of the defect is bounded by `B ‖u‖^2`. -/
lemma norm_form_le {h : ℂ → ℂ} {a : ℂ} {r A : ℝ} (hA : 0 ≤ A)
    (hh_close : ∀ z ∈ ball 0 r, ‖h z - 1 - a * z‖ ≤ A * ‖z‖ ^ 2)
    (hh_bound : ∀ z ∈ ball 0 r, ‖h z‖ ≤ 2)
    {u : ℂ} (hu_ball : u ∈ ball 0 r) (hu_lt1 : ‖u‖ < 1) (hShalf : ‖u * h u‖ < 1 / 2) :
    ‖(h u - 1 - u * h u) / (1 + u * h u) + (1 - a) * Complex.log (1 + u * h u)‖
      ≤ (2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖)) * ‖u‖ ^ 2 := by
  set S : ℂ := u * h u with hSdef
  have hu1 : ‖u‖ ≤ 1 := le_of_lt hu_lt1
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have hShalf' : ‖S‖ < 1 / 2 := by rw [hSdef]; exact hShalf
  have hSne : (1 : ℂ) + S ≠ 0 := one_add_ne_zero_of_norm_lt_half hShalf'
  have he := hh_close u hu_ball
  have hh2 := hh_bound u hu_ball
  have hS2 : ‖S‖ ≤ 2 * ‖u‖ := by
    rw [hSdef, norm_mul]; nlinarith [hh2, norm_nonneg u]
  have hpow : ‖u‖ ^ 3 ≤ ‖u‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (le_of_lt hu_lt1) (sq_nonneg ‖u‖)
    rw [mul_one] at h; nlinarith [h]
  -- logarithm defect
  have hlogS : ‖Complex.log (1 + S) - S‖ ≤ 4 * ‖u‖ ^ 2 := by
    have h := Complex.norm_log_one_add_sub_self_le (z := S) (by linarith)
    have hq : (1 - ‖S‖)⁻¹ / 2 ≤ 1 := by
      have h1 : (1 - ‖S‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      linarith
    have hq0 : 0 ≤ (1 - ‖S‖)⁻¹ / 2 := by
      apply div_nonneg; apply inv_nonneg.mpr; linarith; norm_num
    have hSsq : ‖S‖ ^ 2 ≤ 4 * ‖u‖ ^ 2 := by nlinarith [hS2, hu0, norm_nonneg S]
    nlinarith [h, hq, hq0, hSsq, hu0, sq_nonneg ‖S‖]
  have hSu : ‖S - u‖ ≤ (A + ‖a‖) * ‖u‖ ^ 2 := by
    have hh1 : ‖h u - 1‖ ≤ A * ‖u‖ ^ 2 + ‖a‖ * ‖u‖ := by
      calc ‖h u - 1‖ = ‖(h u - 1 - a * u) + a * u‖ := by congr 1; ring
        _ ≤ ‖h u - 1 - a * u‖ + ‖a * u‖ := norm_add_le _ _
        _ = ‖h u - 1 - a * u‖ + ‖a‖ * ‖u‖ := by rw [norm_mul]
        _ ≤ A * ‖u‖ ^ 2 + ‖a‖ * ‖u‖ := by linarith [he]
    rw [hSdef, show u * h u - u = u * (h u - 1) by ring, norm_mul]
    calc ‖u‖ * ‖h u - 1‖ ≤ ‖u‖ * (A * ‖u‖ ^ 2 + ‖a‖ * ‖u‖) :=
          mul_le_mul_of_nonneg_left hh1 hu0
      _ ≤ (A + ‖a‖) * ‖u‖ ^ 2 := by nlinarith [hpow, hu0, hA]
  have hlogpart : ‖Complex.log (1 + S) - u‖ ≤ (4 + A + ‖a‖) * ‖u‖ ^ 2 := by
    calc ‖Complex.log (1 + S) - u‖ = ‖(Complex.log (1 + S) - S) + (S - u)‖ := by
            congr 1; ring
      _ ≤ ‖Complex.log (1 + S) - S‖ + ‖S - u‖ := norm_add_le _ _
      _ ≤ 4 * ‖u‖ ^ 2 + (A + ‖a‖) * ‖u‖ ^ 2 := by linarith [hlogS, hSu]
      _ = (4 + A + ‖a‖) * ‖u‖ ^ 2 := by ring
  -- the numerator `N1`
  have hN1 : ‖(h u - 1 - S) - (a - 1) * u * (1 + S)‖ ≤ (2 * A + ‖a‖ + 2 * ‖a - 1‖) * ‖u‖ ^ 2 := by
    have hsplit : (h u - 1 - S) - (a - 1) * u * (1 + S)
        = (h u - 1 - a * u) - a * u ^ 2 - u * (h u - 1 - a * u) - (a - 1) * u * S := by
      rw [hSdef]; ring
    rw [hsplit]
    have h1 : ‖(h u - 1 - a * u) - a * u ^ 2 - u * (h u - 1 - a * u) - (a - 1) * u * S‖
        ≤ ‖h u - 1 - a * u‖ + ‖a * u ^ 2‖ + ‖u * (h u - 1 - a * u)‖ + ‖(a - 1) * u * S‖ := by
      have h2 := norm_sub_le ((h u - 1 - a * u) - a * u ^ 2 - u * (h u - 1 - a * u))
        ((a - 1) * u * S)
      have h3 := norm_sub_le ((h u - 1 - a * u) - a * u ^ 2) (u * (h u - 1 - a * u))
      have h4 := norm_sub_le (h u - 1 - a * u) (a * u ^ 2)
      linarith [h2, h3, h4]
    have hA2 : ‖a * u ^ 2‖ = ‖a‖ * ‖u‖ ^ 2 := by rw [norm_mul, norm_pow]
    have hA3 : ‖u * (h u - 1 - a * u)‖ ≤ A * ‖u‖ ^ 3 := by
      rw [norm_mul]
      calc ‖u‖ * ‖h u - 1 - a * u‖ ≤ ‖u‖ * (A * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left he hu0
        _ = A * ‖u‖ ^ 3 := by ring
    have hA4 : ‖(a - 1) * u * S‖ ≤ 2 * ‖a - 1‖ * ‖u‖ ^ 2 := by
      rw [norm_mul, norm_mul]
      have hna : (0 : ℝ) ≤ ‖a - 1‖ * ‖u‖ := mul_nonneg (norm_nonneg _) hu0
      calc ‖a - 1‖ * ‖u‖ * ‖S‖ ≤ ‖a - 1‖ * ‖u‖ * (2 * ‖u‖) :=
            mul_le_mul_of_nonneg_left hS2 hna
        _ = 2 * ‖a - 1‖ * ‖u‖ ^ 2 := by ring
    have hA5 : A * ‖u‖ ^ 3 ≤ A * ‖u‖ ^ 2 := by nlinarith [hA, hpow]
    calc ‖(h u - 1 - a * u) - a * u ^ 2 - u * (h u - 1 - a * u) - (a - 1) * u * S‖
        ≤ ‖h u - 1 - a * u‖ + ‖a * u ^ 2‖ + ‖u * (h u - 1 - a * u)‖ + ‖(a - 1) * u * S‖ := h1
      _ = ‖h u - 1 - a * u‖ + ‖a‖ * ‖u‖ ^ 2 + ‖u * (h u - 1 - a * u)‖
            + ‖(a - 1) * u * S‖ := by rw [hA2]
      _ ≤ A * ‖u‖ ^ 2 + ‖a‖ * ‖u‖ ^ 2 + A * ‖u‖ ^ 3 + 2 * ‖a - 1‖ * ‖u‖ ^ 2 := by
            linarith [he, hA3, hA4]
      _ ≤ A * ‖u‖ ^ 2 + ‖a‖ * ‖u‖ ^ 2 + A * ‖u‖ ^ 2 + 2 * ‖a - 1‖ * ‖u‖ ^ 2 := by
            linarith [hA5]
      _ = (2 * A + ‖a‖ + 2 * ‖a - 1‖) * ‖u‖ ^ 2 := by ring
  -- norm of the inverse factor
  have h1S_ge : 1 - ‖S‖ ≤ ‖1 + S‖ := by
    have h := norm_sub_le ((1 : ℂ) + S) S
    rw [add_sub_cancel_right, norm_one] at h
    linarith
  have h1S_pos : 0 < ‖1 + S‖ := by linarith [hShalf']
  have hq : ‖(1 + S)⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_le_comm₀ h1S_pos (by norm_num)]
    linarith [hShalf', h1S_ge]
  -- decompose and add up
  have hdecomp : (h u - 1 - S) / (1 + S) + (1 - a) * Complex.log (1 + S)
      = ((h u - 1 - S) - (a - 1) * u * (1 + S)) * (1 + S)⁻¹
          + (1 - a) * (Complex.log (1 + S) - u) := by
    field_simp
    ring
  rw [hdecomp]
  calc ‖((h u - 1 - S) - (a - 1) * u * (1 + S)) * (1 + S)⁻¹
          + (1 - a) * (Complex.log (1 + S) - u)‖
      ≤ ‖((h u - 1 - S) - (a - 1) * u * (1 + S)) * (1 + S)⁻¹‖
          + ‖(1 - a) * (Complex.log (1 + S) - u)‖ := norm_add_le _ _
    _ = ‖(h u - 1 - S) - (a - 1) * u * (1 + S)‖ * ‖(1 + S)⁻¹‖
          + ‖1 - a‖ * ‖Complex.log (1 + S) - u‖ := by rw [norm_mul, norm_mul]
    _ ≤ (2 * A + ‖a‖ + 2 * ‖a - 1‖) * ‖u‖ ^ 2 * 2
          + ‖1 - a‖ * ((4 + A + ‖a‖) * ‖u‖ ^ 2) := by
        have h1 := mul_le_mul hN1 hq (norm_nonneg _)
          (by nlinarith [hA, norm_nonneg a, norm_nonneg (a - 1), sq_nonneg ‖u‖])
        have h2 := mul_le_mul_of_nonneg_left hlogpart (norm_nonneg (1 - a))
        linarith [h1, h2]
    _ = (2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖)) * ‖u‖ ^ 2 := by ring

/-- **The defect of the approximate Abel coordinate is `O(1/w²)`.**  For the parabolic germ
described by `ParabolicBounds` there are constants `N > 1/r` and `B ≥ 0` such that
`‖coordError f (1 - a) w‖ ≤ B / ‖w‖ ^ 2` for every `w` with `Re w > N`. -/
theorem coordError_bound {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') :
    ∃ N B : ℝ, 0 < N ∧ 0 ≤ B ∧ 1 / r < N ∧
      ∀ w : ℂ, N < w.re → ‖coordError f (1 - a) w‖ ≤ B / ‖w‖ ^ 2 := by
  refine ⟨max (1 / r) 4 + 1,
      2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖), ?_, ?_, ?_, ?_⟩
  · linarith [le_max_right (1 / r) 4]
  · have h1 : 0 ≤ 2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) := by
      have h2 := norm_nonneg a; have h3 := norm_nonneg (a - 1); nlinarith [hb.hA]
    have h4 : 0 ≤ ‖1 - a‖ * (4 + A + ‖a‖) :=
      mul_nonneg (norm_nonneg _) (by nlinarith [hb.hA, norm_nonneg a])
    linarith
  · linarith [le_max_left (1 / r) 4]
  · intro w hw
    set M : ℝ := (max (1 / r) 4 + 1) with hMdef
    have hM4 : (4 : ℝ) < M := by rw [hMdef]; linarith [le_max_right (1 / r) 4]
    have hMpos : 0 < M := by linarith
    have hMr : 1 / r < M := by rw [hMdef]; linarith [le_max_left (1 / r) 4]
    have hwpos : 0 < w.re := lt_trans hMpos hw
    have hMnormw : M < ‖w‖ := lt_of_lt_of_le hw (Complex.re_le_norm w)
    have hrw : 1 / r < ‖w‖ := lt_trans hMr hMnormw
    have hwne : w ≠ 0 := by
      intro hh
      rw [hh] at hMnormw
      simp at hMnormw
      linarith [hMpos]
    have hwposn : 0 < ‖w‖ := norm_pos_iff.mpr hwne
    have hu_norm : ‖-1 / w‖ = (‖w‖)⁻¹ := by rw [norm_div, norm_neg, norm_one, one_div]
    have hu_ball : -1 / w ∈ ball 0 r := by
      rw [mem_ball_zero_iff, hu_norm, inv_lt_comm₀ hwposn hb.hr, inv_eq_one_div]
      exact lt_trans hMr hMnormw
    have hu_lt1 : ‖-1 / w‖ < 1 := by
      rw [hu_norm, inv_lt_comm₀ hwposn one_pos, inv_one]
      linarith [hMnormw, hM4]
    have hu_lt_invM : ‖-1 / w‖ < 1 / M := by
      rw [hu_norm, lt_div_iff₀ hMpos]
      have h1 : ‖w‖⁻¹ * M < ‖w‖⁻¹ * ‖w‖ :=
        mul_lt_mul_of_pos_left hMnormw (inv_pos.mpr hwposn)
      rw [inv_mul_cancel₀ (ne_of_gt hwposn)] at h1
      exact h1
    have hhb_u : ‖h (-1 / w)‖ ≤ 2 := hb.h_bound (-1 / w) hu_ball
    have hShalf : ‖(-1 / w) * h (-1 / w)‖ < 1 / 2 := by
      rw [norm_mul]
      calc ‖-1 / w‖ * ‖h (-1 / w)‖ ≤ ‖-1 / w‖ * 2 :=
            mul_le_mul_of_nonneg_left hhb_u (norm_nonneg _)
        _ < (1 / M) * 2 := mul_lt_mul_of_pos_right hu_lt_invM (by norm_num)
        _ = 2 / M := by ring
        _ ≤ 1 / 2 := by rw [div_le_iff₀ hMpos]; linarith [hM4]
    rw [coordError_eq_form hb hwpos hrw hShalf]
    calc ‖(h (-1 / w) - 1 - (-1 / w) * h (-1 / w)) / (1 + (-1 / w) * h (-1 / w))
            + (1 - a) * Complex.log (1 + (-1 / w) * h (-1 / w))‖
        ≤ (2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖)) * ‖-1 / w‖ ^ 2 :=
          norm_form_le hb.hA hb.h_close hb.h_bound hu_ball hu_lt1 hShalf
      _ = (2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖)) / ‖w‖ ^ 2 := by
          rw [hu_norm, inv_pow, div_eq_mul_inv]

end

end Work.FatouCoord.Estimate
