import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.coordError_bound
import Submission.Work.Parab.leftCoord.wMap_large_estimates

/-!
# The defect `coordError` is `O(1/‖w‖²)` on the sectors of the left chart

The companion file `FatouCoord/Estimate/coordError_bound.lean` proves
`‖coordError f (1 - a) w‖ ≤ B / ‖w‖ ^ 2` in the *right half plane* `Re w > N`, using the
closed form

`coordError f (1 - a) w = (h u - 1 - u h u)/(1 + u h u) + (1 - a) log (1 + u h u)`,  `u = -1/w`,

where `log` is the principal branch.  The only place where `Re w > 0` enters that proof is the
logarithm identity `log (w / (1 + u h u)) - log w = - log (1 + u h u)`, which requires `w` and
`w/(1 + u h u)` to lie on the same side of the branch cut of `log`.

In this file we remove the hypothesis on `Re w`.  What matters for the principal logarithm is
only that `w` and its image `wMap f w = w / (1 + u h u)` lie *strictly on the same side* of the
real axis; then their arguments lie in `(-π, π)` with the same sign and the identity above
still holds (`log_mul_of_im_same`).  Consequently the `O(1/‖w‖²)` estimate holds on the upper
sector `Im w > 0, Im (wMap f w) > 0` and on the lower sector `Im w < 0, Im (wMap f w) < 0`, in
addition to the right half plane `Re w > 0` handled by `coordError_bound`.
-/

open scoped Topology
open Set Metric Function

set_option maxHeartbeats 1600000

namespace Work.Parab.leftCoord

open Work.FatouCoord
open Work.FatouCoord.Estimate

noncomputable section

/-! ## The branch condition for the principal logarithm -/

/-- **Multiplicativity of the principal logarithm on one side of the real axis.**  If `y` has
positive real part and `x`, `x * y` are both strictly in the upper (resp. lower) half plane,
then `log (x * y) = log x + log y`.

Indeed `arg y ∈ (-π/2, π/2)` and `arg x`, `arg (x*y)` are both in `(0, π)` (resp. `(-π, 0)`),
so `arg x + arg y - arg (x*y)`, which is an integral multiple of `2π`, lies in
`(-3π/2, 3π/2)` and hence vanishes. -/
lemma log_mul_of_im_same {x y : ℂ} (hy : 0 < y.re)
    (h : (0 < x.im ∧ 0 < (x * y).im) ∨ (x.im < 0 ∧ (x * y).im < 0)) :
    Complex.log (x * y) = Complex.log x + Complex.log y := by
  have hx0 : x ≠ 0 := by rintro rfl; rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp at h1
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  rw [Complex.log_mul_eq_add_log_iff hx0 hy0]
  have hangle := Complex.arg_mul_coe_angle hx0 hy0
  have hzero : ((x.arg + y.arg - (x * y).arg : ℝ) : Real.Angle) = 0 := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_add, hangle, sub_self]
  obtain ⟨n, hn⟩ := Real.Angle.coe_eq_zero_iff.mp hzero
  have hB := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  have hbound : |x.arg + y.arg - (x * y).arg| < 3 * Real.pi / 2 := by
    rw [abs_lt]
    rcases h with ⟨hi, hpi⟩ | ⟨hi, hpi⟩
    · have hA0 : 0 ≤ x.arg := Complex.arg_nonneg_iff.mpr hi.le
      have hC0 : 0 ≤ (x * y).arg := Complex.arg_nonneg_iff.mpr hpi.le
      constructor
      · have := Complex.arg_le_pi (x * y); linarith
      · have := Complex.arg_le_pi x; linarith
    · have hA0 : x.arg < 0 :=
        not_le.mp (mt (fun hh => Complex.arg_nonneg_iff.mp hh) (not_le.mpr hi))
      have hC0 : (x * y).arg < 0 :=
        not_le.mp (mt (fun hh => Complex.arg_nonneg_iff.mp hh) (not_le.mpr hpi))
      constructor
      · linarith [Complex.neg_pi_lt_arg x, hB.1, le_of_lt hC0]
      · linarith [Complex.neg_pi_lt_arg (x * y), hB.2, le_of_lt hA0]
  have hn0 : n = 0 := by
    have hsn : (n : ℝ) * (2 * Real.pi) = x.arg + y.arg - (x * y).arg := by
      rw [← hn, zsmul_eq_mul]
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have key : |x.arg + y.arg - (x * y).arg| = |(n : ℝ)| * (2 * Real.pi) := by
      rw [← hsn, abs_mul, abs_of_pos h2pi]
    have h1 : |(n : ℝ)| * (2 * Real.pi) < 3 * Real.pi / 2 := key ▸ hbound
    have h2 : |(n : ℝ)| < 1 := by nlinarith
    by_contra hne
    have hle : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hne
      rwa [Int.cast_abs] at this
    linarith
  have hs : x.arg + y.arg - (x * y).arg = 0 := by
    rw [← hn, hn0]; simp
  rw [Set.mem_Ioc]
  constructor <;> linarith [Complex.neg_pi_lt_arg (x * y), Complex.arg_le_pi (x * y)]

/-! ## The chart form of `wMap`, without a hypothesis on `Re w` -/

/-- `wMap f w = w / (1 + (-1/w) h (-1/w))` as soon as `1/r < ‖w‖`: the real-part hypothesis of
`Work.FatouCoord.wMap_eq` is only used to conclude `w ≠ 0`. -/
private lemma wMap_eq_general {f h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z) {w : ℂ} (hN : 1 / r < ‖w‖) :
    wMap f w = w / (1 + (-1 / w) * h (-1 / w)) := by
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hN
    have : 0 < 1 / r := one_div_pos.mpr hr
    linarith
  have hz : -1 / w ∈ ball 0 r := by
    simpa [mem_ball_zero_iff] using norm_neg_one_div_lt hr hw0 hN
  have hzw : -1 / (-1 / w) = w := by field_simp
  have h1 : f (-1 / w) = (-1 / w) * (1 + (-1 / w) * h (-1 / w)) := by
    rw [hf (-1 / w) hz]; ring
  simp only [wMap, chart]
  rw [h1, div_mul_eq_div_div, hzw]

/-- The defect form `wMap f w - w = h (-1/w) / (1 + (-1/w) h (-1/w))` under `1/r < ‖w‖`
(`Work.FatouCoord.wMap_sub_eq` with the real-part hypothesis weakened). -/
private lemma wMap_sub_eq_general {f h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z) {w : ℂ} (hN : 1 / r < ‖w‖)
    (hne : 1 + (-1 / w) * h (-1 / w) ≠ 0) :
    wMap f w - w = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hN
    have : 0 < 1 / r := one_div_pos.mpr hr
    linarith
  have key : w * ((-1 / w) * h (-1 / w)) = -h (-1 / w) := by field_simp
  have hsub : (wMap f w - w) * (1 + (-1 / w) * h (-1 / w)) = h (-1 / w) := by
    rw [wMap_eq_general hr hf hN, sub_mul, div_mul_cancel₀ _ hne]
    rw [show w - w * (1 + (-1 / w) * h (-1 / w))
        = -(w * ((-1 / w) * h (-1 / w))) by ring, key, neg_neg]
  calc wMap f w - w
      = ((wMap f w - w) * (1 + (-1 / w) * h (-1 / w))) / (1 + (-1 / w) * h (-1 / w)) :=
        (mul_div_cancel_right₀ _ hne).symm
    _ = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by rw [hsub]

/-! ## The closed form of the defect on the two sectors -/

/-- Closed form of the defect for `w` whose image `wMap f w` lies strictly on the same side of
the real axis as `w`.  This is `Work.FatouCoord.Estimate.coordError_eq_form` with the
hypothesis `0 < Re w` replaced by the branch condition
`(0 < Im w ∧ 0 < Im (wMap f w)) ∨ (Im w < 0 ∧ Im (wMap f w) < 0)`. -/
lemma coordError_eq_form_im {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') {w : ℂ} (hN : 1 / r < ‖w‖)
    (hS : ‖(-1 / w) * h (-1 / w)‖ < 1 / 2)
    (hbranch : (0 < w.im ∧ 0 < (wMap f w).im) ∨ (w.im < 0 ∧ (wMap f w).im < 0)) :
    coordError f (1 - a) w =
      (h (-1 / w) - 1 - (-1 / w) * h (-1 / w)) / (1 + (-1 / w) * h (-1 / w))
        + (1 - a) * Complex.log (1 + (-1 / w) * h (-1 / w)) := by
  have hSne : (1 : ℂ) + (-1 / w) * h (-1 / w) ≠ 0 := one_add_ne_zero_of_norm_lt_half hS
  have hre : 0 < (1 + (-1 / w) * h (-1 / w)).re := re_one_add_pos hS
  have hargS : (1 + (-1 / w) * h (-1 / w)).arg ≠ Real.pi := by
    have hlt := (abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))).2
    intro hc
    rw [hc] at hlt
    linarith [Real.pi_pos]
  have hyre : 0 < ((1 + (-1 / w) * h (-1 / w))⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos hre (Complex.normSq_pos.mpr hSne)
  have hweq : wMap f w = w * (1 + (-1 / w) * h (-1 / w))⁻¹ := by
    rw [wMap_eq_general hb.hr hb.f_eq hN, div_eq_mul_inv]
  have hmul : Complex.log (w * (1 + (-1 / w) * h (-1 / w))⁻¹)
      = Complex.log w + Complex.log ((1 + (-1 / w) * h (-1 / w))⁻¹) :=
    log_mul_of_im_same hyre (by simpa [hweq] using hbranch)
  have hinv : Complex.log ((1 + (-1 / w) * h (-1 / w))⁻¹)
      = -Complex.log (1 + (-1 / w) * h (-1 / w)) :=
    Complex.log_inv _ hargS
  have hlog : Complex.log (wMap f w) - Complex.log w
      = -Complex.log (1 + (-1 / w) * h (-1 / w)) := by
    rw [hweq, hmul, hinv]; ring
  have hwsub := wMap_sub_eq_general hb.hr hb.f_eq hN hSne
  rw [coordError_eq, hwsub, hlog]
  have hkey : h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) - 1
      = (h (-1 / w) - 1 - (-1 / w) * h (-1 / w)) / (1 + (-1 / w) * h (-1 / w)) := by
    rw [div_sub_one hSne]
    congr 1
    ring
  rw [hkey]
  ring

/-! ## Uniform set-up on the complement of a large disc -/

/-- All the elementary consequences of `max (1/r) 4 + 1 < ‖w‖` that the three sector estimates
need: `w` is far enough out that `u = -1/w` is a legitimate small parameter. -/
private lemma sector_setup {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') {w : ℂ} (hw : max (1 / r) 4 + 1 < ‖w‖) :
    1 / r < ‖w‖ ∧ (-1 / w) ∈ ball 0 r ∧ ‖-1 / w‖ < 1 ∧
      ‖(-1 / w) * h (-1 / w)‖ < 1 / 2 := by
  have hM4 : (4 : ℝ) < max (1 / r) 4 + 1 := by linarith [le_max_right (1 / r) 4]
  have hMr : 1 / r < max (1 / r) 4 + 1 := by linarith [le_max_left (1 / r) 4]
  have h4 : (4 : ℝ) ≤ ‖w‖ := le_of_lt (lt_trans hM4 hw)
  have h1r : 1 / r < ‖w‖ := lt_trans hMr hw
  have hwn : 0 < ‖w‖ := by linarith
  have hun : ‖-1 / w‖ = (‖w‖)⁻¹ := by rw [norm_div, norm_neg, norm_one, one_div]
  have hu : (-1 / w) ∈ ball 0 r := by
    rw [mem_ball_zero_iff, hun, inv_lt_comm₀ hwn hb.hr, inv_eq_one_div]
    exact h1r
  have hu1 : ‖-1 / w‖ < 1 := by
    rw [hun, inv_lt_comm₀ hwn one_pos, inv_one]
    linarith
  have hS : ‖(-1 / w) * h (-1 / w)‖ < 1 / 2 := by
    rw [norm_mul]
    have hhn : ‖h (-1 / w)‖ ≤ 2 := hb.h_bound _ hu
    have hstep : ‖-1 / w‖ * ‖h (-1 / w)‖ ≤ ‖-1 / w‖ * 2 :=
      mul_le_mul_of_nonneg_left hhn (norm_nonneg _)
    have hstep2 : ‖-1 / w‖ * 2 < 1 / 2 := by
      rw [hun]
      have hlt : (‖w‖)⁻¹ < 1 / 4 := by
        rw [inv_lt_comm₀ hwn (by norm_num : (0 : ℝ) < 1 / 4)]
        linarith
      nlinarith
    exact lt_of_le_of_lt hstep hstep2
  exact ⟨h1r, hu, hu1, hS⟩

/-! ## The sector estimate -/

theorem coordError_sector {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ R C : ℝ, 0 < R ∧ 1 / r < R ∧ 0 ≤ C ∧
      (∀ w : ℂ, R < ‖w‖ → 0 < w.re →
        ‖Work.FatouCoord.coordError f (1 - a) w‖ ≤ C / ‖w‖ ^ 2) ∧
      (∀ w : ℂ, R < ‖w‖ → 0 < w.im → 0 < (Work.FatouCoord.wMap f w).im →
        ‖Work.FatouCoord.coordError f (1 - a) w‖ ≤ C / ‖w‖ ^ 2) ∧
      (∀ w : ℂ, R < ‖w‖ → w.im < 0 → (Work.FatouCoord.wMap f w).im < 0 →
        ‖Work.FatouCoord.coordError f (1 - a) w‖ ≤ C / ‖w‖ ^ 2) := by
  refine ⟨max (1 / r) 4 + 1,
    2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : 0 < 1 / r := one_div_pos.mpr hb.hr
    have h2 : (0 : ℝ) < max (1 / r) 4 := lt_of_lt_of_le h1 (le_max_left _ _)
    linarith
  · have h2 : (1 : ℝ) / r ≤ max (1 / r) 4 := le_max_left _ _
    linarith
  · have h1 : 0 ≤ 2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) := by
      nlinarith [hb.hA, norm_nonneg a, norm_nonneg (a - 1)]
    have h4 : 0 ≤ ‖1 - a‖ * (4 + A + ‖a‖) :=
      mul_nonneg (norm_nonneg _) (by nlinarith [hb.hA, norm_nonneg a])
    linarith
  · intro w hw hwre
    obtain ⟨h1r, hu, hu1, hS⟩ := sector_setup hb hw
    have hun : ‖-1 / w‖ = (‖w‖)⁻¹ := by rw [norm_div, norm_neg, norm_one, one_div]
    rw [coordError_eq_form hb hwre h1r hS]
    calc ‖(h (-1 / w) - 1 - (-1 / w) * h (-1 / w)) / (1 + (-1 / w) * h (-1 / w))
            + (1 - a) * Complex.log (1 + (-1 / w) * h (-1 / w))‖
        ≤ (2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖)) * ‖-1 / w‖ ^ 2 :=
          norm_form_le hb.hA hb.h_close hb.h_bound hu hu1 hS
      _ = (2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖)) / ‖w‖ ^ 2 := by
          rw [hun, inv_pow, div_eq_mul_inv]
  · intro w hw hwim hwmi
    obtain ⟨h1r, hu, hu1, hS⟩ := sector_setup hb hw
    have hun : ‖-1 / w‖ = (‖w‖)⁻¹ := by rw [norm_div, norm_neg, norm_one, one_div]
    rw [coordError_eq_form_im hb h1r hS (Or.inl ⟨hwim, hwmi⟩)]
    calc ‖(h (-1 / w) - 1 - (-1 / w) * h (-1 / w)) / (1 + (-1 / w) * h (-1 / w))
            + (1 - a) * Complex.log (1 + (-1 / w) * h (-1 / w))‖
        ≤ (2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖)) * ‖-1 / w‖ ^ 2 :=
          norm_form_le hb.hA hb.h_close hb.h_bound hu hu1 hS
      _ = (2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖)) / ‖w‖ ^ 2 := by
          rw [hun, inv_pow, div_eq_mul_inv]
  · intro w hw hwim hwmi
    obtain ⟨h1r, hu, hu1, hS⟩ := sector_setup hb hw
    have hun : ‖-1 / w‖ = (‖w‖)⁻¹ := by rw [norm_div, norm_neg, norm_one, one_div]
    rw [coordError_eq_form_im hb h1r hS (Or.inr ⟨hwim, hwmi⟩)]
    calc ‖(h (-1 / w) - 1 - (-1 / w) * h (-1 / w)) / (1 + (-1 / w) * h (-1 / w))
            + (1 - a) * Complex.log (1 + (-1 / w) * h (-1 / w))‖
        ≤ (2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖)) * ‖-1 / w‖ ^ 2 :=
          norm_form_le hb.hA hb.h_close hb.h_bound hu hu1 hS
      _ = (2 * (2 * A + ‖a‖ + 2 * ‖a - 1‖) + ‖1 - a‖ * (4 + A + ‖a‖)) / ‖w‖ ^ 2 := by
          rw [hun, inv_pow, div_eq_mul_inv]

end

end Work.Parab.leftCoord
