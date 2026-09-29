import Submission.Work.TMComp.RotBasics.PSCont
import Submission.Work.TMComp.RotBasics.UpperLift

/-!
# Properties of the explicit lift `upperLift`

`upperLift r q` (defined in `UpperLift.lean`) is a positive lift of the upper triangular
matrix `!![r,q;0,1/r]` (`r > 0`): its value lies within `2` of `t`, it vanishes at `t = 0`.
-/

namespace Work.TMComp.RotBasics

open Work.TMContract
open Filter
open scoped Topology

noncomputable section

theorem vc_arg_div_pi (z : ℂ) (hz : z ≠ 0) : vc (z.arg / Real.pi) = z / (‖z‖ : ℂ) := by
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine Complex.ext ?_ ?_
  · simp only [vc, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_zero,
      mul_zero, add_zero, Complex.normSq_ofReal]
    rw [show Real.pi * (z.arg / Real.pi) = z.arg by field_simp]
    rw [Complex.cos_arg hz]
    field_simp
    ring
  · simp only [vc, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_zero,
      mul_zero, zero_mul, sub_zero, Complex.normSq_ofReal]
    rw [show Real.pi * (z.arg / Real.pi) = z.arg by field_simp]
    rw [Complex.sin_arg]
    field_simp
    ring

theorem smul_div_self {t : ℝ} (ht : t ≠ 0) (z : ℂ) : t • (z / (t : ℂ)) = z := by
  rw [show t • (z / (t : ℂ)) = (t : ℂ) * (z / (t : ℂ)) from by simp]
  rw [← mul_div_assoc, mul_comm (t : ℂ) z, mul_div_cancel_right₀ _ (by simp [ht])]

theorem smul_div_smul_self {c : ℝ} (hc : c * c = 1) {z : ℂ} {t : ℝ} (ht : t ≠ 0) :
    c • ((c • z) / (t : ℂ)) = z / (t : ℂ) := by
  rw [show c • ((c • z) / (t : ℂ)) = (c : ℂ) * ((c • z) / (t : ℂ)) from by simp]
  rw [← mul_div_assoc]
  rw [show (c : ℂ) * (c • z) = z from by
    rw [show c • z = (c : ℂ) * z from by simp]
    rw [← mul_assoc, ← Complex.ofReal_mul, hc, Complex.ofReal_one, one_mul]]

/-- `upperLift r q 0 = 0` for `r > 0` (the base point of the lift). -/
theorem upperLift_zero {r : ℝ} (hr : 0 < r) (q : ℝ) : upperLift r q 0 = 0 := by
  rw [upperLift]
  rw [show ⌊(0 : ℝ)⌋ = (0 : ℤ) by norm_num]
  have hvec : (((-1 : ℝ) ^ (0 : ℤ) : ℝ)) • (⟨r * Real.cos (Real.pi * 0) +
      q * Real.sin (Real.pi * 0), Real.sin (Real.pi * 0) / r⟩ : ℂ) = ((r : ℂ)) := by
    rw [zpow_zero, one_smul]
    refine Complex.ext ?_ ?_ <;> simp
  rw [hvec, Complex.arg_ofReal_of_nonneg (le_of_lt hr)]
  norm_num

theorem upperLift_bound (r q t : ℝ) : |upperLift r q t - t| ≤ 2 := by
  rw [upperLift]
  have hfl : |((⌊t⌋ : ℤ) : ℝ) - t| ≤ 1 := by
    have h1 : ((⌊t⌋ : ℤ) : ℝ) - t ≤ 0 := by
      have := Int.floor_le t; linarith
    have h2 : -1 ≤ ((⌊t⌋ : ℤ) : ℝ) - t := by
      have := Int.lt_floor_add_one t; linarith
    rw [abs_le]
    exact ⟨h2, by linarith⟩
  have harg : |Complex.arg (((-1 : ℝ) ^ ⌊t⌋ : ℝ) •
      (⟨r * Real.cos (Real.pi * t) + q * Real.sin (Real.pi * t),
        Real.sin (Real.pi * t) / r⟩ : ℂ))| ≤ Real.pi := by
    rw [abs_le]
    exact ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
  have hargπ : |Complex.arg (((-1 : ℝ) ^ ⌊t⌋ : ℝ) •
      (⟨r * Real.cos (Real.pi * t) + q * Real.sin (Real.pi * t),
        Real.sin (Real.pi * t) / r⟩ : ℂ)) / Real.pi| ≤ 1 := by
    rw [abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos]
    exact harg
  calc |((⌊t⌋ : ℤ) : ℝ) + Complex.arg (((-1 : ℝ) ^ ⌊t⌋ : ℝ) •
        (⟨r * Real.cos (Real.pi * t) + q * Real.sin (Real.pi * t),
          Real.sin (Real.pi * t) / r⟩ : ℂ)) / Real.pi - t|
      = |(((⌊t⌋ : ℤ) : ℝ) - t) + Complex.arg (((-1 : ℝ) ^ ⌊t⌋ : ℝ) •
        (⟨r * Real.cos (Real.pi * t) + q * Real.sin (Real.pi * t),
          Real.sin (Real.pi * t) / r⟩ : ℂ)) / Real.pi| := by ring_nf
    _ ≤ |((⌊t⌋ : ℤ) : ℝ) - t| + |Complex.arg (((-1 : ℝ) ^ ⌊t⌋ : ℝ) •
        (⟨r * Real.cos (Real.pi * t) + q * Real.sin (Real.pi * t),
          Real.sin (Real.pi * t) / r⟩ : ℂ)) / Real.pi| := abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add hfl hargπ
    _ = 2 := by norm_num

theorem upperLift_isPosLift {r q : ℝ} (hr : 0 < r) :
    IsPosLift !![r, q; 0, 1 / r] (fun t => upperLift r q t) := by
  intro t
  set c : ℝ := (-1 : ℝ) ^ ⌊t⌋ with hcdef
  set z : ℂ := ⟨r * Real.cos (Real.pi * t) + q * Real.sin (Real.pi * t),
    Real.sin (Real.pi * t) / r⟩ with hzdef
  have hrne : r ≠ 0 := ne_of_gt hr
  have hzne : z ≠ 0 := by
    intro h
    have h1 : Real.sin (Real.pi * t) / r = 0 := by
      have hh := congrArg Complex.im h
      rw [hzdef] at hh
      simpa using hh
    have h2 : r * Real.cos (Real.pi * t) + q * Real.sin (Real.pi * t) = 0 := by
      have hh := congrArg Complex.re h
      rw [hzdef] at hh
      simpa using hh
    have hs : Real.sin (Real.pi * t) = 0 := by
      rcases div_eq_zero_iff.mp h1 with h | h
      · exact h
      · exact absurd h hrne
    have hcs : Real.cos (Real.pi * t) = 0 := by
      have h3 : r * Real.cos (Real.pi * t) = 0 := by
        rw [hs, mul_zero, add_zero] at h2
        exact h2
      exact (mul_eq_zero.mp h3).resolve_left hrne
    nlinarith [Real.cos_sq_add_sin_sq (Real.pi * t)]
  have hcsq : c * c = 1 := by
    rw [hcdef]
    rcases Int.even_or_odd ⌊t⌋ with h | h
    · rw [h.neg_one_zpow]; norm_num
    · rw [h.neg_one_zpow]; norm_num
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0] at hcsq
    norm_num at hcsq
  have hsm : smul !![r, q; 0, 1 / r] (vc t) = z := by
    rw [hzdef]
    refine Complex.ext ?_ ?_ <;>
      simp [smul, vc, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        div_eq_inv_mul]
  have hup : upperLift r q t = ((⌊t⌋ : ℤ) : ℝ) + (c • z).arg / Real.pi := by
    rw [upperLift]
  have hnorm : ‖c • z‖ = ‖z‖ := by
    rw [norm_smul_real]
    have habs : |c| = 1 := by
      have h2 : |c| ^ 2 = 1 := by rw [sq_abs]; simpa [sq] using hcsq
      nlinarith [abs_nonneg c]
    rw [habs, one_mul]
  have hvc : vc (upperLift r q t) = z / (‖z‖ : ℂ) := by
    rw [hup, vc_add_int (⌊t⌋) ((c • z).arg / Real.pi),
      vc_arg_div_pi (c • z) (by rw [smul_ne_zero_iff]; exact ⟨hcne, hzne⟩), hnorm]
    exact smul_div_smul_self hcsq (ne_of_gt (norm_pos_iff.mpr hzne))
  rw [hsm, hvc, smul_div_self (ne_of_gt (norm_pos_iff.mpr hzne))]


/-- `upperLift r q m = m` at integers, for `r > 0`. -/
theorem upperLift_of_int {r : ℝ} (hr : 0 < r) (q : ℝ) (m : ℤ) :
    upperLift r q (m : ℝ) = (m : ℝ) := by
  have hcos : Real.cos (Real.pi * (m : ℝ)) = ((-1 : ℝ) ^ m : ℝ) := by
    rw [show Real.pi * (m : ℝ) = (m : ℝ) * Real.pi by ring, Real.cos_int_mul_pi]
  have hsin : Real.sin (Real.pi * (m : ℝ)) = 0 := by
    rw [show Real.pi * (m : ℝ) = (m : ℝ) * Real.pi by ring, Real.sin_int_mul_pi]
  have hcsq : ((-1 : ℝ) ^ m : ℝ) * ((-1 : ℝ) ^ m : ℝ) = 1 := by
    rcases Int.even_or_odd m with h | h
    · rw [h.neg_one_zpow]; norm_num
    · rw [h.neg_one_zpow]; norm_num
  have hz : (((-1 : ℝ) ^ m : ℝ)) •
      (⟨r * Real.cos (Real.pi * (m : ℝ)) + q * Real.sin (Real.pi * (m : ℝ)),
        Real.sin (Real.pi * (m : ℝ)) / r⟩ : ℂ) = ((r : ℂ)) := by
    rw [hcos, hsin, mul_zero, add_zero, zero_div]
    refine Complex.ext ?_ ?_
    · simp only [Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
      rw [show ((-1 : ℝ) ^ m : ℝ) * (r * ((-1 : ℝ) ^ m : ℝ)) = r by
        have h : ((-1 : ℝ) ^ m : ℝ) * (r * ((-1 : ℝ) ^ m : ℝ))
            = r * (((-1 : ℝ) ^ m : ℝ) * ((-1 : ℝ) ^ m : ℝ)) := by ring
        rw [h, hcsq, mul_one]]
    · simp only [Complex.smul_im, Complex.ofReal_im, smul_eq_mul]
      ring
  rw [upperLift, show ⌊((m : ℤ) : ℝ)⌋ = m by exact Int.floor_intCast m, hz,
    Complex.arg_ofReal_of_nonneg (le_of_lt hr)]
  norm_num

/-- The right-cell formula: for `s ∈ [0,1)`, `t = m + s`, the lift is `m` plus the argument
of the cell vector. -/
theorem upperLift_right {r : ℝ} (q s : ℝ) (m : ℤ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    upperLift r q ((m : ℝ) + s) = (m : ℝ) +
      (Complex.arg (⟨r * Real.cos (Real.pi * s) + q * Real.sin (Real.pi * s),
        Real.sin (Real.pi * s) / r⟩ : ℂ)) / Real.pi := by
  rw [upperLift]
  have hfl : ⌊(m : ℝ) + s⌋ = m := by
    rw [Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  rw [hfl]
  have hcos : Real.cos (Real.pi * ((m : ℝ) + s))
      = ((-1 : ℝ) ^ m : ℝ) * Real.cos (Real.pi * s) := by
    rw [show Real.pi * ((m : ℝ) + s) = Real.pi * s + (m : ℝ) * Real.pi by ring,
      Real.cos_add_int_mul_pi]
  have hsin : Real.sin (Real.pi * ((m : ℝ) + s))
      = ((-1 : ℝ) ^ m : ℝ) * Real.sin (Real.pi * s) := by
    rw [show Real.pi * ((m : ℝ) + s) = Real.pi * s + (m : ℝ) * Real.pi by ring,
      Real.sin_add_int_mul_pi]
  have hcsq : ((-1 : ℝ) ^ m : ℝ) * ((-1 : ℝ) ^ m : ℝ) = 1 := by
    rcases Int.even_or_odd m with h | h
    · rw [h.neg_one_zpow]; norm_num
    · rw [h.neg_one_zpow]; norm_num
  have hvec : (((-1 : ℝ) ^ m : ℝ)) •
      (⟨r * Real.cos (Real.pi * ((m : ℝ) + s)) + q * Real.sin (Real.pi * ((m : ℝ) + s)),
        Real.sin (Real.pi * ((m : ℝ) + s)) / r⟩ : ℂ)
      = (⟨r * Real.cos (Real.pi * s) + q * Real.sin (Real.pi * s),
        Real.sin (Real.pi * s) / r⟩ : ℂ) := by
    rw [hcos, hsin]
    rw [show (((-1 : ℝ) ^ m : ℝ)) •
        (⟨r * (((-1 : ℝ) ^ m : ℝ) * Real.cos (Real.pi * s)) +
            q * (((-1 : ℝ) ^ m : ℝ) * Real.sin (Real.pi * s)),
          (((-1 : ℝ) ^ m : ℝ) * Real.sin (Real.pi * s)) / r⟩ : ℂ)
        = (((-1 : ℝ) ^ m : ℝ)) • ((((-1 : ℝ) ^ m : ℝ)) •
            (⟨r * Real.cos (Real.pi * s) + q * Real.sin (Real.pi * s),
              Real.sin (Real.pi * s) / r⟩ : ℂ)) from by
      congr 1
      refine Complex.ext ?_ ?_ <;> simp only [Complex.smul_re, Complex.smul_im] <;> ring]
    rw [smul_smul, hcsq, one_smul]
  rw [hvec]

/-- The left-cell formula: for `s ∈ (-1,0]`, `t = m + s`, the lift is `m` plus the argument
of the same cell vector (by `arg (-w) = arg w + π`). -/
theorem upperLift_left {r : ℝ} (hr : 0 < r) (q s : ℝ) (m : ℤ) (hs0 : s < 0) (hs1 : -1 < s) :
    upperLift r q ((m : ℝ) + s) = (m : ℝ) +
      (Complex.arg (⟨r * Real.cos (Real.pi * s) + q * Real.sin (Real.pi * s),
        Real.sin (Real.pi * s) / r⟩ : ℂ)) / Real.pi := by
  rw [upperLift]
  have hfl : ⌊(m : ℝ) + s⌋ = m - 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · push_cast; linarith
    · push_cast; linarith
  rw [hfl]
  have hcos : Real.cos (Real.pi * ((m : ℝ) + s))
      = ((-1 : ℝ) ^ m : ℝ) * Real.cos (Real.pi * s) := by
    rw [show Real.pi * ((m : ℝ) + s) = Real.pi * s + (m : ℝ) * Real.pi by ring,
      Real.cos_add_int_mul_pi]
  have hsin : Real.sin (Real.pi * ((m : ℝ) + s))
      = ((-1 : ℝ) ^ m : ℝ) * Real.sin (Real.pi * s) := by
    rw [show Real.pi * ((m : ℝ) + s) = Real.pi * s + (m : ℝ) * Real.pi by ring,
      Real.sin_add_int_mul_pi]
  have hone : (((-1 : ℝ) ^ (m - 1) : ℝ)) * (((-1 : ℝ) ^ m : ℝ)) = -1 := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    have h2 : m - 1 + m = 2 * m - 1 := by ring
    rw [h2, Odd.neg_one_zpow]
    exact ⟨m - 1, by ring⟩
  have hvec : (((-1 : ℝ) ^ (m - 1) : ℝ)) •
      (⟨r * Real.cos (Real.pi * ((m : ℝ) + s)) + q * Real.sin (Real.pi * ((m : ℝ) + s)),
        Real.sin (Real.pi * ((m : ℝ) + s)) / r⟩ : ℂ)
      = -(⟨r * Real.cos (Real.pi * s) + q * Real.sin (Real.pi * s),
        Real.sin (Real.pi * s) / r⟩ : ℂ) := by
    rw [hcos, hsin]
    rw [show (((-1 : ℝ) ^ (m - 1) : ℝ)) •
        (⟨r * (((-1 : ℝ) ^ m : ℝ) * Real.cos (Real.pi * s)) +
            q * (((-1 : ℝ) ^ m : ℝ) * Real.sin (Real.pi * s)),
          (((-1 : ℝ) ^ m : ℝ) * Real.sin (Real.pi * s)) / r⟩ : ℂ)
        = (((-1 : ℝ) ^ (m - 1) : ℝ)) • ((((-1 : ℝ) ^ m : ℝ)) •
            (⟨r * Real.cos (Real.pi * s) + q * Real.sin (Real.pi * s),
              Real.sin (Real.pi * s) / r⟩ : ℂ)) from by
      congr 1
      refine Complex.ext ?_ ?_ <;> simp only [Complex.smul_re, Complex.smul_im] <;> ring]
    rw [smul_smul, hone]
    rw [show ((-1 : ℝ)) • (⟨r * Real.cos (Real.pi * s) + q * Real.sin (Real.pi * s),
        Real.sin (Real.pi * s) / r⟩ : ℂ)
        = -(⟨r * Real.cos (Real.pi * s) + q * Real.sin (Real.pi * s),
          Real.sin (Real.pi * s) / r⟩ : ℂ) from by
      refine Complex.ext ?_ ?_ <;> simp only [Complex.neg_re, Complex.neg_im, Complex.smul_re,
        Complex.smul_im] <;> ring]
  rw [hvec]
  have hsneg : Real.sin (Real.pi * s) < 0 := by
    have h1 : 0 < Real.pi * (-s) := by nlinarith [Real.pi_pos, hs1]
    have h2 : Real.pi * (-s) < Real.pi := by nlinarith [Real.pi_pos, hs0, hs1]
    have h3 : 0 < Real.sin (Real.pi * (-s)) := Real.sin_pos_of_pos_of_lt_pi h1 h2
    have h4 : Real.sin (Real.pi * s) = -Real.sin (Real.pi * (-s)) := by
      rw [show Real.pi * s = -(Real.pi * (-s)) by ring, Real.sin_neg]
    linarith
  have him : (⟨r * Real.cos (Real.pi * s) + q * Real.sin (Real.pi * s),
      Real.sin (Real.pi * s) / r⟩ : ℂ).im < 0 := by
    simp only [Complex.ofReal_im]
    exact div_neg_of_neg_of_pos hsneg hr
  rw [show (-(⟨r * Real.cos (Real.pi * s) + q * Real.sin (Real.pi * s),
      Real.sin (Real.pi * s) / r⟩ : ℂ)).arg
      = (⟨r * Real.cos (Real.pi * s) + q * Real.sin (Real.pi * s),
        Real.sin (Real.pi * s) / r⟩ : ℂ).arg + Real.pi from
    (Complex.arg_neg_eq_arg_add_pi_iff (x := (⟨r * Real.cos (Real.pi * s) +
      q * Real.sin (Real.pi * s), Real.sin (Real.pi * s) / r⟩ : ℂ))).mpr (Or.inl him)]
  push_cast
  rw [add_div, div_self Real.pi_ne_zero]
  ring


theorem complex_norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  have h : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h2 : z.re ^ 2 + z.im ^ 2 ≤ (|z.re| + |z.im|) ^ 2 := by
    rw [add_sq, sq_abs, sq_abs]
    nlinarith [abs_nonneg z.re, abs_nonneg z.im]
  nlinarith [norm_nonneg z, abs_nonneg z.re, abs_nonneg z.im]

/-- Continuity of a `ℂ`-valued map given by its two real components. -/
theorem continuousAt_complexMk {X : Type*} [PseudoMetricSpace X] {f g : X → ℝ} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun y => (⟨f y, g y⟩ : ℂ)) x := by
  rw [Metric.continuousAt_iff]
  intro η hη
  obtain ⟨δ₁, hδ₁, h1⟩ := Metric.mem_nhds_iff.mp
    (hf.tendsto.eventually (Metric.ball_mem_nhds _ (by linarith : (0 : ℝ) < η / 2)))
  obtain ⟨δ₂, hδ₂, h2⟩ := Metric.mem_nhds_iff.mp
    (hg.tendsto.eventually (Metric.ball_mem_nhds _ (by linarith : (0 : ℝ) < η / 2)))
  refine ⟨min δ₁ δ₂, by positivity, fun y hy => ?_⟩
  have hy1 : dist (f y) (f x) < η / 2 := h1 (lt_of_lt_of_le hy (min_le_left _ _))
  have hy2 : dist (g y) (g x) < η / 2 := h2 (lt_of_lt_of_le hy (min_le_right _ _))
  have hle := complex_norm_le_abs_re_add_abs_im ((⟨f y, g y⟩ : ℂ) - (⟨f x, g x⟩ : ℂ))
  rw [Complex.dist_eq]
  simp only [Complex.sub_re, Complex.sub_im] at hle
  rw [Real.dist_eq] at hy1 hy2
  linarith

/-- On the interval `[m, m+1]` the vector `z(t - m)` equals `(-1)^m • z(t)`: the shift by an
integer changes the components by the sign `(-1)^m`. -/
theorem upperLift_vec_sub (r q : ℝ) (m : ℤ) (t : ℝ) :
    (⟨r * Real.cos (Real.pi * (t - (m : ℝ))) + q * Real.sin (Real.pi * (t - (m : ℝ))),
      Real.sin (Real.pi * (t - (m : ℝ))) / r⟩ : ℂ)
      = ((-1 : ℝ) ^ m) •
        (⟨r * Real.cos (Real.pi * t) + q * Real.sin (Real.pi * t),
          Real.sin (Real.pi * t) / r⟩ : ℂ) := by
  have hc : Real.cos (Real.pi * (t - (m : ℝ))) = (-1 : ℝ) ^ m * Real.cos (Real.pi * t) := by
    rw [show Real.pi * (t - (m : ℝ)) = Real.pi * t - (m : ℝ) * Real.pi by ring]
    exact Real.cos_sub_int_mul_pi _ m
  have hs : Real.sin (Real.pi * (t - (m : ℝ))) = (-1 : ℝ) ^ m * Real.sin (Real.pi * t) := by
    rw [show Real.pi * (t - (m : ℝ)) = Real.pi * t - (m : ℝ) * Real.pi by ring]
    exact Real.sin_sub_int_mul_pi _ m
  refine Complex.ext ?_ ?_
  · rw [Complex.smul_re, smul_eq_mul, hc, hs]
    ring
  · rw [Complex.smul_im, smul_eq_mul, hs]
    ring

theorem upperLift_continuousAt {r₀ q₀ t₀ : ℝ} (hr : 0 < r₀) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => upperLift p.1 p.2.1 p.2.2) (r₀, q₀, t₀) := by
  by_cases hint : ((⌊t₀⌋ : ℤ) : ℝ) = t₀
  · -- the integer case
    set m : ℤ := ⌊t₀⌋ with hm
    have ht : t₀ = (m : ℝ) := by rw [hm]; exact hint.symm
    rw [ht]
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hπε : 0 < Real.pi * ε := mul_pos Real.pi_pos hε
    have hslit : (r₀ : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by simpa using hr)
    have hcontarg : Filter.Tendsto Complex.arg (𝓝 ((r₀ : ℂ))) (𝓝 0) := by
      have h := Complex.continuousAt_arg hslit
      rw [ContinuousAt] at h
      rwa [Complex.arg_ofReal_of_nonneg (le_of_lt hr)] at h
    have hev : ∀ᶠ w in 𝓝 ((r₀ : ℂ)), |Complex.arg w| < Real.pi * ε := by
      have h := hcontarg.eventually (Metric.ball_mem_nhds 0 hπε)
      filter_upwards [h] with w hw
      simpa [Real.dist_eq] using hw
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp hev
    have hre : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 (r₀, q₀, (m : ℝ)),
        |p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
          p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))) - r₀| < δ₁ / 2 := by
      have hcont : ContinuousAt (fun p : ℝ × ℝ × ℝ =>
          p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
            p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))) - r₀) (r₀, q₀, (m : ℝ)) := by
        fun_prop
      have := hcont.tendsto.eventually (Metric.ball_mem_nhds _ (by linarith : (0:ℝ) < δ₁ / 2))
      filter_upwards [this] with p hp
      simpa [Real.dist_eq] using hp
    have him : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 (r₀, q₀, (m : ℝ)),
        |Real.sin (Real.pi * (p.2.2 - (m : ℝ)))| < δ₁ * r₀ / 4 := by
      have hcont : ContinuousAt (fun p : ℝ × ℝ × ℝ =>
          Real.sin (Real.pi * (p.2.2 - (m : ℝ)))) (r₀, q₀, (m : ℝ)) := by fun_prop
      have := hcont.tendsto.eventually
        (Metric.ball_mem_nhds _ (by positivity : (0:ℝ) < δ₁ * r₀ / 4))
      filter_upwards [this] with p hp
      simpa [Real.dist_eq] using hp
    have hpos : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 (r₀, q₀, (m : ℝ)), r₀ / 2 < p.1 := by
      have hcont : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1) (r₀, q₀, (m : ℝ)) := continuousAt_fst
      have := hcont.tendsto.eventually (Metric.ball_mem_nhds r₀ (by linarith : (0:ℝ) < r₀ / 2))
      filter_upwards [this] with p hp
      rw [Real.dist_eq, abs_lt] at hp
      linarith [hp.2]
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.mem_nhds_iff.mp hre
    obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := Metric.mem_nhds_iff.mp him
    obtain ⟨δ₄, hδ₄pos, hδ₄⟩ := Metric.mem_nhds_iff.mp hpos
    refine ⟨min (min δ₂ δ₃) (min δ₄ 1), by positivity, fun p hp => ?_⟩
    have hp2 : p ∈ Metric.ball (r₀, q₀, (m : ℝ)) δ₂ := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hp (le_trans (min_le_left _ _) (min_le_left _ _))
    have hp3 : p ∈ Metric.ball (r₀, q₀, (m : ℝ)) δ₃ := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hp (le_trans (min_le_left _ _) (min_le_right _ _))
    have hp4 : p ∈ Metric.ball (r₀, q₀, (m : ℝ)) δ₄ := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hp (le_trans (min_le_right _ _) (min_le_left _ _))
    have hp1 : dist p (r₀, q₀, (m : ℝ)) < 1 :=
      lt_of_lt_of_le hp (le_trans (min_le_right _ _) (min_le_right _ _))
    have hre' : |p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
        p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))) - r₀| < δ₁ / 2 := hδ₂ hp2
    have him' : |Real.sin (Real.pi * (p.2.2 - (m : ℝ)))| < δ₁ * r₀ / 4 := hδ₃ hp3
    have hpos' : r₀ / 2 < p.1 := hδ₄ hp4
    have hcomp : max (max (dist p.1 r₀) (dist p.2.1 q₀)) (dist p.2.2 (m : ℝ)) < 1 := by
      have h : max (dist p.1 r₀) (max (dist p.2.1 q₀) (dist p.2.2 (m : ℝ))) < 1 := by
        simpa only [Prod.dist_eq] using hp1
      rwa [← max_assoc] at h
    have ht1 : |p.2.2 - (m : ℝ)| < 1 := by
      have h := (max_lt_iff.mp hcomp).2
      rwa [Real.dist_eq] at h
    have hrpos : 0 < p.1 := by linarith [hpos', hr]
    have hbase : upperLift r₀ q₀ (m : ℝ) = (m : ℝ) := upperLift_of_int hr q₀ m
    have hVclose : dist (⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
        p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
        Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ) ((r₀ : ℂ)) < δ₁ := by
      rw [Complex.dist_eq]
      have hle := complex_norm_le_abs_re_add_abs_im
        ((⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
          p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
          Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ) - (r₀ : ℂ))
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        sub_zero] at hle
      have him3 : |Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1| < δ₁ / 2 := by
        rw [abs_div, abs_of_pos hrpos, div_lt_iff₀ hrpos]
        nlinarith [him', hr, hpos']
      linarith [hle, hre', him3]
    have hargsmall : |Complex.arg (⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
        p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
        Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ)| < Real.pi * ε :=
      hδ₁ (by simpa [Metric.mem_ball] using hVclose)
    rcases lt_trichotomy p.2.2 (m : ℝ) with hlt | heq | hgt
    · -- below: the left cell
      have hcell : upperLift p.1 p.2.1 ((m : ℝ) + (p.2.2 - (m : ℝ))) =
          (m : ℝ) + (Complex.arg (⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
            p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
            Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ)) / Real.pi :=
        upperLift_left hrpos p.2.1 (p.2.2 - (m : ℝ)) m (by linarith)
          (by rw [abs_lt] at ht1; linarith [ht1.1])
      rw [add_sub_cancel] at hcell
      rw [hcell, Real.dist_eq, hbase]
      have hsimp : (m : ℝ) + (Complex.arg (⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
            p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
            Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ)) / Real.pi - (m : ℝ)
          = (Complex.arg (⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
            p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
            Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ)) / Real.pi := by ring
      rw [hsimp, abs_div, abs_of_pos Real.pi_pos, div_lt_iff₀ Real.pi_pos]
      linarith [hargsmall]
    · -- exactly `m`
      rw [heq]
      have hcell : upperLift p.1 p.2.1 (m : ℝ) = (m : ℝ) := upperLift_of_int hrpos p.2.1 m
      rw [hcell, hbase, Real.dist_eq, sub_self, abs_zero]
      exact hε
    · -- above: the right cell
      have hcell : upperLift p.1 p.2.1 ((m : ℝ) + (p.2.2 - (m : ℝ))) =
          (m : ℝ) + (Complex.arg (⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
            p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
            Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ)) / Real.pi :=
        upperLift_right p.2.1 (p.2.2 - (m : ℝ)) m (by linarith)
          (by rw [abs_lt] at ht1; linarith [ht1.2])
      rw [add_sub_cancel] at hcell
      rw [hcell, Real.dist_eq, hbase]
      have hsimp : (m : ℝ) + (Complex.arg (⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
            p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
            Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ)) / Real.pi - (m : ℝ)
          = (Complex.arg (⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
            p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
            Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ)) / Real.pi := by ring
      rw [hsimp, abs_div, abs_of_pos Real.pi_pos, div_lt_iff₀ Real.pi_pos]
      linarith [hargsmall]
  · -- the non-integer case: `upperLift` is locally given by a continuous formula
    set m : ℤ := ⌊t₀⌋ with hm
    have hmlt : (m : ℝ) < t₀ := by
      have h1 : (m : ℝ) ≤ t₀ := by rw [hm]; exact Int.floor_le t₀
      have h2 : (m : ℝ) ≠ t₀ := by rw [hm]; exact hint
      exact lt_of_le_of_ne h1 h2
    have hmlt' : t₀ < (m : ℝ) + 1 := by rw [hm]; exact Int.lt_floor_add_one t₀
    set s₀ : ℝ := t₀ - (m : ℝ) with hs₀
    have hs₀pos : 0 < s₀ := by rw [hs₀]; linarith
    have hs₀lt : s₀ < 1 := by rw [hs₀]; linarith
    have hslit : (⟨r₀ * Real.cos (Real.pi * s₀) + q₀ * Real.sin (Real.pi * s₀),
        Real.sin (Real.pi * s₀) / r₀⟩ : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      refine Or.inr ?_
      simp only [Complex.ofReal_im]
      exact ne_of_gt (div_pos (Real.sin_pos_of_pos_of_lt_pi (by positivity)
        (by nlinarith [Real.pi_pos])) hr)
    have hcontformula : ContinuousAt (fun p : ℝ × ℝ × ℝ => (m : ℝ) +
        (Complex.arg (⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
          p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
          Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ)) / Real.pi)
        (r₀, q₀, t₀) := by
      have h1 : ContinuousAt (fun p : ℝ × ℝ × ℝ =>
          ((p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
            p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))) : ℝ) : ℂ)) (r₀, q₀, t₀) :=
        Complex.continuous_ofReal.continuousAt.comp (by fun_prop)
      have h2 : ContinuousAt (fun p : ℝ × ℝ × ℝ =>
          ((Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1 : ℝ) : ℂ) * Complex.I)
          (r₀, q₀, t₀) := by
        refine ContinuousAt.mul ?_ continuousAt_const
        exact Complex.continuous_ofReal.continuousAt.comp
          (ContinuousAt.div (by fun_prop) continuousAt_fst (ne_of_gt hr))
      have h3 : ContinuousAt (fun p : ℝ × ℝ × ℝ =>
          (⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
            p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
            Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ)) (r₀, q₀, t₀) := by
        refine continuousAt_complexMk ?_ ?_
        · fun_prop
        · exact ContinuousAt.div (by fun_prop) continuousAt_fst (ne_of_gt hr)
      have h4 : ContinuousAt (fun p : ℝ × ℝ × ℝ => Complex.arg
          (⟨p.1 * Real.cos (Real.pi * (p.2.2 - (m : ℝ))) +
            p.2.1 * Real.sin (Real.pi * (p.2.2 - (m : ℝ))),
            Real.sin (Real.pi * (p.2.2 - (m : ℝ))) / p.1⟩ : ℂ)) (r₀, q₀, t₀) := by
        refine ContinuousAt.comp (g := Complex.arg) ?_ h3
        have hpt : (⟨r₀ * Real.cos (Real.pi * s₀) + q₀ * Real.sin (Real.pi * s₀),
            Real.sin (Real.pi * s₀) / r₀⟩ : ℂ)
            = (⟨r₀ * Real.cos (Real.pi * (t₀ - (m : ℝ))) +
              q₀ * Real.sin (Real.pi * (t₀ - (m : ℝ))),
              Real.sin (Real.pi * (t₀ - (m : ℝ))) / r₀⟩ : ℂ) := by rw [hs₀]
        rw [hpt]
        exact Complex.continuousAt_arg hslit
      exact (h4.div_const Real.pi).const_add (m : ℝ)
    refine hcontformula.congr ?_
    have hopen : Set.Ioo ((m : ℝ)) ((m : ℝ) + 1) ∈ 𝓝 t₀ :=
      isOpen_Ioo.mem_nhds ⟨hmlt, hmlt'⟩
    have hpr : ∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 (r₀, q₀, t₀),
        p.2.2 ∈ Set.Ioo ((m : ℝ)) ((m : ℝ) + 1) := by
      have hc : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.2) (r₀, q₀, t₀) := by fun_prop
      exact hc.preimage_mem_nhds hopen
    filter_upwards [hpr] with p hp
    have hfl : ⌊p.2.2⌋ = m := by
      rw [Int.floor_eq_iff]
      exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
    rw [upperLift, hfl, ← upperLift_vec_sub p.1 p.2.1 m p.2.2]

end

end Work.TMComp.RotBasics
