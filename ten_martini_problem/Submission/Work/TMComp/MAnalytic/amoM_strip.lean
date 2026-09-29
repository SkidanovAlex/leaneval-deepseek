import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMComp.MAnalytic.strip_defs

open Filter
open scoped Topology BigOperators

namespace Work.TMComp.MAnalytic

noncomputable section

open Work.TMContract

/-! ## 1. Elementary bounds for the complex cosine -/

lemma cos_norm_le_cosh (w : ℂ) : ‖Complex.cos w‖ ≤ Real.cosh w.im := by
  have h1 : ‖Complex.exp (w * Complex.I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp, Complex.mul_I_re]
  have h2 : ‖Complex.exp (-w * Complex.I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp, Complex.mul_I_re]; simp
  rw [Complex.cos]
  calc ‖(Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2‖
      = ‖(Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I))‖ / 2 := by
        rw [norm_div]; norm_num
    _ ≤ (‖Complex.exp (w * Complex.I)‖ + ‖Complex.exp (-w * Complex.I)‖) / 2 := by
        gcongr; exact norm_add_le _ _
    _ = (Real.exp (-w.im) + Real.exp w.im) / 2 := by rw [h1, h2]
    _ = Real.cosh w.im := by rw [Real.cosh_eq]; ring

lemma cos_im_abs_le (w : ℂ) : |(Complex.cos w).im| ≤ Real.sinh |w.im| := by
  have h : Complex.cos w =
      ((Real.cos w.re * Real.cosh w.im : ℝ) : ℂ)
        - ((Real.sin w.re * Real.sinh w.im : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cos_eq, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
    push_cast; ring
  rw [h]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, add_zero]
  rw [abs_neg, abs_mul, Real.abs_sinh]
  calc |Real.sin w.re| * Real.sinh |w.im| ≤ 1 * Real.sinh |w.im| := by
        apply mul_le_mul_of_nonneg_right
          (by rw [abs_le]; exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)
        exact (Real.sinh_nonneg_iff).mpr (abs_nonneg _)
    _ = Real.sinh |w.im| := one_mul _

/-! ## 2. The inhomogeneity `stripA` -/

lemma stripA_eq (α lam : ℝ) (z x : ℂ) :
    stripA α lam z x = z - ((2 * lam : ℝ) : ℂ) * Complex.cos (2 * Real.pi * (x - α)) := by
  unfold stripA; push_cast; ring

lemma stripA_im (α lam : ℝ) (z x : ℂ) :
    (stripA α lam z x).im = z.im - 2 * lam * (Complex.cos (2 * Real.pi * (x - α))).im := by
  rw [stripA_eq, Complex.sub_im, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, add_zero]
  ring

lemma stripA_im_lower (α : ℝ) {lam σ : ℝ} (hlam : 0 ≤ lam) (z : ℂ) {x : ℂ}
    (hx : |x.im| < σ) :
    z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ (stripA α lam z x).im := by
  have hσ : 0 < σ := lt_of_le_of_lt (abs_nonneg _) hx
  rw [stripA_im]
  have h1 : (Complex.cos (2 * Real.pi * (x - α))).im ≤ Real.sinh (2 * Real.pi * σ) := by
    calc (Complex.cos (2 * Real.pi * (x - α))).im
        ≤ |(Complex.cos (2 * Real.pi * (x - α))).im| := le_abs_self _
      _ ≤ Real.sinh |(2 * Real.pi * (x - α)).im| := cos_im_abs_le _
      _ ≤ Real.sinh (2 * Real.pi * σ) := by
          rw [Real.sinh_le_sinh]
          have h2 : (2 * Real.pi * (x - α)).im = 2 * Real.pi * x.im := by simp [Complex.sub_im]
          rw [h2, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
          have : |x.im| ≤ σ := le_of_lt hx
          nlinarith [Real.pi_pos]
  nlinarith [h1, hlam]

lemma stripA_norm_upper (α : ℝ) {lam σ : ℝ} (hlam : 0 ≤ lam) (z : ℂ) {x : ℂ}
    (hx : |x.im| < σ) :
    ‖stripA α lam z x‖ ≤ ‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) := by
  have hσ : 0 < σ := lt_of_le_of_lt (abs_nonneg _) hx
  have h1 : ‖Complex.cos (2 * Real.pi * (x - α))‖ ≤ Real.cosh (2 * Real.pi * σ) := by
    calc ‖Complex.cos (2 * Real.pi * (x - α))‖ ≤ Real.cosh (2 * Real.pi * (x - α)).im :=
          cos_norm_le_cosh _
      _ ≤ Real.cosh (2 * Real.pi * σ) := by
          rw [Real.cosh_le_cosh]
          have h2 : (2 * Real.pi * (x - α)).im = 2 * Real.pi * x.im := by simp [Complex.sub_im]
          rw [h2, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi),
              abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi * σ)]
          have : |x.im| ≤ σ := le_of_lt hx
          nlinarith [Real.pi_pos]
  rw [stripA_eq]
  have h2lam : (0:ℝ) ≤ 2 * lam := by linarith
  have hnorm : ‖((2*lam:ℝ):ℂ)‖ = 2 * lam := by
    have h2 : ‖((2*lam:ℝ):ℂ)‖ = |2 * lam| := by simp
    rw [h2, abs_of_nonneg h2lam]
  calc ‖z - ↑(2 * lam) * Complex.cos (2 * ↑Real.pi * (x - ↑α))‖
      ≤ ‖z‖ + ‖↑(2 * lam) * Complex.cos (2 * ↑Real.pi * (x - ↑α))‖ := norm_sub_le _ _
    _ = ‖z‖ + 2 * lam * ‖Complex.cos (2 * ↑Real.pi * (x - ↑α))‖ := by rw [norm_mul, hnorm]
    _ ≤ ‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) := by
        nlinarith [mul_le_mul_of_nonneg_left h1 h2lam]

lemma stripA_differentiable (α lam : ℝ) (z : ℂ) : Differentiable ℂ (stripA α lam z) := by
  unfold stripA; fun_prop

lemma stripA_ofReal_im (α lam : ℝ) (z : ℂ) (x : ℝ) : (stripA α lam z (x:ℂ)).im = z.im := by
  have hw : (2 * (↑Real.pi : ℂ) * ((x : ℂ) - α)) = ((2 * Real.pi * (x - α) : ℝ) : ℂ) := by
    push_cast; ring
  have hcos : (Complex.cos (2 * (↑Real.pi : ℂ) * ((x : ℂ) - α))).im = 0 := by
    rw [hw, ← Complex.ofReal_cos, Complex.ofReal_im]
  rw [stripA_eq, Complex.sub_im, Complex.mul_im, hcos]
  simp

/-! ## 3. The backward iterates and the Möbius recursion -/

lemma backIterC_shift (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    backIterC α lam E (n + 1) x = tmC lam E (x - α) * backIterC α lam E n (x - α) := by
  induction n with
  | zero => simp [backIterC]
  | succ n ih =>
    have hstep : backIterC α lam E (n + 2) x
        = backIterC α lam E (n + 1) x * tmC lam E (x - ((n : ℝ) + 1 + 1) * α) := by
      simp [backIterC]
    have hstep2 : backIterC α lam E (n + 1) (x - α)
        = backIterC α lam E n (x - α) * tmC lam E ((x - α) - ((n : ℝ) + 1) * α) := by
      simp [backIterC]
    rw [hstep, hstep2, ih, mul_assoc]
    congr 1
    congr 1
    ring_nf

lemma tmC_00 (lam : ℝ) (E : ℂ) (x : ℝ) :
    (tmC lam E x) 0 0 = E - ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) := by simp [tmC]
lemma tmC_01 (lam : ℝ) (E : ℂ) (x : ℝ) : (tmC lam E x) 0 1 = -1 := by simp [tmC]
lemma tmC_10 (lam : ℝ) (E : ℂ) (x : ℝ) : (tmC lam E x) 1 0 = 1 := by simp [tmC]
lemma tmC_11 (lam : ℝ) (E : ℂ) (x : ℝ) : (tmC lam E x) 1 1 = 0 := by simp [tmC]

lemma tmC_zero_zero_eq_stripA (α lam : ℝ) (z : ℂ) (x : ℝ) :
    (tmC lam z (x - α)) 0 0 = stripA α lam z (x : ℂ) := by
  rw [tmC_00, stripA_eq]
  congr 1
  have hcos : Complex.cos (2 * (↑Real.pi:ℂ) * ((x:ℂ) - α))
      = ↑(Real.cos (2 * Real.pi * (x - α))) := by
    rw [show 2 * (↑Real.pi:ℂ) * ((x:ℂ) - α) = ↑(2 * Real.pi * (x - α)) by push_cast; ring]
    rw [← Complex.ofReal_cos]
  rw [hcos, ← Complex.ofReal_mul]

def pnum (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (backIterC α lam z n x) 0 0 * Complex.I + (backIterC α lam z n x) 0 1

def qden (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (backIterC α lam z n x) 1 0 * Complex.I + (backIterC α lam z n x) 1 1

lemma mob_eq_pdivq (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    mob (backIterC α lam z n x) Complex.I = pnum α lam z n x / qden α lam z n x := rfl

lemma pnum_succ (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    pnum α lam z (n + 1) x
      = stripA α lam z (x:ℂ) * pnum α lam z n (x - α) - qden α lam z n (x - α) := by
  unfold pnum qden
  rw [backIterC_shift]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  rw [tmC_zero_zero_eq_stripA]
  simp only [tmC_01, tmC_10, tmC_11]
  ring

lemma qden_succ (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℝ) :
    qden α lam z (n + 1) x = pnum α lam z n (x - α) := by
  unfold qden pnum
  rw [backIterC_shift]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [tmC_01, tmC_10, tmC_11]
  ring

lemma backIterC_aux {α lam : ℝ} {z : ℂ} (hz : 0 < z.im) :
    ∀ n x, pnum α lam z n x ≠ 0 ∧
      0 < (pnum α lam z n x / qden α lam z n x).im := by
  intro n
  induction n with
  | zero =>
    intro x
    constructor
    · rw [pnum]; simp [backIterC]
    · rw [pnum, qden]; simp [backIterC, Complex.I_im]
  | succ n ih =>
    intro x
    obtain ⟨hp, him⟩ := ih (x - α)
    have hp0 : pnum α lam z n (x - α) ≠ 0 := hp
    have him' : 0 < (pnum α lam z (n+1) x / qden α lam z (n+1) x).im := by
      rw [pnum_succ, qden_succ, ← sub_div' hp0, ← inv_div]
      rw [Complex.sub_im, Complex.inv_im, stripA_ofReal_im]
      have hd : 0 ≤ (pnum α lam z n (x-α) / qden α lam z n (x-α)).im
          / Complex.normSq (pnum α lam z n (x-α) / qden α lam z n (x-α)) :=
        div_nonneg him.le (Complex.normSq_nonneg _)
      have heq : -(pnum α lam z n (x - α) / qden α lam z n (x - α)).im
              / Complex.normSq (pnum α lam z n (x - α) / qden α lam z n (x - α))
          = -((pnum α lam z n (x - α) / qden α lam z n (x - α)).im
              / Complex.normSq (pnum α lam z n (x - α) / qden α lam z n (x - α))) := by ring
      rw [heq]
      linarith
    refine ⟨?_, him'⟩
    intro hzero
    have h := him'
    rw [hzero, zero_div, Complex.zero_im] at h
    exact lt_irrefl 0 h

lemma mob_backIterC_succ {α lam : ℝ} {z : ℂ} (hz : 0 < z.im) (n : ℕ) (y : ℝ) :
    mob (backIterC α lam z (n+1) y) Complex.I
      = stripA α lam z (y:ℂ) - (mob (backIterC α lam z n (y-α)) Complex.I)⁻¹ := by
  have hp0 : pnum α lam z n (y-α) ≠ 0 := (backIterC_aux hz n (y-α)).1
  rw [mob_eq_pdivq, mob_eq_pdivq, pnum_succ, qden_succ, ← sub_div' hp0, ← inv_div]

/-! ## 4. The strip iteration -/

lemma stripIter_succ_apply (A : ℂ → ℂ) (α : ℝ) (n : ℕ) (x : ℂ) :
    stripIter A α (n + 1) x = A x - (stripIter A α n (x - α))⁻¹ := by
  rw [stripIter_succ, stripStep_apply]

lemma stripIter_im_lower {α lam σ : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 4 ≤ z.im) (hσ : 0 < σ)
    (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im) :
    ∀ (n : ℕ) (x : ℂ), |x.im| < σ →
      z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ (stripIter (stripA α lam z) α n x).im := by
  have hδ : 0 < z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) := by
    have h1 : z.im / 2 + 2 / z.im ≤ z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) := by linarith
    have h2 : (0:ℝ) < 2 / z.im := by apply div_pos (by norm_num); linarith
    linarith
  intro n
  induction n with
  | zero => intro x hx; simpa using stripA_im_lower α hlam z hx
  | succ n ih =>
    intro x hx
    rw [stripIter_succ_apply]
    have hx' : |(x - α).im| < σ := by simpa [Complex.sub_im] using hx
    have hw : 0 < (stripIter (stripA α lam z) α n (x - α)).im := lt_of_lt_of_le hδ (ih (x-α) hx')
    have hinv : ((stripIter (stripA α lam z) α n (x - α))⁻¹).im ≤ 0 := by
      rw [Complex.inv_im]
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · exact Complex.normSq_nonneg _
    rw [Complex.sub_im]
    linarith [stripA_im_lower α hlam z hx]

lemma stripIter_norm_lower {α lam σ : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 4 ≤ z.im) (hσ : 0 < σ)
    (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im) :
    ∀ (n : ℕ) (x : ℂ), |x.im| < σ → z.im / 2 ≤ ‖stripIter (stripA α lam z) α n x‖ := by
  intro n x hx
  have h1 := stripIter_im_lower (α := α) hlam hz hσ hσz n x hx
  have h2 : z.im / 2 ≤ z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) := by
    have h3 : (0:ℝ) ≤ 2 / z.im := by positivity
    linarith
  calc z.im / 2 ≤ (stripIter (stripA α lam z) α n x).im := le_trans h2 h1
    _ ≤ |(stripIter (stripA α lam z) α n x).im| := le_abs_self _
    _ ≤ ‖stripIter (stripA α lam z) α n x‖ := Complex.abs_im_le_norm _

lemma stripIter_norm_upper {α lam σ : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 4 ≤ z.im) (hσ : 0 < σ)
    (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im) :
    ∀ (n : ℕ) (x : ℂ), |x.im| < σ →
      ‖stripIter (stripA α lam z) α n x‖
        ≤ ‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) + 2 / z.im := by
  intro n
  induction n with
  | zero =>
    intro x hx
    show ‖stripA α lam z x‖ ≤ ‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) + 2 / z.im
    have h : ‖stripA α lam z x‖ ≤ ‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) :=
      stripA_norm_upper α hlam z hx
    have h2 : (0:ℝ) ≤ 2 / z.im := by positivity
    linarith
  | succ n ih =>
    intro x hx
    rw [stripIter_succ_apply]
    have hx' : |(x - α).im| < σ := by simpa [Complex.sub_im] using hx
    have hlow := stripIter_norm_lower (α := α) hlam hz hσ hσz n (x-α) hx'
    have hinv : ‖(stripIter (stripA α lam z) α n (x - α))⁻¹‖ ≤ 2 / z.im := by
      rw [norm_inv]
      have hpos : (0:ℝ) < z.im / 2 := by linarith
      have h1 : (1:ℝ) / ‖stripIter (stripA α lam z) α n (x - α)‖ ≤ 1 / (z.im / 2) :=
        one_div_le_one_div_of_le hpos hlow
      have h2 : (1:ℝ) / (z.im / 2) = 2 / z.im := by rw [one_div, inv_div]
      rw [← one_div, ← h2]
      exact h1
    calc ‖stripA α lam z x - (stripIter (stripA α lam z) α n (x - α))⁻¹‖
        ≤ ‖stripA α lam z x‖ + ‖(stripIter (stripA α lam z) α n (x - α))⁻¹‖ := norm_sub_le _ _
      _ ≤ (‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ)) + 2 / z.im := by
          linarith [stripA_norm_upper α hlam z hx, hinv]
      _ = ‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) + 2 / z.im := by ring

lemma inv_sub_inv_bound {Y : ℝ} (hY : 0 < Y) {u v : ℂ} (hu : Y ≤ ‖u‖) (hv : Y ≤ ‖v‖) :
    ‖u⁻¹ - v⁻¹‖ ≤ (1 / Y^2) * ‖u - v‖ := by
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; linarith
  have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; linarith
  have h1 : Y^2 ≤ ‖u‖ * ‖v‖ := by nlinarith [hu, hv, hY, norm_nonneg u, norm_nonneg v]
  have h3 : (0:ℝ) < Y^2 := by positivity
  have h4 : (1:ℝ) ≤ (1 / Y^2) * (‖u‖ * ‖v‖) := by
    have he : (1 / Y^2) * (‖u‖ * ‖v‖) = (‖u‖ * ‖v‖) / Y^2 := by ring
    rw [he, le_div_iff₀ h3, one_mul]
    exact h1
  rw [inv_sub_inv hu0 hv0, norm_div, norm_mul, norm_sub_rev]
  have h2 : (0:ℝ) < ‖u‖ * ‖v‖ := mul_pos (lt_of_lt_of_le hY hu) (lt_of_lt_of_le hY hv)
  rw [div_le_iff₀ h2]
  calc ‖u - v‖ = ‖u - v‖ * 1 := (mul_one _).symm
    _ ≤ ‖u - v‖ * ((1 / Y^2) * (‖u‖ * ‖v‖)) := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = (1 / Y^2) * ‖u - v‖ * (‖u‖ * ‖v‖) := by ring

lemma stripIter_diff {α lam σ : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 4 ≤ z.im) (hσ : 0 < σ)
    (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im) :
    ∀ (n : ℕ) (x : ℂ), |x.im| < σ →
      ‖stripIter (stripA α lam z) α (n + 1) x - stripIter (stripA α lam z) α n x‖
        ≤ (4 / z.im ^ 2) ^ n * (2 / z.im) := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [stripIter_succ_apply, stripIter_zero]
    simp only [pow_zero, one_mul]
    have hx' : |(x - α).im| < σ := by simpa [Complex.sub_im] using hx
    have hlow : z.im / 2 ≤ ‖stripA α lam z (x - α)‖ :=
      stripIter_norm_lower (α := α) hlam hz hσ hσz 0 (x-α) hx'
    have hdiff : (stripA α lam z x - (stripA α lam z (x - α))⁻¹) - stripA α lam z x
        = -(stripA α lam z (x - α))⁻¹ := by ring
    rw [hdiff, norm_neg, norm_inv]
    have hpos : (0:ℝ) < z.im / 2 := by linarith
    have h1 : (1:ℝ) / ‖stripA α lam z (x - α)‖ ≤ 1 / (z.im / 2) :=
      one_div_le_one_div_of_le hpos hlow
    have h2 : (1:ℝ) / (z.im / 2) = 2 / z.im := by rw [one_div, inv_div]
    rw [← one_div, ← h2]
    exact h1
  | succ n ih =>
    intro x hx
    have hx' : |(x - α).im| < σ := by simpa [Complex.sub_im] using hx
    have hp : (0:ℝ) < z.im / 2 := by linarith
    have hn : z.im / 2 ≤ ‖stripIter (stripA α lam z) α n (x - α)‖ :=
      stripIter_norm_lower (α := α) hlam hz hσ hσz n (x-α) hx'
    have hn1 : z.im / 2 ≤ ‖stripIter (stripA α lam z) α (n+1) (x - α)‖ :=
      stripIter_norm_lower (α := α) hlam hz hσ hσz (n+1) (x-α) hx'
    have hb := inv_sub_inv_bound hp hn hn1
    have hdiff : stripIter (stripA α lam z) α (n + 1 + 1) x - stripIter (stripA α lam z) α (n + 1) x
        = (stripIter (stripA α lam z) α n (x - α))⁻¹
          - (stripIter (stripA α lam z) α (n + 1) (x - α))⁻¹ := by
      rw [stripIter_succ_apply (stripA α lam z) α (n+1) x,
          stripIter_succ_apply (stripA α lam z) α n x]
      ring
    rw [hdiff]
    have hih := ih (x-α) hx'
    have hconst : (1:ℝ) / (z.im / 2) ^ 2 = 4 / z.im ^ 2 := by
      have h : (z.im / 2) ^ 2 = z.im ^ 2 / 4 := by ring
      rw [h, one_div, inv_div]
    calc ‖(stripIter (stripA α lam z) α n (x - α))⁻¹
            - (stripIter (stripA α lam z) α (n + 1) (x - α))⁻¹‖
        ≤ (1 / (z.im / 2) ^ 2)
            * ‖stripIter (stripA α lam z) α n (x - α) - stripIter (stripA α lam z) α (n+1) (x - α)‖ := hb
      _ = (1 / (z.im / 2) ^ 2)
            * ‖stripIter (stripA α lam z) α (n+1) (x - α) - stripIter (stripA α lam z) α n (x - α)‖ := by
          rw [norm_sub_rev]
      _ ≤ (1 / (z.im / 2) ^ 2) * ((4 / z.im ^ 2) ^ n * (2 / z.im)) := by
          apply mul_le_mul_of_nonneg_left hih
          positivity
      _ = (4 / z.im ^ 2) ^ (n + 1) * (2 / z.im) := by rw [hconst]; ring

lemma stripIter_differentiable {α lam σ : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 4 ≤ z.im) (hσ : 0 < σ)
    (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im)
    (n : ℕ) :
    DifferentiableOn ℂ (stripIter (stripA α lam z) α n) {x : ℂ | |x.im| < σ} := by
  have hδ : 0 < z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) := by
    have h1 : z.im / 2 + 2 / z.im ≤ z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) := by linarith
    have h2 : (0:ℝ) < 2 / z.im := by apply div_pos (by norm_num); linarith
    linarith
  induction n with
  | zero => exact (stripA_differentiable α lam z).differentiableOn
  | succ n ih =>
    have hne : ∀ x ∈ {x : ℂ | |x.im| < σ}, stripIter (stripA α lam z) α n (x - α) ≠ 0 := by
      intro x hx
      have hx' : |(x - α).im| < σ := by simpa [Complex.sub_im] using hx
      have h := stripIter_im_lower (α := α) hlam hz hσ hσz n (x-α) hx'
      intro hzero
      rw [hzero, Complex.zero_im] at h
      linarith
    have hcomp : DifferentiableOn ℂ (fun x : ℂ => stripIter (stripA α lam z) α n (x - α))
        {x : ℂ | |x.im| < σ} :=
      ih.comp (by fun_prop : DifferentiableOn ℂ (fun x : ℂ => x - α) {x : ℂ | |x.im| < σ})
        (fun x hx => by simpa [Complex.sub_im] using hx)
    have hinv := hcomp.inv hne
    have hfun : stripIter (stripA α lam z) α (n + 1)
        = fun x : ℂ => stripA α lam z x - (stripIter (stripA α lam z) α n (x - α))⁻¹ := by
      funext x; rw [stripIter_succ_apply]
    rw [hfun]
    exact (stripA_differentiable α lam z).differentiableOn.sub hinv

/-! ## 5. The limiting section -/

def stripLim (α lam : ℝ) (z : ℂ) : ℂ → ℂ :=
  fun x => stripA α lam z x +
    ∑' k : ℕ, (stripIter (stripA α lam z) α (k + 1) x - stripIter (stripA α lam z) α k x)

lemma summable_stripIter_diff {α lam σ : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 4 ≤ z.im) (hσ : 0 < σ)
    (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im)
    {x : ℂ} (hx : |x.im| < σ) :
    Summable (fun k : ℕ =>
      stripIter (stripA α lam z) α (k+1) x - stripIter (stripA α lam z) α k x) := by
  have hc0 : (0:ℝ) ≤ 4 / z.im^2 := by positivity
  have hc1 : 4 / z.im^2 < 1 := by
    rw [div_lt_one (by positivity : (0:ℝ) < z.im^2)]
    nlinarith
  refine Summable.of_norm_bounded (g := fun k : ℕ => (2/z.im) * (4/z.im^2)^k)
    ((summable_geometric_of_lt_one hc0 hc1).mul_left _) ?_
  intro k
  have h := stripIter_diff (α := α) hlam hz hσ hσz k x hx
  rwa [mul_comm] at h

lemma stripLim_tendsto {α lam σ : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 4 ≤ z.im) (hσ : 0 < σ)
    (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im)
    {x : ℂ} (hx : |x.im| < σ) :
    Tendsto (fun n : ℕ => stripIter (stripA α lam z) α n x) atTop (nhds (stripLim α lam z x)) := by
  have hs := (summable_stripIter_diff (α := α) hlam hz hσ hσz hx).hasSum
  have h2 := hs.tendsto_sum_nat.const_add (stripA α lam z x)
  have heq : (fun n : ℕ => stripA α lam z x + ∑ k ∈ Finset.range n,
        (stripIter (stripA α lam z) α (k+1) x - stripIter (stripA α lam z) α k x))
      = fun n : ℕ => stripIter (stripA α lam z) α n x := by
    funext n
    have h := Finset.sum_range_sub (fun k => stripIter (stripA α lam z) α k x) n
    simp only [stripIter_zero] at h
    rw [h]; ring
  rw [heq] at h2
  exact h2

lemma stripLim_bound {α lam σ : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 4 ≤ z.im) (hσ : 0 < σ)
    (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im)
    (n : ℕ) {x : ℂ} (hx : |x.im| < σ) :
    ‖stripLim α lam z x - stripIter (stripA α lam z) α n x‖
      ≤ (2 / z.im) * (4 / z.im^2)^n / (1 - 4 / z.im^2) := by
  have hc0 : (0:ℝ) ≤ 4 / z.im^2 := by positivity
  have hc1 : 4 / z.im^2 < 1 := by
    rw [div_lt_one (by positivity : (0:ℝ) < z.im^2)]
    nlinarith
  have hs := summable_stripIter_diff (α := α) hlam hz hσ hσz hx
  have hkey : stripLim α lam z x - stripIter (stripA α lam z) α n x
      = ∑' k : ℕ, (stripIter (stripA α lam z) α (k+n+1) x - stripIter (stripA α lam z) α (k+n) x) := by
    have htel : stripIter (stripA α lam z) α n x
        = stripA α lam z x + ∑ k ∈ Finset.range n,
            (stripIter (stripA α lam z) α (k+1) x - stripIter (stripA α lam z) α k x) := by
      have h := Finset.sum_range_sub (fun k => stripIter (stripA α lam z) α k x) n
      simp only [stripIter_zero] at h
      rw [h]; ring
    show stripA α lam z x +
        (∑' k : ℕ, (stripIter (stripA α lam z) α (k + 1) x - stripIter (stripA α lam z) α k x))
        - stripIter (stripA α lam z) α n x = _
    rw [htel]
    have hsum := Summable.sum_add_tsum_nat_add n hs
    rw [← hsum]
    ring
  rw [hkey]
  have hgnorm : Summable (fun k : ℕ =>
      ‖stripIter (stripA α lam z) α (k+n+1) x - stripIter (stripA α lam z) α (k+n) x‖) := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => (2/z.im) * (4/z.im^2)^(k+n)) ?_ ?_
    · exact (summable_nat_add_iff n).mpr ((summable_geometric_of_lt_one hc0 hc1).mul_left _)
    · intro k
      have h := stripIter_diff (α := α) hlam hz hσ hσz (k+n) x hx
      rw [mul_comm] at h
      simpa only [norm_norm] using h
  have hsumg : Summable (fun k : ℕ => (2/z.im) * (4/z.im^2)^(k+n)) :=
    (summable_nat_add_iff n).mpr ((summable_geometric_of_lt_one hc0 hc1).mul_left _)
  calc ‖∑' k : ℕ, (stripIter (stripA α lam z) α (k+n+1) x - stripIter (stripA α lam z) α (k+n) x)‖
      ≤ ∑' k : ℕ, ‖stripIter (stripA α lam z) α (k+n+1) x - stripIter (stripA α lam z) α (k+n) x‖ :=
        norm_tsum_le_tsum_norm hgnorm
    _ ≤ ∑' k : ℕ, (2/z.im) * (4/z.im^2)^(k+n) := by
        apply Summable.tsum_le_tsum _ hgnorm hsumg
        intro k
        have h := stripIter_diff (α := α) hlam hz hσ hσz (k+n) x hx
        rwa [mul_comm] at h
    _ = (2 / z.im) * (4 / z.im^2)^n / (1 - 4 / z.im^2) := by
        rw [tsum_mul_left]
        have h1 : (∑' k : ℕ, (4/z.im^2)^(k+n)) = (4/z.im^2)^n / (1 - 4/z.im^2) := by
          rw [show (fun k : ℕ => (4/z.im^2)^(k+n))
              = (fun k : ℕ => (4/z.im^2)^k * (4/z.im^2)^n) from by
                funext k; rw [pow_add]]
          rw [tsum_mul_right, tsum_geometric_of_lt_one hc0 hc1]
          ring
        rw [h1]
        ring

/-! ## 6. The main theorem -/

theorem amoM_strip {α lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 4 ≤ z.im) {σ : ℝ}
    (hσ : 0 < σ) (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im) :
    ∃ M : ℂ → ℂ, AnalyticOnNhd ℂ M {x : ℂ | |x.im| < σ} ∧
      (∀ x : ℂ, |x.im| < σ →
        z.im / 2 ≤ ‖M x‖ ∧
        ‖M x‖ ≤ ‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) + 2 / z.im) ∧
      (∀ x : ℂ, |x.im| < σ →
        M x = (z - 2 * lam * Complex.cos (2 * Real.pi * (x - α))) - 1 / M (x - α)) ∧
      (∀ y : ℝ, Filter.Tendsto
        (fun n : ℕ => Work.TMContract.mob (Work.TMContract.backIterC α lam z n y) Complex.I)
        Filter.atTop (nhds (M (y : ℂ)))) := by
  have hlam0 : (0:ℝ) ≤ lam := le_of_lt hlam
  have hzpos : 0 < z.im := by linarith
  have hU : IsOpen {x : ℂ | |x.im| < σ} := isOpen_lt (Complex.continuous_im.abs) continuous_const
  have hδhalf : z.im / 2 ≤ z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) := by
    have h3 : (0:ℝ) ≤ 2 / z.im := by positivity
    linarith
  have hδpos : 0 < z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) := by
    have h1 : z.im / 2 + 2 / z.im ≤ z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) := by linarith
    have h2 : (0:ℝ) < 2 / z.im := by apply div_pos (by norm_num); linarith
    linarith
  have him : ∀ (n : ℕ) (x : ℂ), |x.im| < σ →
      z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ (stripIter (stripA α lam z) α n x).im :=
    fun n x hx => stripIter_im_lower hlam0 hz hσ hσz n x hx
  have hlow : ∀ (n : ℕ) (x : ℂ), |x.im| < σ →
      z.im / 2 ≤ ‖stripIter (stripA α lam z) α n x‖ :=
    fun n x hx => stripIter_norm_lower hlam0 hz hσ hσz n x hx
  have hup : ∀ (n : ℕ) (x : ℂ), |x.im| < σ →
      ‖stripIter (stripA α lam z) α n x‖
        ≤ ‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) + 2 / z.im :=
    fun n x hx => stripIter_norm_upper hlam0 hz hσ hσz n x hx
  have hlim : ∀ x : ℂ, |x.im| < σ →
      Tendsto (fun n : ℕ => stripIter (stripA α lam z) α n x) atTop (nhds (stripLim α lam z x)) :=
    fun x hx => stripLim_tendsto hlam0 hz hσ hσz hx
  have htail : ∀ (n : ℕ) (x : ℂ), |x.im| < σ →
      ‖stripLim α lam z x - stripIter (stripA α lam z) α n x‖
        ≤ (2 / z.im) * (4 / z.im^2)^n / (1 - 4 / z.im^2) :=
    fun n x hx => stripLim_bound hlam0 hz hσ hσz n hx
  have hc0 : (0:ℝ) ≤ 4 / z.im^2 := by positivity
  have hc1 : 4 / z.im^2 < 1 := by
    rw [div_lt_one (by positivity : (0:ℝ) < z.im^2)]
    nlinarith
  have hunif : TendstoUniformlyOn (fun n : ℕ => stripIter (stripA α lam z) α n)
      (stripLim α lam z) atTop {x : ℂ | |x.im| < σ} := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hbd : Tendsto (fun n : ℕ => (2/z.im) * (4/z.im^2)^n / (1 - 4/z.im^2)) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => (4/z.im^2)^n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
      have h2 : Tendsto (fun n : ℕ => (2/z.im) * (4/z.im^2)^n) atTop (nhds ((2/z.im) * 0)) :=
        h1.const_mul _
      have h3 : Tendsto (fun n : ℕ => (2/z.im) * (4/z.im^2)^n / (1 - 4/z.im^2)) atTop
          (nhds (((2/z.im) * 0) / (1 - 4/z.im^2))) := h2.div_const _
      simpa using h3
    rw [Metric.tendsto_atTop] at hbd
    obtain ⟨N, hN⟩ := hbd ε hε
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn x hx => ?_⟩
    have hb : dist (stripLim α lam z x) (stripIter (stripA α lam z) α n x)
        ≤ (2/z.im) * (4/z.im^2)^n / (1 - 4/z.im^2) := by
      rw [dist_eq_norm]; exact htail n x hx
    have hb0 : (0:ℝ) ≤ (2/z.im) * (4/z.im^2)^n / (1 - 4/z.im^2) := by positivity
    have hN' : dist ((2/z.im) * (4/z.im^2)^n / (1 - 4/z.im^2)) 0 < ε := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hb0] at hN'
    linarith
  have hdiffble : ∀ n : ℕ, DifferentiableOn ℂ (stripIter (stripA α lam z) α n)
      {x : ℂ | |x.im| < σ} := fun n => stripIter_differentiable hlam0 hz hσ hσz n
  have hM_an : AnalyticOnNhd ℂ (stripLim α lam z) {x : ℂ | |x.im| < σ} :=
    (hunif.tendstoLocallyUniformlyOn.differentiableOn
      (Filter.Eventually.of_forall hdiffble) hU).analyticOnNhd hU
  have hM_bound : ∀ x : ℂ, |x.im| < σ →
      z.im / 2 ≤ ‖stripLim α lam z x‖ ∧
      ‖stripLim α lam z x‖ ≤ ‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) + 2 / z.im := by
    intro x hx
    have hl := (hlim x hx).norm
    exact ⟨ge_of_tendsto' hl (fun n => hlow n x hx), le_of_tendsto' hl (fun n => hup n x hx)⟩
  have hne0 : ∀ x : ℂ, |x.im| < σ → stripLim α lam z (x - α) ≠ 0 := by
    intro x hx
    have hx' : |(x - α).im| < σ := by simpa [Complex.sub_im] using hx
    intro hzero
    have h1 := (hM_bound (x-α) hx').1
    rw [hzero, norm_zero] at h1
    linarith
  have hM_eq : ∀ x : ℂ, |x.im| < σ →
      stripLim α lam z x
        = (z - 2 * lam * Complex.cos (2 * Real.pi * (x - α))) - 1 / stripLim α lam z (x - α) := by
    intro x hx
    have hx' : |(x - α).im| < σ := by simpa [Complex.sub_im] using hx
    have hL : Tendsto (fun n : ℕ => stripIter (stripA α lam z) α (n+1) x) atTop
        (nhds (stripLim α lam z x)) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mpr (hlim x hx)
    have hR : Tendsto (fun n : ℕ => stripIter (stripA α lam z) α (n+1) x) atTop
        (nhds (stripA α lam z x - (stripLim α lam z (x - α))⁻¹)) := by
      have h0 : Tendsto (fun n : ℕ => stripIter (stripA α lam z) α n (x - α)) atTop
          (nhds (stripLim α lam z (x - α))) := hlim (x-α) hx'
      have h1 := (h0.inv₀ (hne0 x hx)).const_sub (stripA α lam z x)
      refine h1.congr' (Filter.Eventually.of_forall (fun n => ?_))
      exact (stripIter_succ_apply (stripA α lam z) α n x).symm
    have hkey := tendsto_nhds_unique hL hR
    simpa [stripA, one_div] using hkey
  have hg_rec : ∀ (n : ℕ) (y : ℝ), mob (backIterC α lam z (n+1) y) Complex.I
      = stripA α lam z (y:ℂ) - (mob (backIterC α lam z n (y-α)) Complex.I)⁻¹ :=
    fun n y => mob_backIterC_succ hzpos n y
  have hg_im : ∀ (n : ℕ) (y : ℝ),
      z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ (mob (backIterC α lam z (n+1) y) Complex.I).im := by
    intro n
    induction n with
    | zero =>
      intro y
      have h0 : mob (backIterC α lam z 0 (y - α)) Complex.I = Complex.I := by
        simp [mob, backIterC]
      rw [hg_rec 0 y, h0, Complex.inv_I, Complex.sub_im, stripA_ofReal_im, Complex.neg_im, Complex.I_im]
      have hs : (0:ℝ) ≤ 2 * lam * Real.sinh (2 * Real.pi * σ) :=
        mul_nonneg (by linarith) (Real.sinh_nonneg_iff.mpr (by positivity))
      linarith
    | succ n ih =>
      intro y
      rw [hg_rec (n+1) y]
      have h1 : 0 < (mob (backIterC α lam z (n+1) (y - α)) Complex.I).im :=
        lt_of_lt_of_le hδpos (ih (y-α))
      have h2 : ((mob (backIterC α lam z (n+1) (y - α)) Complex.I)⁻¹).im ≤ 0 := by
        rw [Complex.inv_im]
        apply div_nonpos_of_nonpos_of_nonneg
        · linarith
        · exact Complex.normSq_nonneg _
      have hs : (0:ℝ) ≤ 2 * lam * Real.sinh (2 * Real.pi * σ) :=
        mul_nonneg (by linarith) (Real.sinh_nonneg_iff.mpr (by positivity))
      rw [Complex.sub_im, stripA_ofReal_im]
      linarith
  have hg_approx : ∀ (n : ℕ) (y : ℝ),
      ‖mob (backIterC α lam z (n+1) y) Complex.I - stripIter (stripA α lam z) α (n+1) (y:ℂ)‖
        ≤ (4/z.im^2)^n * (1 + 2/z.im) := by
    intro n
    induction n with
    | zero =>
      intro y
      have h0 : mob (backIterC α lam z 0 (y - α)) Complex.I = Complex.I := by
        simp [mob, backIterC]
      have hF : stripIter (stripA α lam z) α 1 (y:ℂ)
          = stripA α lam z (y:ℂ) - (stripA α lam z ((y:ℂ) - α))⁻¹ := by
        rw [show (1:ℕ) = 0 + 1 from rfl, stripIter_succ_apply, stripIter_zero]
      rw [hg_rec 0 y, h0, Complex.inv_I, hF]
      have hdiff : (stripA α lam z (y:ℂ) - -Complex.I)
          - (stripA α lam z (y:ℂ) - (stripA α lam z ((y:ℂ) - α))⁻¹)
          = Complex.I + (stripA α lam z ((y:ℂ) - α))⁻¹ := by ring
      rw [hdiff, pow_zero, one_mul]
      have hx' : |((y:ℂ) - α).im| < σ := by simpa [Complex.sub_im] using hσ
      have hlow0 : z.im / 2 ≤ ‖stripA α lam z ((y:ℂ) - α)‖ :=
        stripIter_norm_lower (α := α) hlam0 hz hσ hσz 0 ((y:ℂ) - α) hx'
      have hinv : ‖(stripA α lam z ((y:ℂ) - α))⁻¹‖ ≤ 2 / z.im := by
        rw [norm_inv]
        have hpos : (0:ℝ) < z.im / 2 := by linarith
        have h1 : (1:ℝ) / ‖stripA α lam z ((y:ℂ) - α)‖ ≤ 1 / (z.im / 2) :=
          one_div_le_one_div_of_le hpos hlow0
        have h2 : (1:ℝ) / (z.im / 2) = 2 / z.im := by rw [one_div, inv_div]
        rw [← one_div, ← h2]
        exact h1
      calc ‖Complex.I + (stripA α lam z ((y:ℂ) - α))⁻¹‖
          ≤ ‖Complex.I‖ + ‖(stripA α lam z ((y:ℂ) - α))⁻¹‖ := norm_add_le _ _
        _ = 1 + ‖(stripA α lam z ((y:ℂ) - α))⁻¹‖ := by simp
        _ ≤ 1 + 2/z.im := by linarith
    | succ n ih =>
      intro y
      have hrecA : mob (backIterC α lam z (n+1+1) y) Complex.I
          = stripA α lam z (y:ℂ) - (mob (backIterC α lam z (n+1) (y-α)) Complex.I)⁻¹ :=
        mob_backIterC_succ hzpos (n+1) y
      have hrecF : stripIter (stripA α lam z) α (n+1+1) (y:ℂ)
          = stripA α lam z (y:ℂ) - (stripIter (stripA α lam z) α (n+1) ((y:ℂ) - α))⁻¹ :=
        stripIter_succ_apply (stripA α lam z) α (n+1) (y:ℂ)
      rw [hrecA, hrecF, ← Complex.ofReal_sub]
      have hdiff : (stripA α lam z (y:ℂ) - (mob (backIterC α lam z (n+1) (y-α)) Complex.I)⁻¹)
          - (stripA α lam z (y:ℂ) - (stripIter (stripA α lam z) α (n+1) ((y-α:ℝ):ℂ))⁻¹)
          = (stripIter (stripA α lam z) α (n+1) ((y-α:ℝ):ℂ))⁻¹
            - (mob (backIterC α lam z (n+1) (y-α)) Complex.I)⁻¹ := by ring
      rw [hdiff]
      have hy' : |(((y-α:ℝ)):ℂ).im| < σ := by simpa using hσ
      have hgn : z.im/2 ≤ ‖mob (backIterC α lam z (n+1) (y-α)) Complex.I‖ := by
        have h1 : z.im/2 ≤ (mob (backIterC α lam z (n+1) (y-α)) Complex.I).im :=
          le_trans hδhalf (hg_im n (y-α))
        calc z.im/2 ≤ (mob (backIterC α lam z (n+1) (y-α)) Complex.I).im := h1
          _ ≤ |(mob (backIterC α lam z (n+1) (y-α)) Complex.I).im| := le_abs_self _
          _ ≤ ‖mob (backIterC α lam z (n+1) (y-α)) Complex.I‖ := Complex.abs_im_le_norm _
      have hfn : z.im/2 ≤ ‖stripIter (stripA α lam z) α (n+1) ((y-α:ℝ):ℂ)‖ :=
        stripIter_norm_lower (α := α) hlam0 hz hσ hσz (n+1) ((y-α:ℝ):ℂ) hy'
      have hb := inv_sub_inv_bound (Y := z.im/2) (by linarith) hgn hfn
      have hconst : (1:ℝ) / (z.im / 2) ^ 2 = 4 / z.im ^ 2 := by
        have h : (z.im / 2) ^ 2 = z.im ^ 2 / 4 := by ring
        rw [h, one_div, inv_div]
      calc ‖(stripIter (stripA α lam z) α (n+1) ((y-α:ℝ):ℂ))⁻¹
              - (mob (backIterC α lam z (n+1) (y-α)) Complex.I)⁻¹‖
          = ‖(mob (backIterC α lam z (n+1) (y-α)) Complex.I)⁻¹
              - (stripIter (stripA α lam z) α (n+1) ((y-α:ℝ):ℂ))⁻¹‖ := norm_sub_rev _ _
        _ ≤ (1 / (z.im / 2) ^ 2)
              * ‖mob (backIterC α lam z (n+1) (y-α)) Complex.I
                  - stripIter (stripA α lam z) α (n+1) ((y-α:ℝ):ℂ)‖ := hb
        _ ≤ (1 / (z.im / 2) ^ 2) * ((4 / z.im ^ 2) ^ n * (1 + 2/z.im)) := by
            apply mul_le_mul_of_nonneg_left (ih (y-α))
            positivity
        _ = (4 / z.im^2)^(n+1) * (1 + 2/z.im) := by rw [hconst]; ring
  have hconv : ∀ y : ℝ, Tendsto (fun n : ℕ => mob (backIterC α lam z n y) Complex.I) atTop
      (nhds (stripLim α lam z (y:ℂ))) := by
    intro y
    have h1 : Tendsto (fun n : ℕ => stripIter (stripA α lam z) α (n+1) (y:ℂ)) atTop
        (nhds (stripLim α lam z (y:ℂ))) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mpr (hlim (y:ℂ) (by simpa using hσ))
    have h2 : Tendsto (fun n : ℕ => mob (backIterC α lam z (n+1) y) Complex.I
        - stripIter (stripA α lam z) α (n+1) (y:ℂ)) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall (fun n => norm_nonneg _)
      · exact Filter.Eventually.of_forall (fun n => hg_approx n y)
      · have hb : Tendsto (fun n : ℕ => (4/z.im^2)^n * (1 + 2/z.im)) atTop (nhds 0) := by
          have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const (1 + 2/z.im)
          simpa using h
        exact hb
    have h3 : Tendsto (fun n : ℕ => mob (backIterC α lam z (n+1) y) Complex.I) atTop
        (nhds (stripLim α lam z (y:ℂ))) := by
      have h := h2.add h1
      simpa using h
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp h3
  exact ⟨stripLim α lam z, hM_an, hM_bound, hM_eq, hconv⟩

end

end Work.TMComp.MAnalytic
