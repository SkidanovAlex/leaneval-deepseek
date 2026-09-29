import Mathlib
import Submission.Work.CNum.BoxSideDefs
import Submission.Work.CNum.NrmSpec

/-!
# `Work.CNum.BoxSide` — the ball `toPB I` contains the box `I`, and every boundary box is `BoxOK`

Two independent halves.

* *Analytic*: `boxSide_pbBound` — for **every** complex interval `I`, every `z ∈ I` satisfies
  `‖z - bpt (toPB I)‖ ≤ m2r (toPB I).e`.  `toPB I` has centre `ic I.re , ic I.im` (mantissas) and
  radius `(3 · max dx dy)/2 + 4`, where `dx`, `dy` are the half-widths of the two coordinate
  intervals.  Since `lo ≤ ic I ≤ hi`, each coordinate of `z - bpt (toPB I)` is bounded by
  `dx/SC`, resp. `dy/SC`, so the norm is at most `√2 · max(dx,dy)/SC ≤ (3/2)·max(dx,dy)/SC`, while
  the ball radius is `≥ (3·max(dx,dy) + 7)/(2·SC)` (the `+4` absorbs the floor of the mantissa
  division).  No side condition (`BoxOK`, `Small`) is needed.

* *Arithmetic*: `BoxOK (ptOf j)` for `0 ≤ j ≤ 1024` and the two cusp boxes.  `BoxOK` is a bundle of
  integer comparisons, decidable at the mantissa level, so the whole range is discharged by kernel
  evaluation of a `Bool` checker; the range is cut into four chunks so that no single `decide`
  invocation carries the whole table.
-/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! ## The decidable mantissa-level side conditions -/

/-- `BoxOK p`, unfolded into a `Bool` (so that the kernel can evaluate it directly). -/
def boxSideOKb (p : Cpx) : Bool :=
  let b := toPB p
  decide (0 ≤ b.e) && decide (b.e ≤ 1024) && decide (Int.natAbs b.x ≤ 2 ^ 34) &&
    decide (Int.natAbs b.y ≤ 2 ^ 34) && decide ((nrmUp b.x b.y + b.e) * 100 ≤ 79 * SC) &&
    decide (b.e < nrmDn b.x b.y)

lemma boxSideOKb_sound {p : Cpx} (h : boxSideOKb p = true) : BoxOK p := by
  simp only [boxSideOKb, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- `boxSideChk a n` checks the side conditions at `ptOf a, …, ptOf (a+n-1)`. -/
def boxSideChk (a : ℕ) : ℕ → Bool
  | 0 => true
  | (n + 1) => boxSideOKb (ptOf (a + n)) && boxSideChk a n

lemma boxSideChk_sound : ∀ (a n : ℕ), boxSideChk a n = true →
    ∀ j, a ≤ j → j < a + n → BoxOK (ptOf j) := by
  intro a n
  induction n with
  | zero => intro h j h1 h2; omega
  | succ n ih =>
    intro h j h1 h2
    simp only [boxSideChk, Bool.and_eq_true] at h
    rcases h with ⟨h1', h2'⟩
    rcases lt_or_ge j (a + n) with hj | hj
    · exact ih h2' j h1 hj
    · have : j = a + n := by omega
      subst this
      exact boxSideOKb_sound h1'

/-- Chunk `0 … 255`. -/
lemma boxSideChk_0 : boxSideChk 0 256 = true := by decide +kernel
/-- Chunk `256 … 511`. -/
lemma boxSideChk_1 : boxSideChk 256 256 = true := by decide +kernel
/-- Chunk `512 … 767`. -/
lemma boxSideChk_2 : boxSideChk 512 256 = true := by decide +kernel
/-- Chunk `768 … 1024`. -/
lemma boxSideChk_3 : boxSideChk 768 257 = true := by decide +kernel

lemma boxSide_ptOf (j : ℕ) (hj : j ≤ 1024) : BoxOK (ptOf j) := by
  rcases le_or_gt j 255 with h | h
  · exact boxSideChk_sound 0 256 boxSideChk_0 j (by omega) (by omega)
  rcases le_or_gt j 511 with h2 | h2
  · exact boxSideChk_sound 256 256 boxSideChk_1 j (by omega) (by omega)
  rcases le_or_gt j 767 with h3 | h3
  · exact boxSideChk_sound 512 256 boxSideChk_2 j (by omega) (by omega)
  · exact boxSideChk_sound 768 257 boxSideChk_3 j (by omega) (by omega)

lemma boxSide_cuspA : BoxOK ptCuspA := boxSideOKb_sound (by decide +kernel)
lemma boxSide_cuspB : BoxOK ptCuspB := boxSideOKb_sound (by decide +kernel)

/-! ## The analytic half: the ball `toPB I` contains the interval `I` -/

lemma boxSide_int_nonneg_of_m2r_nonneg {n : ℤ} (h : 0 ≤ m2r n) : 0 ≤ n := by
  have h2 : (0 : ℝ) ≤ (n : ℝ) := by
    have := mul_nonneg h SC_posR.le
    rwa [m2r, div_mul_cancel₀ _ (ne_of_gt SC_posR)] at this
  exact_mod_cast h2

theorem boxSide_pbBound (I : Cpx) (z : ℂ) (hz : I.Mem z) :
    ‖z - bpt (toPB I)‖ ≤ m2r (toPB I).e := by
  obtain ⟨hzre, hzim⟩ := hz
  obtain ⟨hrelo, hrehi⟩ := hzre
  obtain ⟨himlo, himhi⟩ := hzim
  -- the mantissas of `toPB I`
  let dx : ℤ := max (ic I.re - I.re.lo) (I.re.hi - ic I.re)
  let dy : ℤ := max (ic I.im - I.im.lo) (I.im.hi - ic I.im)
  let M : ℤ := max dx dy
  have hx : (toPB I).x = ic I.re := rfl
  have hy : (toPB I).y = ic I.im := rfl
  have hxre : (z - bpt (toPB I)).re = z.re - m2r (toPB I).x := by
    simp only [bpt, m2r, Complex.sub_re, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    simp
    field_simp
  have hxim : (z - bpt (toPB I)).im = z.im - m2r (toPB I).y := by
    simp only [bpt, m2r, Complex.sub_im, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    simp
    field_simp
  -- one coordinate at a time: the centre lies in the interval, `dx`, `dy` are the half-widths
  have hre : |z.re - m2r (toPB I).x| ≤ m2r dx := by
    have h1 : z.re - m2r (toPB I).x ≤ m2r dx := by
      calc z.re - m2r (toPB I).x ≤ m2r I.re.hi - m2r (ic I.re) := by
            rw [hx]; linarith
        _ = m2r (I.re.hi - ic I.re) := by rw [m2r_sub]
        _ ≤ m2r dx := m2r_le (le_max_right _ _)
    have h2 : -(z.re - m2r (toPB I).x) ≤ m2r dx := by
      rw [hx]
      calc -(z.re - m2r (ic I.re)) = m2r (ic I.re) - z.re := by ring
        _ ≤ m2r (ic I.re) - m2r I.re.lo := by linarith
        _ = m2r (ic I.re - I.re.lo) := by rw [m2r_sub]
        _ ≤ m2r dx := m2r_le (le_max_left _ _)
    exact abs_le.mpr ⟨by linarith, h1⟩
  have him : |z.im - m2r (toPB I).y| ≤ m2r dy := by
    have h1 : z.im - m2r (toPB I).y ≤ m2r dy := by
      calc z.im - m2r (toPB I).y ≤ m2r I.im.hi - m2r (ic I.im) := by
            rw [hy]; linarith
        _ = m2r (I.im.hi - ic I.im) := by rw [m2r_sub]
        _ ≤ m2r dy := m2r_le (le_max_right _ _)
    have h2 : -(z.im - m2r (toPB I).y) ≤ m2r dy := by
      rw [hy]
      calc -(z.im - m2r (ic I.im)) = m2r (ic I.im) - z.im := by ring
        _ ≤ m2r (ic I.im) - m2r I.im.lo := by linarith
        _ = m2r (ic I.im - I.im.lo) := by rw [m2r_sub]
        _ ≤ m2r dy := m2r_le (le_max_left _ _)
    exact abs_le.mpr ⟨by linarith, h1⟩
  have hdx0 : (0 : ℝ) ≤ m2r dx := le_trans (abs_nonneg _) hre
  have hdy0 : (0 : ℝ) ≤ m2r dy := le_trans (abs_nonneg _) him
  have hM0 : (0 : ℝ) ≤ m2r M := le_trans hdx0 (m2r_le (le_max_left _ _))
  -- the sum of squares of the two coordinates is at most `2 · (m2r M)²`
  have hsq : (z - bpt (toPB I)).re ^ 2 + (z - bpt (toPB I)).im ^ 2 ≤ 2 * (m2r M) ^ 2 := by
    rw [hxre, hxim]
    have ha : (z.re - m2r (toPB I).x) ^ 2 ≤ (m2r M) ^ 2 := by
      have h := abs_le.mp hre
      have h2 : (m2r dx) ^ 2 ≤ (m2r M) ^ 2 :=
        pow_le_pow_left₀ hdx0 (m2r_le (le_max_left _ _)) 2
      nlinarith [h.1, h.2, hdx0]
    have hb : (z.im - m2r (toPB I).y) ^ 2 ≤ (m2r M) ^ 2 := by
      have h := abs_le.mp him
      have h2 : (m2r dy) ^ 2 ≤ (m2r M) ^ 2 :=
        pow_le_pow_left₀ hdy0 (m2r_le (le_max_right _ _)) 2
      nlinarith [h.1, h.2, hdy0]
    linarith
  have hnorm : ‖z - bpt (toPB I)‖ ≤ (3 / 2) * m2r M := by
    have h1 : ‖z - bpt (toPB I)‖
        = Real.sqrt ((z - bpt (toPB I)).re ^ 2 + (z - bpt (toPB I)).im ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_apply]
      ring_nf
    rw [h1]
    have h3 : Real.sqrt (2 * (m2r M) ^ 2) = Real.sqrt 2 * m2r M := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hM0]
    calc Real.sqrt ((z - bpt (toPB I)).re ^ 2 + (z - bpt (toPB I)).im ^ 2)
        ≤ Real.sqrt (2 * (m2r M) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt 2 * m2r M := h3
      _ ≤ (3 / 2) * m2r M := by
          have := Real.sqrt_two_lt_three_halves
          nlinarith
  -- the radius `(3·M)/2 + 4` (mantissa) dominates `(3/2)·m2r M`
  have he : (3 / 2 : ℝ) * m2r M ≤ m2r (toPB I).e := by
    show (3 / 2 : ℝ) * m2r M ≤ m2r ((3 * M) / 2 + 4)
    have hq : (3 * M : ℤ) ≤ 2 * ((3 * M) / 2) + 1 := by
      have h := Int.ediv_mul_add_emod (3 * M) 2
      have h1 : 0 ≤ (3 * M) % 2 := Int.emod_nonneg _ (by norm_num)
      have h2 : (3 * M) % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
      linarith
    have hqR : (3 * M : ℝ) ≤ 2 * (((3 * M) / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast hq
    rw [m2r, m2r]
    push_cast
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right SC_posR]
    linarith
  linarith

/-! ## The target -/

theorem BoxSide : (∀ (I : Work.CNum.Cpx) (z : ℂ), I.Mem z → ‖z - Work.CNum.bpt (Work.CNum.toPB I)‖ ≤ Work.ANum.m2r (Work.CNum.toPB I).e) ∧ (∀ j : ℕ, j ≤ 1024 → Work.CNum.BoxOK (Work.CNum.ptOf j)) ∧ Work.CNum.BoxOK Work.CNum.ptCuspA ∧ Work.CNum.BoxOK Work.CNum.ptCuspB := by
  exact ⟨boxSide_pbBound, boxSide_ptOf, boxSide_cuspA, boxSide_cuspB⟩

end Work.CNum
