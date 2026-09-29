import Mathlib
import Submission.Work.ANum.CDisc

/-! # The principal square root of a complex interval (rectangle)

`CD.sqrt D` encloses `Complex.sqrt z` for every `z ∈ D`.  The construction uses the closed form

  `√z = √((‖z‖ + z.re)/2) + (if 0 ≤ z.im then 1 else -1) · √((‖z‖ - z.re)/2) · I`
  (`Complex.sqrt_eq_real_add_ite`),

so only real interval operations are needed: the modulus `‖z‖` is enclosed by
`Iv.sqrt (D.re.sq + D.im.sq)`, the two arguments `(‖z‖ ± z.re)/2` are clamped to be nonnegative and
square-rooted (`Iv.sqrt`), and the imaginary part is enclosed by the symmetric hull
`[-q.hi, q.hi]` of `|Im √z| ≤ q` (valid whether or not the rectangle crosses the real axis).

The mantissa-level side conditions (`0 ≤ m2r …hi` for the two clamped arguments and for the modulus
interval) are the numerically checked hypothesis that the rectangle avoids the branch cut; they are
discharged per certificate by the generator.

This is the last missing ingredient of the per-arc contour evaluation (`ANum/STATUS.md`). -/

namespace Work.ANum

noncomputable section

open Complex

namespace CD

/-- The argument `(‖z‖ + z.re)/2` of the real part of `√z`, clamped to be nonnegative. -/
def sqrtArgRe (D : CD) : Iv := Iv.nonneg (Iv.scale2 (((D.re.sq.add D.im.sq).sqrt).add D.re))

/-- The argument `(‖z‖ - z.re)/2` of `|Im √z|`, clamped to be nonnegative. -/
def sqrtArgIm (D : CD) : Iv := Iv.nonneg (Iv.scale2 (((D.re.sq.add D.im.sq).sqrt).sub D.re))

/-- An enclosure of `Re √z = √((‖z‖ + z.re)/2)`. -/
def sqrtRe (D : CD) : Iv := (sqrtArgRe D).sqrt

theorem m2r_natAbs (a : ℤ) : m2r a.natAbs = |m2r a| := by
  rcases lt_trichotomy a 0 with h | h | h
  · have h1 : a.natAbs = -a := by rw [← Int.natAbs_neg a, Int.natAbs_of_nonneg (by omega)]
    have hx : m2r a < 0 := by
      rw [m2r]
      exact div_neg_of_neg_of_pos (by exact_mod_cast h) SC_posR
    rw [h1, m2r_neg]
    exact (abs_of_neg hx).symm
  · subst h
    simp [m2r]
  · have hx : 0 ≤ m2r a := by
      rw [m2r]
      exact le_of_lt (div_pos (by exact_mod_cast h) SC_posR)
    rw [Int.natAbs_of_nonneg h.le]
    exact (abs_of_nonneg hx).symm

theorem abs_le_maxAbs {I : Iv} {x : ℝ} (h : I.Mem x) :
    |x| ≤ m2r (max I.lo.natAbs I.hi.natAbs) := by
  have h1 : |x| ≤ max |m2r I.lo| |m2r I.hi| := by
    rcases le_total 0 x with hx | hx
    · have h2 : x ≤ |m2r I.hi| := le_trans h.2 (le_abs_self _)
      rw [abs_of_nonneg hx]
      exact le_trans h2 (le_max_right _ _)
    · have hlo : m2r I.lo ≤ 0 := le_trans h.1 hx
      have h2 : |x| ≤ |m2r I.lo| := by
        rw [abs_of_nonpos hx, abs_of_nonpos hlo]
        linarith [h.1]
      exact le_trans h2 (le_max_left _ _)
  calc |x| ≤ max |m2r I.lo| |m2r I.hi| := h1
    _ = m2r (max I.lo.natAbs I.hi.natAbs) := by rw [Iv.m2r_max, m2r_natAbs, m2r_natAbs]

/-- **`⌈a/b⌉ ≥ a/b`** at mantissa level: `m2r a / m2r b ≤ m2r (⌈a·SC/b⌉)` for `b > 0`. -/
theorem le_ceilDiv (a b : ℤ) (hb : 0 < b) :
    m2r a / m2r b ≤ m2r (-Int.ediv (-(a * SC)) b) := by
  have h1 : Int.ediv (-(a * SC)) b * b ≤ -(a * SC) := Int.ediv_mul_le _ (ne_of_gt hb)
  have h2 : (a * SC : ℤ) ≤ (-Int.ediv (-(a * SC)) b) * b := by
    have := neg_le_neg h1; push_cast at this ⊢
    linarith [this]
  have h3 : m2r (a * SC) ≤ m2r ((-Int.ediv (-(a * SC)) b) * b) := m2r_le h2
  rw [m2r_mul, m2r_mul, m2r_SC, mul_one] at h3
  have hbR : 0 < m2r b := by
    simp only [m2r]; exact div_pos (by exact_mod_cast hb) SC_posR
  have h4 : m2r a ≤ m2r (-Int.ediv (-(a * SC)) b) * m2r b :=
    le_of_mul_le_mul_left (by linarith [h3]) SC_posR
  rw [div_le_iff₀ hbR]
  linarith [h4]

/-- The rationalized upper bound `|Im z|/(2 Re √z)` for `|Im √z| = √((‖z‖ - z.re)/2)`.  It is
tight exactly where the direct form loses all significance: when the radicand's imaginary part is
of the order of the rounding unit, so the difference `‖z‖ - z.re` is computed with total
cancellation. -/
def sqrtImAbsAux (D : CD) : ℤ :=
  -Int.ediv (-(max D.im.lo.natAbs D.im.hi.natAbs * SC)) (2 * (sqrtArgRe D).sqrt.lo)

/-- An enclosure of `|Im √z| = √((‖z‖ - z.re)/2)` (the *sound but lossy* direct form; see
`sqrtImAbsI` for the repaired version used by the ANum certificate). -/
def sqrtImAbs (D : CD) : Iv := (sqrtArgIm D).sqrt

/-- The repaired `|Im √z|`: the direct form, tightened by the rationalized bound
`|Im z|/(2 Re √z)` whenever the real part of the root is provably positive (decidable integer
test).  The direct form is catastrophic when the radicand is close to the real axis, because
`‖z‖ - z.re` is then a difference of nearly equal numbers. -/
def sqrtImAbsI (D : CD) : Iv :=
  if 0 < 2 * (sqrtArgRe D).sqrt.lo then
    ⟨(sqrtArgIm D).sqrt.lo, min (sqrtArgIm D).sqrt.hi (sqrtImAbsAux D)⟩
  else (sqrtArgIm D).sqrt

theorem sqrtImAbsI_lo (D : CD) : (sqrtImAbsI D).lo = (sqrtArgIm D).sqrt.lo := by
  unfold sqrtImAbsI
  split <;> rfl

def sqrtI (D : CD) : CD :=
  if 0 < D.im.lo then ⟨sqrtRe D, sqrtImAbsI D⟩
  else if D.im.hi < 0 then ⟨sqrtRe D, (sqrtImAbsI D).neg⟩
  else ⟨sqrtRe D, ⟨-(sqrtImAbsI D).hi, (sqrtImAbsI D).hi⟩⟩

theorem sqrtI_defA {D : CD} (h : 0 < D.im.lo) : sqrtI D = ⟨sqrtRe D, sqrtImAbsI D⟩ := if_pos h
theorem sqrtI_defB {D : CD} (h1 : ¬ 0 < D.im.lo) (h2 : D.im.hi < 0) :
    sqrtI D = ⟨sqrtRe D, (sqrtImAbsI D).neg⟩ := by
  simp only [sqrtI, if_neg h1, if_pos h2]
theorem sqrtI_defC {D : CD} (h1 : ¬ 0 < D.im.lo) (h2 : ¬ D.im.hi < 0) :
    sqrtI D = ⟨sqrtRe D, ⟨-(sqrtImAbsI D).hi, (sqrtImAbsI D).hi⟩⟩ := by
  simp only [sqrtI, if_neg h1, if_neg h2]

/-- The principal square root of a complex rectangle.

If the rectangle stays strictly off the real axis, the imaginary part of the root has a *known sign*
and the (tight) interval `sqrtImAbs D` is used with that sign; otherwise (the rectangle meets the
real axis) the symmetric hull `[-sqrtImAbs.hi, sqrtImAbs.hi]` is used, which is sound for every `z`.

The two tests `0 < D.im.lo` / `D.im.hi < 0` are *integer* comparisons so that the kernel can
evaluate the definition; the old unconditional symmetric hull lost a factor ~40 in width at each
square root, which compounds catastrophically along the five-stage contour. -/
def sqrt (D : CD) : CD :=
  if 0 < D.im.lo then ⟨sqrtRe D, sqrtImAbs D⟩
  else if D.im.hi < 0 then ⟨sqrtRe D, (sqrtImAbs D).neg⟩
  else ⟨sqrtRe D, ⟨-(sqrtImAbs D).hi, (sqrtImAbs D).hi⟩⟩

theorem sqrt_defA {D : CD} (h : 0 < D.im.lo) : sqrt D = ⟨sqrtRe D, sqrtImAbs D⟩ := if_pos h
theorem sqrt_defB {D : CD} (h1 : ¬ 0 < D.im.lo) (h2 : D.im.hi < 0) :
    sqrt D = ⟨sqrtRe D, (sqrtImAbs D).neg⟩ := by
  simp only [sqrt, if_neg h1, if_pos h2]
theorem sqrt_defC {D : CD} (h1 : ¬ 0 < D.im.lo) (h2 : ¬ D.im.hi < 0) :
    sqrt D = ⟨sqrtRe D, ⟨-(sqrtImAbs D).hi, (sqrtImAbs D).hi⟩⟩ := by
  simp only [sqrt, if_neg h1, if_neg h2]

theorem sqrt_arg_re_val (D : CD) : (sqrtRe D) = ((sqrtArgRe D)).sqrt := rfl

/-- **Soundness of `CD.sqrt`.**  For every `z ∈ D` in the slit plane,

`Complex.sqrt z ∈ D.sqrt`,

provided the numerical side conditions hold (the modulus interval is nonnegative and the two
clamped arguments have nonnegative *upper* ends). -/
theorem mem_sqrt {D : CD} {z : ℂ} (hz : D.Mem z) (hsp : z ∈ Complex.slitPlane)
    (hRlo : 0 ≤ m2r (D.re.sq.add D.im.sq).lo) (hRhi : 0 ≤ m2r (D.re.sq.add D.im.sq).hi)
    (hPhi : 0 ≤ m2r (sqrtArgRe D).hi) (hQhi : 0 ≤ m2r (sqrtArgIm D).hi) :
    (sqrt D).Mem (Complex.sqrt z) := by
  obtain ⟨ha, hb⟩ := hz
  -- the modulus
  have hsq : (D.re.sq.add D.im.sq).Mem (z.re * z.re + z.im * z.im) :=
    Iv.mem_add (Iv.mem_sq ha) (Iv.mem_sq hb)
  have hnorm : ‖z‖ = Real.sqrt (z.re * z.re + z.im * z.im) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; ring_nf
  have hR : ((D.re.sq.add D.im.sq).sqrt).Mem ‖z‖ := by
    rw [hnorm]
    exact Iv.mem_sqrt hsq hRlo hRhi
  have hRhi' : ‖z‖ ≤ m2r ((D.re.sq.add D.im.sq).sqrt).hi := hR.2
  -- the absolute value of the real part
  have habsre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hre_le : z.re ≤ ‖z‖ := le_trans (le_abs_self z.re) habsre
  have hne_re : -z.re ≤ ‖z‖ := by
    have := neg_le_abs z.re
    linarith [habsre]
  -- the two arguments
  have hSp : (Iv.scale2 (((D.re.sq.add D.im.sq).sqrt).add D.re)).Mem ((‖z‖ + z.re) / 2) :=
    Iv.mem_scale2 (Iv.mem_add hR ha)
  have hSp0 : 0 ≤ (‖z‖ + z.re) / 2 := by linarith
  have hP : (sqrtArgRe D).Mem ((‖z‖ + z.re) / 2) := Iv.mem_nonneg hSp hSp0
  have hPval : (sqrtRe D).Mem (Real.sqrt ((‖z‖ + z.re) / 2)) :=
    Iv.mem_sqrt hP (Iv.nonneg_lo_nonneg _) hPhi
  have hSm : (Iv.scale2 (((D.re.sq.add D.im.sq).sqrt).sub D.re)).Mem ((‖z‖ - z.re) / 2) :=
    Iv.mem_scale2 (Iv.mem_sub hR ha)
  have hSm0 : 0 ≤ (‖z‖ - z.re) / 2 := by linarith
  have hQ : (sqrtArgIm D).Mem ((‖z‖ - z.re) / 2) := Iv.mem_nonneg hSm hSm0
  have hQval : (sqrtImAbs D).Mem (Real.sqrt ((‖z‖ - z.re) / 2)) :=
    Iv.mem_sqrt hQ (Iv.nonneg_lo_nonneg _) hQhi
  -- the closed form
  have hite : (Complex.sqrt z).re = Real.sqrt ((‖z‖ + z.re) / 2) := by
    rw [Complex.sqrt_eq_real_add_ite]
    by_cases h : 0 ≤ z.im <;> simp [h, Complex.mul_I_re]
  have himte : (Complex.sqrt z).im
      = (if 0 ≤ z.im then (1 : ℝ) else -1) * Real.sqrt ((‖z‖ - z.re) / 2) := by
    rw [Complex.sqrt_eq_real_add_ite]
    by_cases h : 0 ≤ z.im <;> simp [h, Complex.mul_I_im]
  have hqnn : 0 ≤ Real.sqrt ((‖z‖ - z.re) / 2) := Real.sqrt_nonneg _
  by_cases hA : 0 < D.im.lo
  · -- the rectangle is strictly above the real axis
    obtain ⟨hAlo, _⟩ := ha
    have hApos : 0 < m2r D.im.lo := by
      have := m2r_lt hA; rwa [m2r_zero] at this
    have hzim : 0 ≤ z.im := le_trans hApos.le (by
      have := hb.1; exact this)
    rw [sqrt_defA hA]
    refine ⟨?_, ?_⟩
    · rw [hite]; exact hPval
    · rw [himte, if_pos hzim, one_mul]
      exact hQval
  · by_cases hB : D.im.hi < 0
    · -- the rectangle is strictly below the real axis
      have hBneg : m2r D.im.hi < 0 := by
        have := m2r_lt hB; rwa [m2r_zero] at this
      have hzim : ¬ (0 ≤ z.im) := by
        intro h
        have h2 : z.im ≤ m2r D.im.hi := hb.2
        linarith
      rw [sqrt_defB hA hB]
      refine ⟨?_, ?_⟩
      · rw [hite]; exact hPval
      · rw [himte, if_neg hzim]
        constructor
        · show m2r (-(sqrtImAbs D).hi) ≤ -1 * Real.sqrt ((‖z‖ - z.re) / 2)
          rw [m2r_neg, neg_mul, one_mul]; linarith [hQval.2]
        · show -1 * Real.sqrt ((‖z‖ - z.re) / 2) ≤ m2r (-(sqrtImAbs D).lo)
          rw [m2r_neg, neg_mul, one_mul]; linarith [hQval.1]
    · -- the rectangle meets the real axis: use the symmetric hull
      rw [sqrt_defC hA hB]
      refine ⟨?_, ?_⟩
      · rw [hite]; exact hPval
      · rw [himte]
        have hq : Real.sqrt ((‖z‖ - z.re) / 2) ≤ m2r (sqrtImAbs D).hi := hQval.2
        have hsign_le : (if 0 ≤ z.im then (1 : ℝ) else -1) * Real.sqrt ((‖z‖ - z.re) / 2)
            ≤ Real.sqrt ((‖z‖ - z.re) / 2) := by
          by_cases h : 0 ≤ z.im
          · simp only [h, ↓reduceIte, one_mul]; exact le_rfl
          · simp only [h, ↓reduceIte]; linarith
        have hsign_ge : -(Real.sqrt ((‖z‖ - z.re) / 2))
            ≤ (if 0 ≤ z.im then (1 : ℝ) else -1) * Real.sqrt ((‖z‖ - z.re) / 2) := by
          by_cases h : 0 ≤ z.im
          · simp only [h, ↓reduceIte, one_mul]; linarith
          · simp only [h, ↓reduceIte]; linarith
        constructor
        · show m2r (-(sqrtImAbs D).hi) ≤ _
          rw [m2r_neg]
          exact le_trans (neg_le_neg hq) hsign_ge
        · show _ ≤ m2r (sqrtImAbs D).hi
          exact le_trans hsign_le hq

end CD

end

end Work.ANum
