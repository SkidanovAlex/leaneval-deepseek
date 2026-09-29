import Mathlib
import Submission.Work.ANum.isqrtSpec

/-! # A fixed-point interval library for the certified numerics of Theorem A

Real numbers are represented by `ℤ` mantissas at the fixed scale `SC = 2^30`; an interval is a pair
of mantissas.  All operations are exact integer computations together with outward rounding, so the
whole certificate is checked by the kernel with plain `ℤ` evaluation.

This module is shared with `Work.CNum` (Theorem C).

All soundness statements have the shape `x ∈ I → y ∈ J → f x y ∈ I.op J`. -/

namespace Work.ANum

noncomputable section

/-- The fixed-point scale `2^30`. -/
def SC : ℤ := 2 ^ 30

lemma SC_pos : 0 < SC := by norm_num [SC]
lemma SC_ne_zero : SC ≠ 0 := ne_of_gt SC_pos
lemma SC_posR : (0 : ℝ) < (SC : ℝ) := by exact_mod_cast SC_pos

/-- The real value of a mantissa. -/
abbrev m2r (n : ℤ) : ℝ := (n : ℝ) / (SC : ℝ)

lemma m2r_add (a b : ℤ) : m2r (a + b) = m2r a + m2r b := by
  simp only [m2r]; push_cast; ring
lemma m2r_sub (a b : ℤ) : m2r (a - b) = m2r a - m2r b := by
  simp only [m2r]; push_cast; ring
lemma m2r_neg (a : ℤ) : m2r (-a) = -m2r a := by
  simp only [m2r]; push_cast; ring
lemma m2r_le {a b : ℤ} (h : a ≤ b) : m2r a ≤ m2r b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) SC_posR.le
lemma m2r_lt {a b : ℤ} (h : a < b) : m2r a < m2r b :=
  div_lt_div_of_pos_right (by exact_mod_cast h) SC_posR
lemma m2r_zero : m2r 0 = 0 := by simp [m2r]
lemma m2r_two : m2r (2 * SC) = 2 := by
  simp only [m2r]
  rw [show ((2 * SC : ℤ) : ℝ) = 2 * (SC : ℝ) by push_cast; ring,
    mul_div_cancel_right₀ 2 (ne_of_gt SC_posR)]

lemma m2r_mul (a b : ℤ) : m2r (a * b) = SC * (m2r a * m2r b) := by
  simp only [m2r]; push_cast; field_simp

lemma m2r_SC : m2r SC = 1 := by
  simp only [m2r]; exact div_self (ne_of_gt SC_posR)

/-- A fixed-point interval `[lo/SC, hi/SC]`. -/
structure Iv where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

namespace Iv

/-- Membership of a real number in an interval. -/
def Mem (I : Iv) (x : ℝ) : Prop := m2r I.lo ≤ x ∧ x ≤ m2r I.hi

theorem Mem.mono {I J : Iv} {x : ℝ} (h : I.Mem x) (hlo : J.lo ≤ I.lo) (hhi : I.hi ≤ J.hi) :
    J.Mem x := ⟨le_trans (m2r_le hlo) h.1, le_trans h.2 (m2r_le hhi)⟩

/-- The point interval `n/SC`. -/
def pt (n : ℤ) : Iv := ⟨n, n⟩
theorem mem_pt (n : ℤ) : (pt n).Mem (m2r n) := ⟨le_rfl, le_rfl⟩

/-! ## Rounding of products -/

/-- `⌊a * b / SC⌋`. -/
def mulLo (a b : ℤ) : ℤ := Int.ediv (a * b) SC
/-- `⌈a * b / SC⌉`. -/
def mulHi (a b : ℤ) : ℤ := -Int.ediv (-(a * b)) SC

theorem mulLo_le (a b : ℤ) : m2r (mulLo a b) ≤ m2r a * m2r b := by
  have h : (mulLo a b * SC : ℤ) ≤ a * b := by
    simp only [mulLo]; exact Int.ediv_mul_le (a * b) SC_ne_zero
  have h1 : m2r (mulLo a b * SC) ≤ m2r (a * b) := m2r_le h
  simp only [m2r_mul, m2r_SC, mul_one] at h1
  exact le_of_mul_le_mul_left h1 SC_posR

theorem le_mulHi (a b : ℤ) : m2r a * m2r b ≤ m2r (mulHi a b) := by
  have h : (Int.ediv (-(a * b)) SC * SC : ℤ) ≤ -(a * b) :=
    Int.ediv_mul_le (-(a * b)) SC_ne_zero
  have h1 : m2r (Int.ediv (-(a * b)) SC * SC) ≤ m2r (-(a * b)) := m2r_le h
  simp only [m2r_mul, m2r_SC, mul_one, m2r_neg] at h1
  have h1b : (SC : ℝ) * m2r (Int.ediv (-(a * b)) SC) ≤ (SC : ℝ) * (-(m2r a * m2r b)) := by
    rw [show -((SC:ℝ) * (m2r a * m2r b)) = (SC:ℝ) * (-(m2r a * m2r b)) by ring] at h1
    exact h1
  have h1'' := le_of_mul_le_mul_left h1b SC_posR
  clear h1 h1b
  have h2 : m2r (mulHi a b) = -m2r (Int.ediv (-(a * b)) SC) := by
    simp only [mulHi, m2r]; push_cast; ring
  rw [h2]; linarith

/-! ## Operations -/

/-- Addition. -/
def add (I J : Iv) : Iv := ⟨I.lo + J.lo, I.hi + J.hi⟩
theorem mem_add {I J : Iv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (add I J).Mem (x + y) := by
  constructor
  · show m2r (I.lo + J.lo) ≤ x + y
    rw [m2r_add]; linarith [hx.1, hy.1]
  · show x + y ≤ m2r (I.hi + J.hi)
    rw [m2r_add]; linarith [hx.2, hy.2]

/-- Negation. -/
def neg (I : Iv) : Iv := ⟨-I.hi, -I.lo⟩
theorem mem_neg {I : Iv} {x : ℝ} (hx : I.Mem x) : (neg I).Mem (-x) := by
  constructor
  · show m2r (-I.hi) ≤ -x
    rw [m2r_neg]; linarith [hx.2]
  · show -x ≤ m2r (-I.lo)
    rw [m2r_neg]; linarith [hx.1]

/-- Subtraction. -/
def sub (I J : Iv) : Iv := add I (neg J)
theorem mem_sub {I J : Iv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (sub I J).Mem (x - y) := by
  have := mem_add hx (mem_neg hy); simpa [sub, sub_eq_add_neg] using this

/-- Square, with outward rounding. -/
def sq (I : Iv) : Iv :=
  if I.lo ≤ 0 ∧ 0 ≤ I.hi then ⟨0, max (mulHi I.lo I.lo) (mulHi I.hi I.hi)⟩
  else ⟨min (mulLo I.lo I.lo) (mulLo I.hi I.hi), max (mulHi I.lo I.lo) (mulHi I.hi I.hi)⟩

theorem m2r_min (a b : ℤ) : m2r (min a b) = min (m2r a) (m2r b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (m2r_le h)]
  · rw [min_eq_right h, min_eq_right (m2r_le h)]
theorem m2r_max (a b : ℤ) : m2r (max a b) = max (m2r a) (m2r b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (m2r_le h)]
  · rw [max_eq_left h, max_eq_left (m2r_le h)]

theorem mem_sq {I : Iv} {x : ℝ} (hx : I.Mem x) : (sq I).Mem (x * x) := by
  obtain ⟨h1, h2⟩ := hx
  have hll := mulLo_le I.lo I.lo
  have hhh := le_mulHi I.hi I.hi
  have hlh := le_mulHi I.lo I.lo
  have hhl := mulLo_le I.hi I.hi
  by_cases hc : I.lo ≤ 0 ∧ 0 ≤ I.hi
  · simp only [sq, if_pos hc]
    constructor
    · simp only [m2r_zero]
      nlinarith [sq_nonneg x]
    · rw [m2r_max]
      rcases le_total 0 x with hx0 | hx0
      · have : x * x ≤ m2r I.hi * m2r I.hi := by nlinarith [h1, h2, hx0]
        exact le_trans (le_trans this hhh) (le_max_right _ _)
      · have : x * x ≤ m2r I.lo * m2r I.lo := by nlinarith [h1, h2, hx0]
        exact le_trans (le_trans this hlh) (le_max_left _ _)
  · have hcn : ¬(I.lo ≤ 0 ∧ 0 ≤ I.hi) := hc
    rw [not_and_or] at hc
    simp only [sq, if_neg hcn]
    rcases hc with hl | hu
    · -- I.lo > 0
      have hl' : 0 < I.lo := not_le.mp hl
      have hx0 : 0 < m2r I.lo := by
        have := m2r_lt hl'; rwa [m2r_zero] at this
      have hxpos : 0 ≤ x := le_trans hx0.le h1
      constructor
      · rw [m2r_min]
        have : m2r I.lo * m2r I.lo ≤ x * x := by nlinarith [h1, hx0, hxpos]
        exact le_trans (le_trans (min_le_left _ _) hll) this
      · rw [m2r_max]
        have : x * x ≤ m2r I.hi * m2r I.hi := by nlinarith [h2, hxpos]
        exact le_trans (le_trans this hhh) (le_max_right _ _)
    · -- I.hi < 0
      have hu' : I.hi < 0 := not_le.mp hu
      have hx1 : m2r I.hi < 0 := by
        have := m2r_lt hu'; rwa [m2r_zero] at this
      have hxneg : x ≤ 0 := le_trans h2 hx1.le
      constructor
      · rw [m2r_min]
        have : m2r I.hi * m2r I.hi ≤ x * x := by nlinarith [h2, hx1, hxneg]
        exact le_trans (le_trans (min_le_right _ _) hhl) this
      · rw [m2r_max]
        have : x * x ≤ m2r I.lo * m2r I.lo := by nlinarith [h1, hxneg]
        exact le_trans (le_trans this hlh) (le_max_left _ _)

/-- Multiplication by `1/2`. -/
def scale2 (I : Iv) : Iv := ⟨mulLo I.lo (SC / 2), mulHi I.hi (SC / 2)⟩

theorem m2r_SC_half : m2r (SC / 2) = 1 / 2 := by
  have : (SC / 2 : ℤ) = 2 ^ 29 := by norm_num [SC]
  rw [this]
  simp only [m2r, SC]
  push_cast
  norm_num

theorem mem_scale2 {I : Iv} {x : ℝ} (hx : I.Mem x) : (scale2 I).Mem (x / 2) := by
  constructor
  · show m2r (mulLo I.lo (SC / 2)) ≤ x / 2
    have := mulLo_le I.lo (SC / 2)
    rw [m2r_SC_half] at this
    have h2 := mul_le_mul_of_nonneg_right hx.1 (by norm_num : (0:ℝ) ≤ 1/2)
    linarith
  · show x / 2 ≤ m2r (mulHi I.hi (SC / 2))
    have := le_mulHi I.hi (SC / 2)
    rw [m2r_SC_half] at this
    have h2 := mul_le_mul_of_nonneg_right hx.2 (by norm_num : (0:ℝ) ≤ 1/2)
    linarith

/-- **Corner bound for a bilinear product**: if `x ∈ [a₁,a₂]` and `y ∈ [b₁,b₂]` then `x*y` lies
between the minimum and the maximum of the four corner products.  This is the classical
"interval multiplication" rule and is used below to give `Iv.mul` the *tightest* sound enclosure
(the older centred-square formula was sound but lost a factor ~4 in width at every product, which
compounds catastrophically along the five-stage contour). -/
lemma mul_corners {a₁ a₂ b₁ b₂ x y : ℝ} (hx1 : a₁ ≤ x) (hx2 : x ≤ a₂)
    (hy1 : b₁ ≤ y) (hy2 : y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y ∧
      x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := by
  constructor
  · rcases le_total 0 y with hy | hy
    · rcases le_total 0 a₁ with ha | ha
      · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
          (le_trans (mul_le_mul_of_nonneg_left hy1 ha) (mul_le_mul_of_nonneg_right hx1 hy))
      · exact le_trans (le_trans (min_le_left _ _) (min_le_right _ _))
          (le_trans (mul_le_mul_of_nonpos_left hy2 ha) (mul_le_mul_of_nonneg_right hx1 hy))
    · rcases le_total 0 a₂ with ha | ha
      · exact le_trans (le_trans (min_le_right _ _) (min_le_left _ _))
          (le_trans (mul_le_mul_of_nonneg_left hy1 ha) (mul_le_mul_of_nonpos_right hx2 hy))
      · exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
          (le_trans (mul_le_mul_of_nonpos_left hy2 ha) (mul_le_mul_of_nonpos_right hx2 hy))
  · rcases le_total 0 y with hy | hy
    · rcases le_total 0 a₂ with ha | ha
      · exact le_trans (le_trans (mul_le_mul_of_nonneg_right hx2 hy) (mul_le_mul_of_nonneg_left hy2 ha))
          (le_trans (le_max_right _ _) (le_max_right _ _))
      · exact le_trans (le_trans (mul_le_mul_of_nonneg_right hx2 hy) (mul_le_mul_of_nonpos_left hy1 ha))
          (le_trans (le_max_left _ _) (le_max_right _ _))
    · rcases le_total 0 a₁ with ha | ha
      · exact le_trans (le_trans (mul_le_mul_of_nonpos_right hx1 hy) (mul_le_mul_of_nonneg_left hy2 ha))
          (le_trans (le_max_right _ _) (le_max_left _ _))
      · exact le_trans (le_trans (mul_le_mul_of_nonpos_right hx1 hy) (mul_le_mul_of_nonpos_left hy1 ha))
          (le_trans (le_max_left _ _) (le_max_left _ _))

/-- Multiplication of intervals, by the four-corner rule (the tightest sound enclosure). -/
def mul (I J : Iv) : Iv :=
  ⟨min (min (mulLo I.lo J.lo) (mulLo I.lo J.hi)) (min (mulLo I.hi J.lo) (mulLo I.hi J.hi)),
   max (max (mulHi I.lo J.lo) (mulHi I.lo J.hi)) (max (mulHi I.hi J.lo) (mulHi I.hi J.hi))⟩

theorem mem_mul {I J : Iv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (mul I J).Mem (x * y) := by
  have key := mul_corners (a₁ := m2r I.lo) (a₂ := m2r I.hi) (b₁ := m2r J.lo) (b₂ := m2r J.hi)
    hx.1 hx.2 hy.1 hy.2
  constructor
  · show m2r (min (min (mulLo I.lo J.lo) (mulLo I.lo J.hi))
        (min (mulLo I.hi J.lo) (mulLo I.hi J.hi))) ≤ x * y
    rw [m2r_min, m2r_min, m2r_min]
    exact le_trans (min_le_min (min_le_min (mulLo_le I.lo J.lo) (mulLo_le I.lo J.hi))
      (min_le_min (mulLo_le I.hi J.lo) (mulLo_le I.hi J.hi))) key.1
  · show x * y ≤ m2r (max (max (mulHi I.lo J.lo) (mulHi I.lo J.hi))
        (max (mulHi I.hi J.lo) (mulHi I.hi J.hi)))
    rw [m2r_max, m2r_max, m2r_max]
    exact le_trans key.2 (max_le_max (max_le_max (le_mulHi I.lo J.lo) (le_mulHi I.lo J.hi))
      (max_le_max (le_mulHi I.hi J.lo) (le_mulHi I.hi J.hi)))

/-! ## Reciprocal and square root -/

/-- Reciprocal of a positive interval. -/
def invPos (I : Iv) : Iv := ⟨Int.ediv (SC * SC) I.hi, -Int.ediv (-(SC * SC)) I.lo⟩

theorem m2r_SC_sq : m2r (SC * SC) = SC := by
  rw [m2r_mul, m2r_SC, mul_one, mul_one]

theorem m2r_mul_SC (a : ℤ) : m2r a * (SC : ℝ) = (a : ℝ) := by
  simp only [m2r]
  rw [div_mul_cancel₀]
  exact ne_of_gt SC_posR

theorem mem_invPos {I : Iv} {x : ℝ} (hx : I.Mem x) (hlo : 0 < m2r I.lo) :
    (invPos I).Mem (1 / x) := by
  have hhi : 0 < m2r I.hi := lt_of_lt_of_le hlo (le_trans hx.1 hx.2)
  have hloR : 0 < (I.lo : ℝ) := by
    have h := mul_lt_mul_of_pos_right hlo SC_posR
    rw [m2r_mul_SC] at h
    simpa using h
  have hhiR : 0 < (I.hi : ℝ) := by
    have h := mul_lt_mul_of_pos_right hhi SC_posR
    rw [m2r_mul_SC] at h
    simpa using h
  have hloZ : 0 < I.lo := by exact_mod_cast hloR
  have hhiZ : 0 < I.hi := by exact_mod_cast hhiR
  have h1 : m2r (Int.ediv (SC * SC) I.hi) * m2r I.hi ≤ 1 := by
    have h := Int.ediv_mul_le (SC * SC) (ne_of_gt hhiZ)
    have h5 : m2r (Int.ediv (SC * SC) I.hi * I.hi) ≤ m2r (SC * SC) := m2r_le h
    simp only [m2r_mul, m2r_SC, mul_one] at h5
    have h6 : (SC : ℝ) * (m2r (Int.ediv (SC * SC) I.hi) * m2r I.hi) ≤ (SC : ℝ) * 1 := by
      rw [mul_one]; exact h5
    exact le_of_mul_le_mul_left h6 SC_posR
  have h4 : 1 ≤ m2r (-Int.ediv (-(SC * SC)) I.lo) * m2r I.lo := by
    have h := Int.ediv_mul_le (-(SC * SC)) (ne_of_gt hloZ)
    have h5 : m2r (Int.ediv (-(SC * SC)) I.lo * I.lo) ≤ m2r (-(SC * SC)) := m2r_le h
    simp only [m2r_mul, m2r_SC, mul_one, m2r_SC_sq, m2r_neg] at h5
    have h6 : (SC : ℝ) * (m2r (Int.ediv (-(SC * SC)) I.lo) * m2r I.lo) ≤ (SC : ℝ) * (-1) := by
      rw [mul_neg, mul_one]; exact h5
    have h7 := le_of_mul_le_mul_left h6 SC_posR
    have h8 : m2r (-Int.ediv (-(SC * SC)) I.lo) * m2r I.lo
        = -(m2r (Int.ediv (-(SC * SC)) I.lo) * m2r I.lo) := by
      rw [m2r_neg]; ring
    rw [h8]; linarith [h7]
  constructor
  · have h5 : m2r (Int.ediv (SC * SC) I.hi) ≤ 1 / m2r I.hi := by
      rw [le_div_iff₀ hhi]; exact h1
    refine le_trans h5 ?_
    rw [div_le_div_iff₀ hhi (lt_of_lt_of_le hlo hx.1)]
    linarith [hx.2, hhi, hlo, hx.1]
  · have h5 : 1 / m2r I.lo ≤ m2r (-Int.ediv (-(SC * SC)) I.lo) := by
      rw [div_le_iff₀ hlo]; exact h4
    refine le_trans ?_ h5
    rw [div_le_div_iff₀ (lt_of_lt_of_le hlo hx.1) hlo]
    linarith [hx.1, hlo]

/-! ## Clamping to nonnegativity -/

/-- Clamp an interval to `[0, ∞)` (for arguments known to be nonnegative semantically, keeping the
operation a cheap integer computation). -/
def nonneg (I : Iv) : Iv := ⟨max I.lo 0, I.hi⟩

theorem mem_nonneg {I : Iv} {x : ℝ} (hx : I.Mem x) (h : 0 ≤ x) : (nonneg I).Mem x := by
  constructor
  · show m2r (max I.lo 0) ≤ x
    rw [m2r_max, m2r_zero]
    exact max_le hx.1 h
  · exact hx.2

theorem nonneg_lo_nonneg (I : Iv) : 0 ≤ m2r (nonneg I).lo := by
  show 0 ≤ m2r (max I.lo 0)
  rw [m2r_max, m2r_zero]
  exact le_max_right _ _

/-! ## Square root -/

/-- Square root of a nonnegative interval. -/
def sqrt (I : Iv) : Iv :=
  ⟨(isqrt ((I.lo * SC).toNat) : ℤ), ((isqrt ((I.hi * SC).toNat) : ℤ) + 1)⟩

theorem mem_sqrt {I : Iv} {x : ℝ} (hx : I.Mem x) (hlo : 0 ≤ m2r I.lo) (hhi : 0 ≤ m2r I.hi) :
    (sqrt I).Mem (Real.sqrt x) := by
  have hloR : 0 ≤ m2r I.lo := hlo
  have hloZ : 0 ≤ I.lo := by
    by_contra h
    rw [not_le] at h
    have : m2r I.lo < 0 := by
      have := m2r_lt h; rwa [m2r_zero] at this
    linarith
  have hhiZ : 0 ≤ I.hi := by
    by_contra h
    rw [not_le] at h
    have : m2r I.hi < 0 := by
      have := m2r_lt h; rwa [m2r_zero] at this
    linarith
  have key : ∀ a : ℤ, 0 ≤ a →
      (m2r ((isqrt ((a * SC).toNat) : ℤ))) * (m2r ((isqrt ((a * SC).toNat) : ℤ))) ≤ m2r a := by
    intro a ha
    have h0 : isqrt ((a * SC).toNat) ^ 2 ≤ (a * SC).toNat := isqrt_le' _
    have h1n : (((isqrt ((a * SC).toNat) : ℕ) : ℤ) * ((isqrt ((a * SC).toNat) : ℕ) : ℤ))
        ≤ ((a * SC).toNat : ℤ) := by
      have hh : (((isqrt ((a * SC).toNat) : ℕ) : ℤ) ^ 2) ≤ ((a * SC).toNat : ℤ) := by
        exact_mod_cast h0
      rwa [pow_two] at hh
    have h1 : (((isqrt ((a * SC).toNat) : ℤ)) * ((isqrt ((a * SC).toNat) : ℤ))) ≤ a * SC := by
      simpa only [Int.toNat_of_nonneg (by exact mul_nonneg ha (le_of_lt SC_pos))] using h1n
    have h3 : m2r (((isqrt ((a * SC).toNat) : ℤ)) * ((isqrt ((a * SC).toNat) : ℤ)))
        ≤ m2r (a * SC) := m2r_le h1
    have e1 : m2r (((isqrt ((a * SC).toNat) : ℤ)) * ((isqrt ((a * SC).toNat) : ℤ)))
        = SC * (m2r ((isqrt ((a * SC).toNat) : ℤ)) * m2r ((isqrt ((a * SC).toNat) : ℤ))) := by
      rw [m2r_mul]
    have e2 : m2r (a * SC) = SC * m2r a := by
      rw [m2r_mul, m2r_SC, mul_one]
    rw [e1, e2] at h3
    exact le_of_mul_le_mul_left h3 SC_posR
  have key2 : ∀ a : ℤ, 0 ≤ a →
      m2r a < (m2r (((isqrt ((a * SC).toNat) : ℤ) + 1))) *
        (m2r (((isqrt ((a * SC).toNat) : ℤ) + 1))) := by
    intro a ha
    have h0 : (a * SC).toNat < (isqrt ((a * SC).toNat) + 1) ^ 2 := lt_succ_isqrt' _
    have h1n : ((a * SC).toNat : ℤ)
        < ((((isqrt ((a * SC).toNat) : ℕ) : ℤ) + 1) * (((isqrt ((a * SC).toNat) : ℕ) : ℤ) + 1)) := by
      have hh : ((a * SC).toNat : ℤ) < (((isqrt ((a * SC).toNat) : ℕ) : ℤ) + 1) ^ 2 := by
        exact_mod_cast h0
      rwa [pow_two] at hh
    have h1 : a * SC < (((isqrt ((a * SC).toNat) : ℤ)) + 1) * (((isqrt ((a * SC).toNat) : ℤ)) + 1) := by
      simpa only [Int.toNat_of_nonneg (by exact mul_nonneg ha (le_of_lt SC_pos))] using h1n
    have h3 : m2r (a * SC)
        < m2r ((((isqrt ((a * SC).toNat) : ℤ)) + 1) * (((isqrt ((a * SC).toNat) : ℤ)) + 1)) := m2r_lt h1
    have e1 : m2r ((((isqrt ((a * SC).toNat) : ℤ)) + 1) * (((isqrt ((a * SC).toNat) : ℤ)) + 1))
        = SC * (m2r (((isqrt ((a * SC).toNat) : ℤ)) + 1) * m2r (((isqrt ((a * SC).toNat) : ℤ)) + 1)) := by
      rw [m2r_mul]
    have e2 : m2r (a * SC) = SC * m2r a := by
      rw [m2r_mul, m2r_SC, mul_one]
    rw [e1, e2] at h3
    exact lt_of_mul_lt_mul_left h3 SC_posR.le
  constructor
  · have h6 : m2r ((isqrt ((I.lo * SC).toNat) : ℤ)) ≤ Real.sqrt (m2r I.lo) := by
      have hk0 : 0 ≤ m2r ((isqrt ((I.lo * SC).toNat) : ℤ)) := by
        simp only [m2r]
        exact div_nonneg (by exact_mod_cast Nat.zero_le _) SC_posR.le
      have hsq : (Real.sqrt (m2r I.lo)) ^ 2 = m2r I.lo := Real.sq_sqrt hloR
      have hle' : (m2r ((isqrt ((I.lo * SC).toNat) : ℤ))) ^ 2 ≤ m2r I.lo := by
        simpa [pow_two] using key I.lo hloZ
      nlinarith [hsq, hle', hk0, Real.sqrt_nonneg (m2r I.lo)]
    exact le_trans h6 (Real.sqrt_le_sqrt hx.1)
  · have h6 : Real.sqrt x ≤ Real.sqrt (m2r I.hi) := Real.sqrt_le_sqrt hx.2
    have h7 : Real.sqrt (m2r I.hi) < m2r (((isqrt ((I.hi * SC).toNat) : ℤ)) + 1) := by
      have hK0 : 0 ≤ m2r (((isqrt ((I.hi * SC).toNat) : ℤ)) + 1) := by
        simp only [m2r]
        exact div_nonneg (by positivity) SC_posR.le
      have hsq : (Real.sqrt (m2r I.hi)) ^ 2 = m2r I.hi :=
        Real.sq_sqrt (le_trans hloR (le_trans hx.1 hx.2))
      have hlt : m2r I.hi < (m2r (((isqrt ((I.hi * SC).toNat) : ℤ)) + 1)) ^ 2 := by
        simpa [pow_two] using key2 I.hi hhiZ
      nlinarith [hsq, hlt, hK0, Real.sqrt_nonneg (m2r I.hi)]
    exact le_of_lt (lt_of_le_of_lt h6 h7)

end Iv

end

end Work.ANum
