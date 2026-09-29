import Submission.Work.ANum.BigS

/-! # The scale-`S` interval layer: elementary facts and the soundness interfaces

`Submission.Work.ANum.BigS` defines a second copy of the interval operations with an explicit
scale `S : ℤ` (value of a mantissa `n` is `m2rS S n = n/S`).  This module adds

* the operations still missing for the contour chain (`inter`, `cst`, `ONE`),
* the elementary rewriting lemmas for `m2rS` (copies of the `Work.ANum.Ivl` lemmas with `SC → S`),
* the two `Prop`-valued interfaces `IvHiSound S` / `CDHiSound S` bundling the soundness of the
  real and complex operations, which are proved in `Submission.Work.ANum.IvHiCore` and
  `Submission.Work.ANum.CDHiCore`.
-/

namespace Work.ANum

noncomputable section

/-! ## Elementary `m2rS` lemmas -/

lemma m2rS_zero (S : ℤ) : m2rS S 0 = 0 := by simp [m2rS]

lemma m2rS_add (S : ℤ) (a b : ℤ) : m2rS S (a + b) = m2rS S a + m2rS S b := by
  simp only [m2rS]; push_cast; ring

lemma m2rS_sub (S : ℤ) (a b : ℤ) : m2rS S (a - b) = m2rS S a - m2rS S b := by
  simp only [m2rS]; push_cast; ring

lemma m2rS_neg (S : ℤ) (a : ℤ) : m2rS S (-a) = -m2rS S a := by
  simp only [m2rS]; push_cast; ring

lemma m2rS_mul (S : ℤ) (a b : ℤ) : m2rS S (a * b) = (S : ℝ) * (m2rS S a * m2rS S b) := by
  simp only [m2rS]; push_cast; field_simp

lemma m2rS_self {S : ℤ} (hS : S ≠ 0) : m2rS S S = 1 := by
  simp only [m2rS]; exact div_self (by exact_mod_cast hS)

lemma m2rS_pos {S : ℤ} (hS : 0 < S) : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS

lemma m2rS_le {S : ℤ} (hS : 0 < S) {a b : ℤ} (h : a ≤ b) : m2rS S a ≤ m2rS S b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) (m2rS_pos hS).le

lemma m2rS_lt {S : ℤ} (hS : 0 < S) {a b : ℤ} (h : a < b) : m2rS S a < m2rS S b :=
  div_lt_div_of_pos_right (by exact_mod_cast h) (m2rS_pos hS)

lemma m2rS_min {S : ℤ} (hS : 0 < S) (a b : ℤ) :
    m2rS S (min a b) = min (m2rS S a) (m2rS S b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (m2rS_le hS h)]
  · rw [min_eq_right h, min_eq_right (m2rS_le hS h)]

lemma m2rS_max {S : ℤ} (hS : 0 < S) (a b : ℤ) :
    m2rS S (max a b) = max (m2rS S a) (m2rS S b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (m2rS_le hS h)]
  · rw [max_eq_left h, max_eq_left (m2rS_le hS h)]

/-! ## The two missing operations -/

namespace IvHi

/-- Intersection of two intervals. -/
def inter (I J : Iv) : Iv := ⟨max I.lo J.lo, min I.hi J.hi⟩

end IvHi

namespace CDHi

/-- Intersection of two rectangles. -/
def inter (D E : CD) : CD := ⟨IvHi.inter D.re E.re, IvHi.inter D.im E.im⟩

/-- A real constant, as a complex rectangle. -/
def cst (I : Iv) : CD := ⟨I, IvHi.pt 0⟩

/-- The complex constant `1`, at scale `S`. -/
def ONE (S : ℤ) : CD := ⟨IvHi.pt S, IvHi.pt 0⟩

end CDHi

/-! ## The soundness interfaces -/

/-- Soundness of the scale-`S` real interval operations. -/
structure IvHiSound (S : ℤ) : Prop where
  mulLo_le : ∀ a b : ℤ, m2rS S (IvHi.mulLo S a b) ≤ m2rS S a * m2rS S b
  le_mulHi : ∀ a b : ℤ, m2rS S a * m2rS S b ≤ m2rS S (IvHi.mulHi S a b)
  mem_add : ∀ {I J : Iv} {x y : ℝ},
    IvHi.Mem S I x → IvHi.Mem S J y → IvHi.Mem S (IvHi.add I J) (x + y)
  mem_neg : ∀ {I : Iv} {x : ℝ}, IvHi.Mem S I x → IvHi.Mem S (IvHi.neg I) (-x)
  mem_sub : ∀ {I J : Iv} {x y : ℝ},
    IvHi.Mem S I x → IvHi.Mem S J y → IvHi.Mem S (IvHi.sub I J) (x - y)
  mem_sq : ∀ {I : Iv} {x : ℝ}, IvHi.Mem S I x → IvHi.Mem S (IvHi.sq S I) (x * x)
  mem_scale2 : ∀ {I : Iv} {x : ℝ}, IvHi.Mem S I x → IvHi.Mem S (IvHi.scale2 S I) (x / 2)
  mem_mul : ∀ {I J : Iv} {x y : ℝ},
    IvHi.Mem S I x → IvHi.Mem S J y → IvHi.Mem S (IvHi.mul S I J) (x * y)
  mem_invPos : ∀ {I : Iv} {x : ℝ},
    IvHi.Mem S I x → 0 < m2rS S I.lo → IvHi.Mem S (IvHi.invPos S I) (1 / x)
  mem_nonneg : ∀ {I : Iv} {x : ℝ},
    IvHi.Mem S I x → 0 ≤ x → IvHi.Mem S (IvHi.nonneg I) x
  mem_sqrt : ∀ {I : Iv} {x : ℝ},
    IvHi.Mem S I x → 0 ≤ m2rS S I.lo → 0 ≤ m2rS S I.hi → IvHi.Mem S (IvHi.sqrt S I) (Real.sqrt x)
  mem_inter : ∀ {I J : Iv} {x : ℝ},
    IvHi.Mem S I x → IvHi.Mem S J x → IvHi.Mem S (IvHi.inter I J) x
  mem_pt : ∀ n : ℤ, IvHi.Mem S (IvHi.pt n) (m2rS S n)
  mem_ratIv : ∀ (p : ℤ) (q : ℕ), 0 < q → IvHi.Mem S (IvHi.ratIv S p q) ((p : ℝ) / q)

/-- Soundness of the scale-`S` complex interval operations. -/
structure CDHiSound (S : ℤ) : Prop where
  mem_add : ∀ {D E : CD} {z w : ℂ},
    CDHi.Mem S D z → CDHi.Mem S E w → CDHi.Mem S (CDHi.add D E) (z + w)
  mem_neg : ∀ {D : CD} {z : ℂ}, CDHi.Mem S D z → CDHi.Mem S (CDHi.neg D) (-z)
  mem_sub : ∀ {D E : CD} {z w : ℂ},
    CDHi.Mem S D z → CDHi.Mem S E w → CDHi.Mem S (CDHi.sub D E) (z - w)
  mem_mul : ∀ {D E : CD} {z w : ℂ},
    CDHi.Mem S D z → CDHi.Mem S E w → CDHi.Mem S (CDHi.mul S D E) (z * w)
  mem_inv : ∀ {D : CD} {z : ℂ}, CDHi.Mem S D z →
    0 < m2rS S (IvHi.add (IvHi.sq S D.re) (IvHi.sq S D.im)).lo →
    CDHi.Mem S (CDHi.inv S D) (1 / z)
  mem_cst : ∀ {I : Iv} {v : ℝ}, IvHi.Mem S I v → CDHi.Mem S (CDHi.cst I) ((v : ℂ))
  mem_ONE : CDHi.Mem S (CDHi.ONE S) 1
  mem_inter : ∀ {D E : CD} {z : ℂ},
    CDHi.Mem S D z → CDHi.Mem S E z → CDHi.Mem S (CDHi.inter D E) z
  mem_pt : ∀ a b : ℤ, CDHi.Mem S (CD.pt a b) (m2rS S a + m2rS S b * Complex.I)
  mem_sqrt : ∀ {D : CD} {z : ℂ}, CDHi.Mem S D z → z ∈ Complex.slitPlane →
    0 ≤ m2rS S (IvHi.add (IvHi.sq S D.re) (IvHi.sq S D.im)).lo →
    0 ≤ m2rS S (IvHi.add (IvHi.sq S D.re) (IvHi.sq S D.im)).hi →
    0 ≤ m2rS S (CDHi.sqrtArgRe S D).hi →
    0 ≤ m2rS S (CDHi.sqrtArgIm S D).hi →
    CDHi.Mem S (CDHi.sqrt S D) (Complex.sqrt z)

end

end Work.ANum
