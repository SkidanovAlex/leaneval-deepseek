/-
# `T13.Iv` — a tiny interval-arithmetic engine (real endpoints)

Rational-endpoint interval arithmetic used by the `table13_cert` numerical certificate.
Endpoints are `ℝ` (they are always rational numbers in the applications, but keeping them
in `ℝ` avoids coercion noise and lets `norm_num` evaluate concrete instances).

`mem_inv` requires the interval to be strictly positive.
-/
import Mathlib

noncomputable section

namespace Work.LinnikAreas.Density4.T13

structure Iv where
  lo : ℝ
  hi : ℝ

namespace Iv

/-- `I.Mem x` : the real number `x` lies in the interval `I`. -/
def Mem (I : Iv) (x : ℝ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

@[simp] theorem mem_iff (I : Iv) (x : ℝ) : I.Mem x ↔ I.lo ≤ x ∧ x ≤ I.hi := Iff.rfl

def ofReal (x : ℝ) : Iv := ⟨x, x⟩

theorem mem_ofReal (x : ℝ) : (ofReal x).Mem x := ⟨le_refl x, le_refl x⟩

def add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩

theorem mem_add {a b : Iv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (add a b).Mem (x + y) :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

def neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩

theorem mem_neg {a : Iv} {x : ℝ} (hx : a.Mem x) : (neg a).Mem (-x) :=
  ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

def sub (a b : Iv) : Iv := add a (neg b)

theorem mem_sub {a b : Iv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (sub a b).Mem (x - y) :=
  mem_add hx (mem_neg hy)

def mul (a b : Iv) : Iv :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
   max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩

/-- Corner upper bound for a product over a rectangle. -/
theorem mul_le_max4 {alo ahi blo bhi x y : ℝ} (h1 : alo ≤ x) (h2 : x ≤ ahi)
    (h3 : blo ≤ y) (h4 : y ≤ bhi) :
    x * y ≤ max (max (alo * blo) (alo * bhi)) (max (ahi * blo) (ahi * bhi)) := by
  have key : ∀ c : ℝ, c * y ≤ max (c * blo) (c * bhi) := by
    intro c
    rcases le_total 0 c with hc | hc
    · exact le_trans (mul_le_mul_of_nonneg_left h4 hc) (le_max_right _ _)
    · have hcy : c * y ≤ c * blo := mul_le_mul_of_nonpos_left h3 hc
      exact le_trans hcy (le_max_left _ _)
  rcases le_total 0 y with hy | hy
  · refine le_trans (mul_le_mul_of_nonneg_right h2 hy) (le_trans (key ahi) ?_)
    exact le_max_right _ _
  · refine le_trans (mul_le_mul_of_nonpos_right h1 hy) (le_trans (key alo) ?_)
    exact le_max_left _ _

/-- Corner lower bound for a product over a rectangle. -/
theorem min4_le_mul {alo ahi blo bhi x y : ℝ} (h1 : alo ≤ x) (h2 : x ≤ ahi)
    (h3 : blo ≤ y) (h4 : y ≤ bhi) :
    min (min (alo * blo) (alo * bhi)) (min (ahi * blo) (ahi * bhi)) ≤ x * y := by
  have key : ∀ c : ℝ, min (c * blo) (c * bhi) ≤ c * y := by
    intro c
    rcases le_total 0 c with hc | hc
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h3 hc)
    · have hcy : c * bhi ≤ c * y := mul_le_mul_of_nonpos_left h4 hc
      exact le_trans (min_le_right _ _) hcy
  rcases le_total 0 y with hy | hy
  · refine le_trans (le_trans (min_le_left _ _) (key alo)) ?_
    exact mul_le_mul_of_nonneg_right h1 hy
  · refine le_trans (le_trans (min_le_right _ _) (key ahi)) ?_
    exact mul_le_mul_of_nonpos_right h2 hy

theorem mem_mul {a b : Iv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) :
    (mul a b).Mem (x * y) :=
  ⟨min4_le_mul hx.1 hx.2 hy.1 hy.2, mul_le_max4 hx.1 hx.2 hy.1 hy.2⟩

def inv (a : Iv) : Iv := ⟨1 / a.hi, 1 / a.lo⟩

theorem mem_inv {a : Iv} {x : ℝ} (hx : a.Mem x) (hpos : 0 < a.lo) :
    (inv a).Mem x⁻¹ := by
  have hxpos : 0 < x := lt_of_lt_of_le hpos hx.1
  have hhipos : 0 < a.hi := lt_of_lt_of_le hpos (le_trans hx.1 hx.2)
  constructor
  · show 1 / a.hi ≤ x⁻¹
    rw [div_eq_mul_inv, one_mul]
    exact (inv_le_inv₀ hhipos hxpos).mpr hx.2
  · show x⁻¹ ≤ 1 / a.lo
    rw [div_eq_mul_inv, one_mul]
    exact (inv_le_inv₀ hxpos hpos).mpr hx.1

def div (a b : Iv) : Iv := mul a (inv b)

theorem mem_div {a b : Iv} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) (hpos : 0 < b.lo) :
    (div a b).Mem (x / y) := by
  have h := mem_mul hx (mem_inv hy hpos)
  simpa only [div, div_eq_mul_inv] using h

end Iv

end Work.LinnikAreas.Density4.T13
