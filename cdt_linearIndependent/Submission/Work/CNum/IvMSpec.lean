import Mathlib
import Submission.Work.CNum.Fx

/-!
# `Work.CNum.IvMSpec` — soundness of the four-corner interval multiplication `IvM`

`Work.CNum.IvM I J` is the interval whose lower endpoint is the minimum (rounded down) of the four
mantissa products `I.lo * J.lo`, `I.lo * J.hi`, `I.hi * J.lo`, `I.hi * J.hi`, and whose upper
endpoint is the maximum (rounded up) of the same four products at scale `SC`.

`IvMSpec` says that this is a sound enclosure of the *product* of two enclosures:

`x ∈ I → y ∈ J → x * y ∈ IvM I J`.

The mathematical content is that the bilinear function `(x, y) ↦ x * y` on a rectangle
`[a₁,a₂] × [b₁,b₂]` is bounded by its corner values, which is the classical "interval
multiplication" rule.  Formally (`mul_bounds_corners`), with `a₁ ≤ x ≤ a₂`, `b₁ ≤ y ≤ b₂`,

`min (min (a₁b₁) (a₁b₂)) (min (a₂b₁) (a₂b₂)) ≤ x * y ≤ max (max (a₁b₁) (a₁b₂)) (max (a₂b₁) (a₂b₂))`,

and everything is then pushed from `ℝ` back to the mantissa level with the outward-rounding
lemmas `Iv.mulLo_le` (`⌊a*b/SC⌋/SC ≤ (a/SC)(b/SC)`) and `Iv.le_mulHi` (`(a/SC)(b/SC) ≤ ⌈a*b/SC⌉/SC`).
-/

namespace Work.CNum

open Work.ANum

/-- **Corner bound for a bilinear product.**  If `x ∈ [a₁, a₂]` and `y ∈ [b₁, b₂]`, then `x * y` lies
between the minimum and the maximum of the four corner products. -/
lemma mul_bounds_corners {a₁ a₂ b₁ b₂ x y : ℝ} (hx1 : a₁ ≤ x) (hx2 : x ≤ a₂)
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

theorem IvMSpec {I J : Work.ANum.Iv} {x y : ℝ} (hx : Work.ANum.Iv.Mem I x) (hy : Work.ANum.Iv.Mem J y) : Work.ANum.Iv.Mem (IvM I J) (x * y) := by
  have h11 : m2r (mulD I.lo J.lo) ≤ m2r I.lo * m2r J.lo := Iv.mulLo_le I.lo J.lo
  have h12 : m2r (mulD I.lo J.hi) ≤ m2r I.lo * m2r J.hi := Iv.mulLo_le I.lo J.hi
  have h21 : m2r (mulD I.hi J.lo) ≤ m2r I.hi * m2r J.lo := Iv.mulLo_le I.hi J.lo
  have h22 : m2r (mulD I.hi J.hi) ≤ m2r I.hi * m2r J.hi := Iv.mulLo_le I.hi J.hi
  have u11 : m2r I.lo * m2r J.lo ≤ m2r (mulU I.lo J.lo) := Iv.le_mulHi I.lo J.lo
  have u12 : m2r I.lo * m2r J.hi ≤ m2r (mulU I.lo J.hi) := Iv.le_mulHi I.lo J.hi
  have u21 : m2r I.hi * m2r J.lo ≤ m2r (mulU I.hi J.lo) := Iv.le_mulHi I.hi J.lo
  have u22 : m2r I.hi * m2r J.hi ≤ m2r (mulU I.hi J.hi) := Iv.le_mulHi I.hi J.hi
  have hkey := mul_bounds_corners (a₁ := m2r I.lo) (a₂ := m2r I.hi) (b₁ := m2r J.lo) (b₂ := m2r J.hi)
    hx.1 hx.2 hy.1 hy.2
  have hlo_def : (IvM I J).lo =
      min (min (mulD I.lo J.lo) (mulD I.lo J.hi)) (min (mulD I.hi J.lo) (mulD I.hi J.hi)) := rfl
  have hhi_def : (IvM I J).hi =
      max (max (mulU I.lo J.lo) (mulU I.lo J.hi)) (max (mulU I.hi J.lo) (mulU I.hi J.hi)) := rfl
  constructor
  · rw [hlo_def, Iv.m2r_min, Iv.m2r_min, Iv.m2r_min]
    exact le_trans (min_le_min (min_le_min h11 h12) (min_le_min h21 h22)) hkey.1
  · rw [hhi_def, Iv.m2r_max, Iv.m2r_max, Iv.m2r_max]
    exact le_trans hkey.2 (max_le_max (max_le_max u11 u12) (max_le_max u21 u22))

end Work.CNum
