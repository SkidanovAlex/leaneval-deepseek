import Mathlib
import Submission.Work.ORVonNeumann.BaerLocalization.BaerRing

namespace Work.ORVonNeumann.BaerLocalization

/-- The element-Baer condition forces the involution to be proper: `x * star x = 0` implies
`x = 0`.  (This is Kaplansky's theorem that a Baer `*`-ring has a proper involution; it is
reproved here so that this file does not depend on a separate development.)  The argument:
let `e = annihProj h x` generate the right annihilator of `x`.  Since `x * star x = 0`, the
element `star x` lies in that annihilator, so `star x = e * y`; starring and using `star e = e`
gives `x = star y * e`, whence `x = x * e = 0` because `e` itself lies in the annihilator. -/
private theorem isProperStar_of_hasBaerAnnihilators_aux {R : Type*} [Ring R] [StarRing R]
    (h : Work.ORVonNeumann.BaerRing.HasBaerAnnihilators R) : Work.ORVonNeumann.IsProperStar R := by
  intro x hx
  set e := Work.ORVonNeumann.BaerRing.annihProj h x with he
  have hep : IsStarProjection e := by
    rw [he]; exact Work.ORVonNeumann.BaerRing.annihProj_isStarProjection h x
  have hse : star e = e := hep.isSelfAdjoint.star_eq
  have hee : e * e = e := hep.isIdempotentElem.eq
  have hspec : ∀ u : R, x * u = 0 ↔ ∃ y, u = e * y := by
    intro u; rw [he]; exact Work.ORVonNeumann.BaerRing.annihProj_spec' h x u
  have hxe : x * e = 0 := (hspec e).mpr ⟨1, (mul_one e).symm⟩
  obtain ⟨y, hy⟩ := (hspec (star x)).mp hx
  have hx' : x = star y * e := by
    have h1 := congrArg star hy
    rw [star_star, star_mul, hse] at h1
    exact h1
  rw [hx'] at hxe
  rw [mul_assoc, hee] at hxe
  rw [hx']
  exact hxe

/-- The right annihilator of `star a * a` coincides with that of `a`, so `rightProj h` is
unchanged.  The two right annihilators are equal because `a * x = 0` iff `(star a * a) * x = 0`:
the non-trivial direction uses that the Baer condition makes the involution proper, so that
`(a * x)⋆ * (a * x) = star x * ((star a * a) * x) = 0` forces `a * x = 0`. -/
theorem rightProj_star_mul_self {R : Type*} [Ring R] [StarRing R] (h : Work.ORVonNeumann.BaerRing.HasBaerAnnihilators R) (a : R) : Work.ORVonNeumann.BaerRing.rightProj h (star a * a) = Work.ORVonNeumann.BaerRing.rightProj h a := by
  have hproper : Work.ORVonNeumann.IsProperStar R := isProperStar_of_hasBaerAnnihilators_aux h
  have hleft : Work.ORVonNeumann.IsProperStarLeft R :=
    Work.ORVonNeumann.isProperStar_iff_isProperStarLeft.mp hproper
  apply Work.ORVonNeumann.BaerRing.rightProj_eq_of_annih_eq h (a := star a * a) (b := a)
  intro x
  constructor
  · intro hx
    refine hleft (a * x) ?_
    rw [star_mul]
    rw [mul_assoc, ← mul_assoc (star a) a x, hx, mul_zero]
  · intro hx
    rw [mul_assoc, hx, mul_zero]

end Work.ORVonNeumann.BaerLocalization
