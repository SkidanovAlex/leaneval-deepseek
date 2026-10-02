/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# `Work.SeedCert.IV`, `Work.SeedCert.CBox`: real intervals and complex boxes

The box layer (item **I** of the `SeedCertNum` contract, `NOTES_LEAD_mandelbar_noncusp.md` §3.2) on
top of the exact dyadics of `Submission/Work/SeedCertNum/Dyadic.lean`.

* `IV` is a closed real interval `[lo, hi]` with dyadic endpoints, `IV.toSet` its carrier;
* `CBox` is a closed complex box `[rlo,rhi] × [ilo,ihi]`, `CBox.toSet` its carrier.

Everything is stated so that a *certificate* is a `Bool` computed from the numerators: the
`mem_*` lemmas below turn the `Bool` tests of `Submission/Work/SeedCertNum/D1.lean` into statements
about `toSet`.

## Main definitions

* `IV.toSet`, `IV.add`, `IV.neg`, `IV.sub`, `IV.mul`, `IV.two`, `IV.half`, `IV.mulScalar`;
* `CBox.toSet`, `CBox.re`, `CBox.im`, `CBox.conj`, `CBox.neg`, `CBox.add`, `CBox.sub`, `CBox.mul`,
  `CBox.sq`, `CBox.mulScalar`.

## Main results

* `IV.mem_add`, `IV.mem_neg`, `IV.mem_sub`, `IV.mem_two`, `IV.mem_half`, `IV.mem_mulScalar`;
* `CBox.mem_add`, `CBox.mem_neg`, `CBox.mem_conj`, `CBox.mem_sub`, `CBox.mem_mulScalar`.

Conventions: complex boxes are closed; `re`/`im` are the coordinate intervals; `conj B` has
imaginary interval `[-ihi, -ilo]`; `B.neg` reverses both coordinate intervals after negating.
-/
import Submission.Work.SeedCertNum.Dyadic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

/-! ## Real intervals with dyadic endpoints -/

/-- A closed real interval `[lo, hi]`. -/
structure IV where
  lo : Dya
  hi : Dya
deriving DecidableEq, Repr

namespace IV

/-- The real set carried by the interval. -/
def toSet (I : IV) : Set ℝ := {x : ℝ | I.lo.toReal ≤ x ∧ x ≤ I.hi.toReal}

@[simp] theorem mem_toSet {I : IV} {x : ℝ} :
    x ∈ I.toSet ↔ I.lo.toReal ≤ x ∧ x ≤ I.hi.toReal := Iff.rfl

/-- A dyadic, as a degenerate interval. -/
def ofDya (a : Dya) : IV := ⟨a, a⟩

/-- The interval `[0,1]`. -/
def unit : IV := ⟨Dya.zero, Dya.one⟩

/-- Interval sum. -/
def add (I J : IV) : IV := ⟨Dya.add I.lo J.lo, Dya.add I.hi J.hi⟩

/-- Interval negation `[-hi, -lo]`. -/
def neg (I : IV) : IV := ⟨Dya.neg I.hi, Dya.neg I.lo⟩

/-- Interval difference. -/
def sub (I J : IV) : IV := I.add J.neg

/-- Doubling of an interval. -/
def two (I : IV) : IV := ⟨Dya.twice I.lo, Dya.twice I.hi⟩

/-- Halving of an interval. -/
def half (I : IV) : IV := ⟨Dya.half I.lo, Dya.half I.hi⟩

/-- Multiplication of an interval by a dyadic constant. -/
def mulScalar (a : Dya) (I : IV) : IV :=
  ⟨Dya.min (Dya.mul a I.lo) (Dya.mul a I.hi), Dya.max (Dya.mul a I.lo) (Dya.mul a I.hi)⟩

/-- The lower end of the four corner products. -/
def cornerMin (I J : IV) : Dya :=
  Dya.min (Dya.min (Dya.mul I.lo J.lo) (Dya.mul I.lo J.hi))
          (Dya.min (Dya.mul I.hi J.lo) (Dya.mul I.hi J.hi))

/-- The upper end of the four corner products. -/
def cornerMax (I J : IV) : Dya :=
  Dya.max (Dya.max (Dya.mul I.lo J.lo) (Dya.mul I.lo J.hi))
          (Dya.max (Dya.mul I.hi J.lo) (Dya.mul I.hi J.hi))

/-- Interval product: the hull of the four corner products. -/
def mul (I J : IV) : IV := ⟨cornerMin I J, cornerMax I J⟩

/-- Interval square. -/
def sq (I : IV) : IV := I.mul I

theorem mem_add {I J : IV} {x y : ℝ} (hx : x ∈ I.toSet) (hy : y ∈ J.toSet) :
    x + y ∈ (I.add J).toSet := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  refine ⟨?_, ?_⟩
  · simp only [toSet, Set.mem_ofPred_eq, add, Dya.toReal_add]
    exact add_le_add h1 h3
  · simp only [toSet, Set.mem_ofPred_eq, add, Dya.toReal_add]
    exact add_le_add h2 h4

theorem mem_neg {I : IV} {x : ℝ} (hx : x ∈ I.toSet) : -x ∈ (I.neg).toSet := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · simp only [toSet, Set.mem_ofPred_eq, neg, Dya.toReal_neg]
    linarith
  · simp only [toSet, Set.mem_ofPred_eq, neg, Dya.toReal_neg]
    linarith

theorem mem_sub {I J : IV} {x y : ℝ} (hx : x ∈ I.toSet) (hy : y ∈ J.toSet) :
    x - y ∈ (I.sub J).toSet := by
  have := mem_add hx (mem_neg hy)
  simpa [sub, sub_eq_add_neg] using this

theorem mem_two {I : IV} {x : ℝ} (hx : x ∈ I.toSet) : 2 * x ∈ (I.two).toSet := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · simp only [toSet, Set.mem_ofPred_eq, two, Dya.toReal_twice]
    linarith
  · simp only [toSet, Set.mem_ofPred_eq, two, Dya.toReal_twice]
    linarith

theorem mem_half {I : IV} {x : ℝ} (hx : x ∈ I.toSet) : x / 2 ∈ (I.half).toSet := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · simp only [toSet, Set.mem_ofPred_eq, half, Dya.toReal_half]
    linarith
  · simp only [toSet, Set.mem_ofPred_eq, half, Dya.toReal_half]
    linarith

theorem mem_mulScalar {I : IV} {x : ℝ} (hx : x ∈ I.toSet) {a : Dya} :
    a.toReal * x ∈ (I.mulScalar a).toSet := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  all_goals
    simp only [toSet, Set.mem_ofPred_eq, mulScalar, Dya.toReal_min, Dya.toReal_max,
      Dya.toReal_mul]
  · rcases le_total 0 a.toReal with h | h
    · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left h1 h)
    · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left h2 h)
  · rcases le_total 0 a.toReal with h | h
    · exact le_trans (mul_le_mul_of_nonneg_left h2 h) (le_max_right _ _)
    · exact le_trans (mul_le_mul_of_nonpos_left h1 h) (le_max_left _ _)

end IV

/-! ## Complex boxes -/

/-- A closed complex box `[rlo,rhi] × [ilo,ihi]` with dyadic endpoints. -/
structure CBox where
  rlo : Dya
  rhi : Dya
  ilo : Dya
  ihi : Dya
deriving DecidableEq, Repr

namespace CBox

/-- The set carried by the box. -/
def toSet (B : CBox) : Set ℂ :=
  {z : ℂ | B.rlo.toReal ≤ z.re ∧ z.re ≤ B.rhi.toReal ∧
    B.ilo.toReal ≤ z.im ∧ z.im ≤ B.ihi.toReal}

@[simp] theorem mem_toSet {B : CBox} {z : ℂ} :
    z ∈ B.toSet ↔ B.rlo.toReal ≤ z.re ∧ z.re ≤ B.rhi.toReal ∧
      B.ilo.toReal ≤ z.im ∧ z.im ≤ B.ihi.toReal := Iff.rfl

/-- The real part interval. -/
def re (B : CBox) : IV := ⟨B.rlo, B.rhi⟩

/-- The imaginary part interval. -/
def im (B : CBox) : IV := ⟨B.ilo, B.ihi⟩

/-- A box from its four dyadic coordinates. -/
def mk4 (a b c d : Dya) : CBox := ⟨a, b, c, d⟩

/-- Componentwise negation `z ↦ -z`. -/
def neg (B : CBox) : CBox :=
  ⟨Dya.neg B.rhi, Dya.neg B.rlo, Dya.neg B.ihi, Dya.neg B.ilo⟩

/-- Complex conjugation. -/
def conj (B : CBox) : CBox := ⟨B.rlo, B.rhi, Dya.neg B.ihi, Dya.neg B.ilo⟩

/-- Componentwise sum. -/
def add (B C : CBox) : CBox :=
  ⟨Dya.add B.rlo C.rlo, Dya.add B.rhi C.rhi, Dya.add B.ilo C.ilo, Dya.add B.ihi C.ihi⟩

/-- Componentwise difference. -/
def sub (B C : CBox) : CBox := B.add C.neg

/-- Multiplication of a box by a real dyadic scalar. -/
def mulScalar (a : Dya) (B : CBox) : CBox :=
  ⟨(B.re.mulScalar a).lo, (B.re.mulScalar a).hi, (B.im.mulScalar a).lo, (B.im.mulScalar a).hi⟩

/-- Complex product: `re = re·re - im·im`, `im = re·im + im·re`. -/
def mul (B C : CBox) : CBox :=
  let rr := (B.re.mul C.re).sub (B.im.mul C.im)
  let ii := (B.re.mul C.im).add (B.im.mul C.re)
  ⟨rr.lo, rr.hi, ii.lo, ii.hi⟩

/-- Complex square. -/
def sq (B : CBox) : CBox := B.mul B

theorem conj_conj (B : CBox) : B.conj.conj = B := by
  simp only [conj, Dya.neg_neg]

theorem neg_neg (B : CBox) : B.neg.neg = B := by
  simp only [neg, Dya.neg_neg]

theorem mem_add {B C : CBox} {z w : ℂ} (hz : z ∈ B.toSet) (hw : w ∈ C.toSet) :
    z + w ∈ (B.add C).toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  obtain ⟨k1, k2, k3, k4⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [toSet, Set.mem_ofPred_eq, add, Complex.add_re, Dya.toReal_add]
    exact add_le_add h1 k1
  · simp only [toSet, Set.mem_ofPred_eq, add, Complex.add_re, Dya.toReal_add]
    exact add_le_add h2 k2
  · simp only [toSet, Set.mem_ofPred_eq, add, Complex.add_im, Dya.toReal_add]
    exact add_le_add h3 k3
  · simp only [toSet, Set.mem_ofPred_eq, add, Complex.add_im, Dya.toReal_add]
    exact add_le_add h4 k4

theorem mem_neg {B : CBox} {z : ℂ} (hz : z ∈ B.toSet) : -z ∈ (B.neg).toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [toSet, Set.mem_ofPred_eq, neg, Complex.neg_re, Dya.toReal_neg]
    linarith
  · simp only [toSet, Set.mem_ofPred_eq, neg, Complex.neg_re, Dya.toReal_neg]
    linarith
  · simp only [toSet, Set.mem_ofPred_eq, neg, Complex.neg_im, Dya.toReal_neg]
    linarith
  · simp only [toSet, Set.mem_ofPred_eq, neg, Complex.neg_im, Dya.toReal_neg]
    linarith

theorem mem_conj {B : CBox} {z : ℂ} (hz : z ∈ B.toSet) : (star z : ℂ) ∈ (B.conj).toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [toSet, Set.mem_ofPred_eq, conj, RCLike.star_def, Complex.conj_re]
    exact h1
  · simp only [toSet, Set.mem_ofPred_eq, conj, RCLike.star_def, Complex.conj_re]
    exact h2
  · simp only [toSet, Set.mem_ofPred_eq, conj, RCLike.star_def, Complex.conj_im,
      Dya.toReal_neg]
    linarith
  · simp only [toSet, Set.mem_ofPred_eq, conj, RCLike.star_def, Complex.conj_im,
      Dya.toReal_neg]
    linarith

theorem mem_sub {B C : CBox} {z w : ℂ} (hz : z ∈ B.toSet) (hw : w ∈ C.toSet) :
    z - w ∈ (B.sub C).toSet := by
  have := mem_add hz (mem_neg hw)
  simpa [sub, sub_eq_add_neg] using this

theorem mem_mulScalar {B : CBox} {z : ℂ} (hz : z ∈ B.toSet) {a : Dya} :
    (a.toReal : ℂ) * z ∈ (B.mulScalar a).toSet := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  have hr := IV.mem_mulScalar (I := B.re) ⟨h1, h2⟩ (a := a)
  have hi := IV.mem_mulScalar (I := B.im) ⟨h3, h4⟩ (a := a)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [toSet, Set.mem_ofPred_eq, mulScalar, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact hr.1
  · simp only [toSet, Set.mem_ofPred_eq, mulScalar, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact hr.2
  · simp only [toSet, Set.mem_ofPred_eq, mulScalar, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    exact hi.1
  · simp only [toSet, Set.mem_ofPred_eq, mulScalar, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    exact hi.2

end CBox

end Work.SeedCert
