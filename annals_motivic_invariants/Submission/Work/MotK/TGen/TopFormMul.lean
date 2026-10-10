import Mathlib
import Submission.Work.MotK.TGen.FwTopDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The top form of a product

`Work.MotK.TGen.topForm p` is the leading (i.e. top degree) homogeneous form of `p`, defined as
`MvPolynomial.homogeneousComponent p.totalDegree p`.  This file proves that it is multiplicative:

`topForm (p * q) = topForm p * topForm q` for nonzero `p`, `q` over a field.

The mathematical content is the standard fact that the degree-`(deg p + deg q)` part of `p * q`
is the product of the degree-`deg p` part of `p` and the degree-`deg q` part of `q`.  Formally we
use the internal grading of `MvPolynomial` by degree: the canonical decomposition
`DirectSum.decompose` into the homogeneous submodules turns products into products
(`DirectSum.decompose_mul`), and taking the `(deg p + deg q)`-component of both sides every
summand except the top one dies because both factors are bounded by the total degree
(`MvPolynomial.homogeneousComponent_eq_zero`, through the support constraint).

## Main results

* `Work.MotK.TGen.coe_decompose_eq_homogeneousComponent` — the `i`-th component of the
  homogeneous decomposition is the `i`-th homogeneous component.
* `Work.MotK.TGen.homogeneousComponent_mul_totalDegree` — multiplicativity of the top homogeneous
  component.
* `Work.MotK.TGen.TopFormMul` — the same statement for `topForm`.
-/

set_option autoImplicit false

namespace Work.MotK.TGen

open MvPolynomial

section HomogeneousComponentMul

-- `homogeneousSubmodule` is the degree grading of `MvPolynomial`; the corresponding
-- `GradedAlgebra` structure is not a global instance (to avoid diamonds), so we enable it
-- locally for this section.
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The `i`-th component of the homogeneous decomposition of `r` is its homogeneous component of
degree `i`. -/
theorem coe_decompose_eq_homogeneousComponent {σ : Type*} {R : Type*} [CommSemiring R]
    (r : MvPolynomial σ R) (i : ℕ) :
    (↑((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) r) i :
        MvPolynomial σ R)) = MvPolynomial.homogeneousComponent i r :=
  MvPolynomial.decomposition.decompose'_apply r i

/-- **The top homogeneous component is multiplicative.**  The `(totalDegree p + totalDegree q)`
component of `p * q` is the product of the top components of `p` and `q`.  (No nonzeroness
hypothesis is needed here: the argument only uses that the graded components of `p` beyond
`totalDegree p` vanish, which is true for the zero polynomial as well.) -/
theorem homogeneousComponent_mul_totalDegree {σ : Type*} {R : Type*} [CommSemiring R]
    (p q : MvPolynomial σ R) :
    MvPolynomial.homogeneousComponent (p.totalDegree + q.totalDegree) (p * q)
      = MvPolynomial.homogeneousComponent p.totalDegree p
        * MvPolynomial.homogeneousComponent q.totalDegree q := by
  classical
  -- Every graded component of `r` of degree `> r.totalDegree` vanishes.
  have hle : ∀ (r : MvPolynomial σ R) (i : ℕ),
      (↑((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) r) i :
        MvPolynomial σ R)) ≠ 0 → i ≤ r.totalDegree := by
    intro r i hi
    by_contra h
    have h' : r.totalDegree < i := Nat.lt_of_not_le h
    exact hi (by rw [coe_decompose_eq_homogeneousComponent r i,
      MvPolynomial.homogeneousComponent_eq_zero i r h'])
  have hdec := DirectSum.decompose_mul (MvPolynomial.homogeneousSubmodule σ R) p q
  have hcomp : (↑((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) (p * q))
        (p.totalDegree + q.totalDegree)) : MvPolynomial σ R)
      = ↑(((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) p
            * DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) q)
          (p.totalDegree + q.totalDegree)) : MvPolynomial σ R) := by
    rw [hdec]
  rw [DirectSum.coe_mul_apply_eq_sum_antidiagonal] at hcomp
  -- Only the pair `(totalDegree p, totalDegree q)` can contribute.
  rw [Finset.sum_eq_single (p.totalDegree, q.totalDegree)] at hcomp
  · rw [coe_decompose_eq_homogeneousComponent (p * q) (p.totalDegree + q.totalDegree),
      coe_decompose_eq_homogeneousComponent p p.totalDegree,
      coe_decompose_eq_homogeneousComponent q q.totalDegree] at hcomp
    exact hcomp
  · rintro ⟨a, b⟩ hx hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_contra h
    have ha : (↑((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) p) a :
        MvPolynomial σ R)) ≠ 0 := by
      intro h0; exact h (by rw [h0, zero_mul])
    have hb : (↑((DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ R) q) b :
        MvPolynomial σ R)) ≠ 0 := by
      intro h0; exact h (by rw [h0, mul_zero])
    have h1 := hle p a ha
    have h2 := hle q b hb
    have h3 : a = p.totalDegree := by omega
    have h4 : b = q.totalDegree := by omega
    exact hne (Prod.ext h3 h4)
  · intro ha
    exact absurd (by simp) ha

end HomogeneousComponentMul

/-- **The top form is multiplicative**: the leading form of a product of two nonzero polynomials
is the product of the leading forms. -/
theorem TopFormMul (K : Type) [Field K] (p q : MvPolynomial (Fin 3) K) (hp : p ≠ 0) (hq : q ≠ 0) :
    Work.MotK.TGen.topForm (p * q) = Work.MotK.TGen.topForm p * Work.MotK.TGen.topForm q := by
  unfold Work.MotK.TGen.topForm
  rw [MvPolynomial.totalDegree_mul_of_isDomain hp hq]
  exact homogeneousComponent_mul_totalDegree p q

end Work.MotK.TGen
