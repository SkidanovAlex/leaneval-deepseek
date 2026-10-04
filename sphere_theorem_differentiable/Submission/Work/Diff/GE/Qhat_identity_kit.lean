import Mathlib
import Submission.Work.Diff.Evol.Calc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The algebraic identity `-Q̂ + Xact + ricact = Q` for algebraic curvature tensors

This file proves `Work.Diff.GE.Qhat_identity_kit`, the pure-algebra ingredient (labelled `(θ)` in
`Submission/Work/Diff/Evol/NOTES.md`) of the derivation of Hamilton's curvature evolution equation

  `∂ₜR = ΔR + Q(R)`   (in the Uhlenbeck frame),

namely that for **every** algebraic curvature tensor `R` (an array with the symmetries of the
Riemann tensor in an orthonormal frame) the three explicit quadratic arrays
`Qhat`, `Xact`, `ricact` of `Submission/Work/Diff/Evol/Calc.lean` satisfy

  `- Qhat R + Xact R + ricact R = Q R`,

where `Q` is Hamilton's reaction term (`Submission/Diff/Alg.lean`).

## Method

All four arrays are of the form `∑ p, ∑ q, (summand)`.  The proof exhibits the common summand
`qkitG` and shows:

* **Expansion** (`qkit_expand`): `-Qhat + Xact + ricact - Q = ∑ p, ∑ q, qkitG p q`
  (a purely combinatorial re-indexing of the four defining double sums, using
  `Finset.sum_mul`, `Finset.mul_sum`, `Finset.sum_comm` and the elementary fact that a sum of sums
  is the sum of the pointwise sum);
* **Antisymmetry** (`qkitG_pair`): `qkitG p q + qkitG q p = 0` for all `p q`.  This is the
  mathematical heart.  Modulo the antisymmetry and the pair symmetry of `R` the sum
  `qkitG p q + qkitG q p` collapses (this is `qkitSym`, the full eight-term antisymmetrisation of
  `R`, which equals `R` for algebraic `R`) to

    `2 * R p q k l * (R q p i j + R p i q j + R i q p j)`,

  and the bracket is exactly the first Bianchi identity `R q p i j + R p i q j + R i q p j = 0`;
* hence `∑ p, ∑ q, qkitG p q = 0` (the sum of an antisymmetric function over an ordered product is
  zero), which together with the expansion gives the claim.

The `qkitSym` device is what makes the collapse formal: because `qkitSym R` is *defined* as an
antisymmetrised expression, the collapse is a free polynomial identity that `ring` can check,
and `qkitSym R = R` follows from the hypotheses `hR`.
-/

namespace Work.Diff.GE

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The `(p,q)`-summand of `Qhat` (`Work.Diff.Evol.Qhat`) with the two dummy indices named `p`,`q`. -/
noncomputable def qkitQh (R : Curv4 n) (i j k l p q : Fin n) : ℝ :=
  R p i q j * R q p k l + R p i q p * R j q k l + R p i q k * R j p q l + R p i q l * R j p k q
    + R p j q p * R q i k l + R p j q i * R p q k l + R p j q k * R p i q l + R p j q l * R p i k q

/-- The `(p,q)`-summand of `Xact` (`Work.Diff.Evol.Xact`) after expanding `ricArr`. -/
noncomputable def qkitX (R : Curv4 n) (i j k l p q : Fin n) : ℝ :=
  R q i q p * R p j k l + R q j q p * R i p k l + R q k q p * R i j p l + R q l q p * R i j k p

/-- The `(p,q)`-summand of `ricact` (`Work.Diff.Evol.ricact`) after expanding `ricArr`. -/
noncomputable def qkitR (R : Curv4 n) (i j k l p q : Fin n) : ℝ :=
  -(R i j q l * R p q p k) + R i j q k * R p l p q

/-- The `(p,q)`-summand of Hamilton's `Q` (`Submission.Diff.Alg.Q`). -/
noncomputable def qkitQ (R : Curv4 n) (i j k l p q : Fin n) : ℝ :=
  R i j p q * R k l p q + 2 * R i p k q * R j p l q - 2 * R i p l q * R j p k q

/-- The common summand of `- Qhat + Xact + ricact - Q`. -/
noncomputable def qkitG (R : Curv4 n) (i j k l p q : Fin n) : ℝ :=
  - qkitQh R i j k l p q + qkitX R i j k l p q + qkitR R i j k l p q - qkitQ R i j k l p q

/-- The full eight-term antisymmetrisation of a `(0,4)`-array, i.e. the orthogonal projection onto
the arrays that are antisymmetric in the first pair, antisymmetric in the last pair and invariant
under the exchange of the two pairs.  For an algebraic curvature tensor this equals `R` itself. -/
noncomputable def qkitSym (R : Curv4 n) : Curv4 n := fun a b c d =>
  (R a b c d - R b a c d - R a b d c + R b a d c + R c d a b - R d c a b - R c d b a + R d c b a) / 8

/-- A sum of sums is the sum of the pointwise sum: the elementary combination step for the
expansion of `- Qhat + Xact + ricact - Q`. -/
theorem qkit_sum_combine (f g h k : Fin n → Fin n → ℝ) :
    -(∑ p, ∑ q, f p q) + (∑ p, ∑ q, g p q) + (∑ p, ∑ q, h p q) - (∑ p, ∑ q, k p q)
      = ∑ p, ∑ q, (- f p q + g p q + h p q - k p q) := by
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- **Expansion.**  The four quadratic arrays are all double sums over an ordered pair of frame
indices, and they add up to the double sum of the common summand `qkitG`. -/
theorem qkit_expand (R : Curv4 n) (i j k l : Fin n) :
    - Work.Diff.Evol.Qhat R i j k l + Work.Diff.Evol.Xact R i j k l
      + Work.Diff.Evol.ricact R i j k l - Submission.Diff.Alg.Q R i j k l
      = ∑ p, ∑ q, qkitG R i j k l p q := by
  have hQh : Work.Diff.Evol.Qhat R i j k l = ∑ p, ∑ q, qkitQh R i j k l p q := by
    simp only [Work.Diff.Evol.Qhat, qkitQh]
  have hX : Work.Diff.Evol.Xact R i j k l = ∑ p, ∑ q, qkitX R i j k l p q := by
    simp only [Work.Diff.Evol.Xact, Work.Diff.Evol.ricArr, qkitX, Finset.sum_mul,
      ← Finset.sum_add_distrib]
  have hR : Work.Diff.Evol.ricact R i j k l = ∑ p, ∑ q, qkitR R i j k l p q := by
    simp only [Work.Diff.Evol.ricact, Work.Diff.Evol.ricArr, qkitR, Finset.mul_sum]
    have h1 : (∑ a, ∑ b, R i j a l * R b a b k) = ∑ p, ∑ q, R i j q l * R p q p k := by
      rw [Finset.sum_comm]
    have h2 : (∑ a, ∑ b, R i j a k * R b l b a) = ∑ p, ∑ q, R i j q k * R p l p q := by
      rw [Finset.sum_comm]
    rw [h1, h2]
    simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hQ : Submission.Diff.Alg.Q R i j k l = ∑ p, ∑ q, qkitQ R i j k l p q := by
    simp only [Submission.Diff.Alg.Q, qkitQ]
  rw [hQh, hX, hR, hQ]
  simp only [qkitG]
  exact qkit_sum_combine _ _ _ _

/-- The antisymmetrisation `qkitSym R` of an algebraic curvature tensor `R` equals `R`. -/
theorem qkitSym_eq (R : Curv4 n) (hR : IsAlgCurv R) : ∀ a b c d, qkitSym R a b c d = R a b c d := by
  intro a b c d
  have f1 : R b a c d = - R a b c d := hR.1 a b c d
  have f2 : R a b d c = - R a b c d := by
    rw [← hR.2.1 a b d c, hR.1 c d a b, hR.2.1 a b c d]
  have f3 : R b a d c = R a b c d := by rw [hR.1 a b d c, f2]; ring
  have f4 : R c d a b = R a b c d := hR.2.1 a b c d
  have f5 : R d c a b = - R a b c d := by rw [hR.1 c d a b, f4]
  have f6 : R c d b a = - R a b c d := by rw [← hR.2.1 c d b a, f1]
  have f7 : R d c b a = R a b c d := by rw [hR.1 c d b a, f6]; ring
  simp only [qkitSym]
  rw [f1, f2, f3, f4, f5, f6, f7]
  ring

/-- **Antisymmetry of the summand.**  For an algebraic curvature tensor the summand `qkitG` is
antisymmetric in the two summed indices.  Modulo the pair symmetries of `R` (handled by replacing
`R` with its antisymmetrisation `qkitSym R`, which is equal to `R`) the sum `qkitG p q + qkitG q p`
collapses to `2 * R p q k l * (R q p i j + R p i q j + R i q p j)`, and the bracket is the first
Bianchi identity `hR.2.2 q p i j`. -/
theorem qkitG_pair (R : Curv4 n) (hR : IsAlgCurv R) (i j k l p q : Fin n) :
    qkitG R i j k l p q + qkitG R i j k l q p = 0 := by
  have hT : ∀ a b c d, qkitSym R a b c d = R a b c d := qkitSym_eq R hR
  have hfree : ∀ i j k l p q, qkitG (qkitSym R) i j k l p q + qkitG (qkitSym R) i j k l q p
      = 2 * qkitSym R p q k l
        * (qkitSym R q p i j + qkitSym R p i q j + qkitSym R i q p j) := by
    intro i j k l p q
    simp only [qkitG, qkitQh, qkitX, qkitR, qkitQ, qkitSym]
    ring
  have hG : ∀ i j k l p q, qkitG R i j k l p q = qkitG (qkitSym R) i j k l p q := by
    intro i j k l p q
    simp only [qkitG, qkitQh, qkitX, qkitR, qkitQ, ← hT]
  rw [hG, hG, hfree, hT, hT, hT, hT]
  rw [hR.2.2 q p i j]
  ring

/-- The double sum of the summand vanishes, because the summand is antisymmetric. -/
theorem qkit_sum_zero (R : Curv4 n) (hR : IsAlgCurv R) (i j k l : Fin n) :
    ∑ p, ∑ q, qkitG R i j k l p q = 0 := by
  have hanti : ∀ p q, qkitG R i j k l q p = - qkitG R i j k l p q := by
    intro p q
    have := qkitG_pair R hR i j k l q p
    linarith
  have hsym : (∑ p, ∑ q, qkitG R i j k l p q) = ∑ p, ∑ q, qkitG R i j k l q p := by
    rw [Finset.sum_comm]
  have hneg : (∑ p, ∑ q, qkitG R i j k l q p) = -(∑ p, ∑ q, qkitG R i j k l p q) := by
    calc ∑ p, ∑ q, qkitG R i j k l q p
        = ∑ p, ∑ q, - qkitG R i j k l p q := by
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro q _
          exact hanti p q
      _ = ∑ p, - ∑ q, qkitG R i j k l p q := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.sum_neg_distrib]
      _ = - ∑ p, ∑ q, qkitG R i j k l p q := by rw [Finset.sum_neg_distrib]
  have hS : (∑ p, ∑ q, qkitG R i j k l p q) = -(∑ p, ∑ q, qkitG R i j k l p q) :=
    hsym.trans hneg
  linarith

/-- **The algebraic identity `-Q̂ + Xact + ricact = Q`** for every algebraic curvature tensor. -/
theorem Qhat_identity_kit {n : ℕ} (R : Submission.Diff.Alg.Curv4 n)
    (hR : Submission.Diff.Alg.IsAlgCurv R) :
    ∀ i j k l, -Work.Diff.Evol.Qhat R i j k l + Work.Diff.Evol.Xact R i j k l
      + Work.Diff.Evol.ricact R i j k l = Submission.Diff.Alg.Q R i j k l := by
  intro i j k l
  have h1 := qkit_expand R i j k l
  have h2 := qkit_sum_zero R hR i j k l
  linarith

end Work.Diff.GE
