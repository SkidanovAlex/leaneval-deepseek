import Mathlib
import Submission.Work.GenShared.periods_defs
import Submission.Work.GenShared.rreg_Dv
import Submission.Work.GenShared.hasDerivAt_rval

/-!
# Tools for the evaluation form `Wev` and its derivative

This module collects the elementary algebra of `Rval` (the evaluation of a rational function at a
point, read off from its canonical numerator/denominator representative, see
`Work.GenShared.periods_defs`) that the `inN_dv` argument needs:

* `Nreg n z` / `Nset x0 δ n` — the three regularity conditions of a tuple `n ∈ W k` as a
  `Prop`/`Set`, so that `InN x0 δ y1 J n` becomes `∀ z ∈ Nset x0 δ n, Wev y1 J n z = 0`
  (`InN_iff_forall_Nset`);
* `Rval_add_of`, `Rval_mul_of`, `Rval_neg_of`, `Rval_sub_of`, `Rval_sum_of` — `Rval` is a ring
  homomorphism on the regular locus of `z` (each lemma asking only that the *factors* are regular
  at `z`);
* `WevD y1 J n z` — the explicit expansion of the derivative `d/dz (Wev y1 J n) (z)`:
  `Rval (dRat n.1) z·y1 z + Rval n.1 z·y1' z + Rval (dRat n.2.1) z·y1' z
   + Rval n.2.1 z·y1'' z + Σᵢ (Rval (dRat (n.2.2 i)) z·Jᵢ z + Rval (n.2.2 i) z·Jᵢ' z)`.

The identity `Wev y1 J (Dv p2 p1 p0 rn rd n) z = WevD y1 J n z` (using the differential equation
for `y1` and the derivative relations for `Jᵢ`) together with the calculus lemma
`HasDerivAt (Wev y1 J n) (WevD y1 J n z) z` is what makes `N = ker ev` stable under the connection
`Dv`.
-/

namespace Work.GenShared

open Complex Metric Work.GenShared
open Submission.CDT (dRat)

noncomputable section

/-! ## The regularity locus -/

/-- The three regularity conditions of a tuple `n ∈ W k` at a point `z`. -/
def Nreg {k : ℕ} (n : W k) (z : ℂ) : Prop :=
  Rreg n.1 z ∧ Rreg n.2.1 z ∧ ∀ i, Rreg (n.2.2 i) z

/-- The set of points of the ball at which every coefficient of `n` is regular. -/
def Nset {k : ℕ} (x0 : ℂ) (δ : ℝ) (n : W k) : Set ℂ := {z | z ∈ ball x0 δ ∧ Nreg n z}

/-- `InN` is exactly the vanishing of `Wev y1 J n` on the regularity locus `Nset x0 δ n`. -/
lemma InN_iff_forall_Nset {k : ℕ} {x0 : ℂ} {δ : ℝ} {y1 : ℂ → ℂ} {J : Fin k → ℂ → ℂ}
    {n : W k} : InN x0 δ y1 J n ↔ ∀ z ∈ Nset x0 δ n, Wev y1 J n z = 0 := by
  constructor
  · intro h z hz
    exact h z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  · intro h z hz ha hb hc
    exact h z ⟨hz, ha, hb, hc⟩

/-! ## `Rval` as a ring homomorphism on the regular locus -/

/-- `Rval` of a polynomial coefficient. -/
lemma Rval_algMap_poly (p : Polynomial ℂ) (z : ℂ) :
    Rval (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) z = p.eval z := by
  simp [Rval, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]

/-- The zero rational function evaluates to zero. -/
lemma Rval_zero (z : ℂ) : Rval (0 : RatFunc ℂ) z = 0 := by simp [Rval]

/-- `Rval` is additive where both summands are regular. -/
lemma Rval_add_of {f g : RatFunc ℂ} {z : ℂ} (hf : Rreg f z) (hg : Rreg g z) :
    Rval (f + g) z = Rval f z + Rval g z := by
  rw [show Rval (f + g) z = RatFunc.eval (RingHom.id ℂ) z (f + g) from rfl,
      show Rval f z = RatFunc.eval (RingHom.id ℂ) z f from rfl,
      show Rval g z = RatFunc.eval (RingHom.id ℂ) z g from rfl]
  exact RatFunc.eval_add (f := RingHom.id ℂ) (a := z) hf hg

/-- `Rval` is multiplicative where both factors are regular. -/
lemma Rval_mul_of {f g : RatFunc ℂ} {z : ℂ} (hf : Rreg f z) (hg : Rreg g z) :
    Rval (f * g) z = Rval f z * Rval g z := by
  rw [show Rval (f * g) z = RatFunc.eval (RingHom.id ℂ) z (f * g) from rfl,
      show Rval f z = RatFunc.eval (RingHom.id ℂ) z f from rfl,
      show Rval g z = RatFunc.eval (RingHom.id ℂ) z g from rfl]
  exact RatFunc.eval_mul (f := RingHom.id ℂ) (a := z) hf hg

/-- The constant `-1` evaluates to `-1`. -/
lemma Rval_neg_one (z : ℂ) : Rval (-1 : RatFunc ℂ) z = -1 := by
  rw [show (-1 : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) (-1 : Polynomial ℂ) by
    rw [map_neg, map_one]]
  rw [Rval_algMap_poly]
  simp

/-- `Rval` commutes with negation on the regular locus. -/
lemma Rval_neg_of {f : RatFunc ℂ} {z : ℂ} (hf : Rreg f z) : Rval (-f) z = -Rval f z := by
  have h : (-f : RatFunc ℂ) = (-1 : RatFunc ℂ) * f := by ring
  rw [h, Rval_mul_of (rreg_neg_one z) hf, Rval_neg_one]
  ring

/-- `Rval` is subtractive where both terms are regular. -/
lemma Rval_sub_of {f g : RatFunc ℂ} {z : ℂ} (hf : Rreg f z) (hg : Rreg g z) :
    Rval (f - g) z = Rval f z - Rval g z := by
  rw [sub_eq_add_neg, Rval_add_of hf (rreg_neg hg), Rval_neg_of hg]
  ring

/-- `Rreg` is closed under finite sums over an arbitrary `Finset`. -/
lemma Rreg_finset_sum {ι : Type*} (s : Finset ι) (g : ι → RatFunc ℂ) {z : ℂ}
    (hg : ∀ i ∈ s, Rreg (g i) z) : Rreg (∑ i ∈ s, g i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rreg_zero (z := z)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact rreg_add (hg a (Finset.mem_insert_self a s))
        (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

/-- `Rval` is additive over finite sums. -/
lemma Rval_finset_sum {ι : Type*} (s : Finset ι) (g : ι → RatFunc ℂ) {z : ℂ}
    (hg : ∀ i ∈ s, Rreg (g i) z) : Rval (∑ i ∈ s, g i) z = ∑ i ∈ s, Rval (g i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Rval]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Rval_add_of (hg a (Finset.mem_insert_self a s))
          (Rreg_finset_sum s g (fun i hi => hg i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

/-- `Rval` is additive over finite sums (universe version). -/
lemma Rval_sum_of {ι : Type*} [Fintype ι] (g : ι → RatFunc ℂ) {z : ℂ}
    (hg : ∀ i, Rreg (g i) z) : Rval (∑ i, g i) z = ∑ i, Rval (g i) z := by
  simpa using Rval_finset_sum (Finset.univ) g (fun i _ => hg i)

/-- The evaluation of a quotient of polynomials. -/
lemma Rval_div_poly_of (p q : Polynomial ℂ) (z : ℂ) (hq : q.eval z ≠ 0) :
    Rval (algebraMap (Polynomial ℂ) (RatFunc ℂ) p / algebraMap (Polynomial ℂ) (RatFunc ℂ) q) z
      = p.eval z / q.eval z :=
  Rval_div p q z hq

/-! ## The expansion of the derivative of `Wev` -/

/-- The explicit expansion of `d/dz (Wev y1 J n)` at a point where every coefficient of `n` is
regular.  See `WevD_eq_deriv`. -/
def WevD {k : ℕ} (y1 : ℂ → ℂ) (J : Fin k → ℂ → ℂ) (n : W k) (z : ℂ) : ℂ :=
  Rval (dRat n.1) z * y1 z
    + Rval n.1 z * deriv y1 z
    + Rval (dRat n.2.1) z * deriv y1 z
    + Rval n.2.1 z * deriv (deriv y1) z
    + ∑ i, (Rval (dRat (n.2.2 i)) z * J i z + Rval (n.2.2 i) z * deriv (J i) z)

end

end Work.GenShared
