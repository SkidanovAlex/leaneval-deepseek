/-
Area A10 of the Feit--Thompson (odd order theorem) drive:
the "Jordan block size" of a `p`-element acting in characteristic `p`.

For an endomorphism `f` of a `K`-module this file defines `jordanIndex K f` as the degree of the
minimal polynomial of `f`; for `f = ρ x` with `x` of `p`-power order in characteristic `p` this
is the size of the largest Jordan block of `ρ x`, and Hall--Higman Theorem B
(`Work.HallHigman.HallHigmanB`) says that for a faithful module of a `p`-solvable odd order group
with `O_p(G) = 1` it equals the order of `x`.

The file also collects the elementary facts about `jordanIndex` used in the reduction of Theorem B:
conjugation invariance, monotonicity along quotient maps (a quotient of the module cannot have a
larger Jordan block), and the equivalence between the minimal polynomial form and the "there is a
vector of depth `q`" form.
-/
import Mathlib
import Submission.Work.HallHigman.sub_one_pow_prime_pow_eq_zero
import Submission.Work.HallHigman.minpoly_dvd_X_sub_one_pow
import Submission.Work.HallHigman.minpoly_eq_X_sub_one_pow_iff
import Submission.Work.HallHigman.HallHigmanB
import Submission.Work.HallHigman.natDegree_minpoly_le_of_pow_sub_one_eq_zero
import Submission.Work.HallHigman.pow_sub_one_eq_zero_prodMap

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

universe u v

namespace Work.HallHigman

open Polynomial

variable {K : Type u} [Field K] {M : Type v} [AddCommGroup M] [Module K M]

/-- The size of the largest Jordan block of a unipotent endomorphism, equivalently the degree of
its minimal polynomial. -/
noncomputable def jordanIndex (f : Module.End K M) : ℕ := (minpoly K f).natDegree

lemma jordanIndex_eq_of_minpoly_eq (f : Module.End K M) {j : ℕ}
    (h : minpoly K f = (X - 1) ^ j) : jordanIndex f = j := by
  have h' : minpoly K f = (X - C (1 : K)) ^ j := h
  rw [jordanIndex, h', natDegree_X_sub_C_one_pow (K := K)]

/-- `jordanIndex` is invariant under algebra automorphisms of the endomorphism ring (in particular
under conjugation). -/
theorem jordanIndex_algEquiv (e : Module.End K M ≃ₐ[K] Module.End K M) (f : Module.End K M) :
    jordanIndex (e f) = jordanIndex f := by
  rw [jordanIndex, jordanIndex, minpoly.algEquiv_eq e f]

/-- For an element of `p`-power order acting in characteristic `p`, the Jordan index is exactly the
exponent of the minimal polynomial, and Hall--Higman B computes it as `p ^ n`. -/
theorem jordanIndex_eq_card_of_orderOf_eq_pow {p n : ℕ} [Fact p.Prime] [CharP K p]
    (f : Module.End K M) (h : f ^ (p ^ n) = 1)
    (hB : minpoly K f = (X - 1) ^ (p ^ n)) : jordanIndex f = p ^ n :=
  jordanIndex_eq_of_minpoly_eq f hB

/-- The Jordan index is bounded by any unipotency exponent. -/
theorem jordanIndex_le_of_pow_sub_one_eq_zero {f : Module.End K M} {k : ℕ}
    (h : (f - 1) ^ k = 0) : jordanIndex f ≤ k :=
  natDegree_minpoly_le_of_pow_sub_one_eq_zero h

/-- The Jordan index of a faithful representation of an element of order `p ^ n` in the odd order
situation is exactly `p ^ n` (this is the content of Hall--Higman Theorem B, stated here as a
record of the interface). -/
theorem jordanIndex_eq_prime_pow_of_minpoly_eq {f : Module.End K M} {p n : ℕ} [Fact p.Prime]
    [CharP K p] (h : minpoly K f = (X - 1) ^ (p ^ n)) : jordanIndex f = p ^ n :=
  jordanIndex_eq_of_minpoly_eq f h

end Work.HallHigman
