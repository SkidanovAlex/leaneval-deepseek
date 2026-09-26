import Submission.Work.StrictDescent
import Submission.Work.NielsenResidual
import Submission.Work.ImageAggregate
import Submission.Work.AggregateProtocol
import Submission.Work.AggregateDispatch
import Submission.Work.StrictAttach
import Submission.Work.SystemReducedImage

open Submission.FreeGroupAut
open FreeGroup
set_option autoImplicit false

/-!
# The residual (NoEndCancel) state always has an exactly-half-absorbed element

**L1 of the Fall-II run.**  The rebalancing run (`StrictDescent.lean`'s pin
`hF`, classical Nielsen 1919 pp. 270-271) iterates over residual states — a
basis state in which *no* single elementary right-composition strictly
decreases the total length (`NielsenResidual.NoEndCancel`, a local minimum of
`N`).  This module proves that a *residual* state with a long basis image
always has a **Fall-II configuration** (`FallTwoConfig`): a confined interior
factor of the image aggregate of some standard generator whose word is
`A ++ B` (`|A| = |B|`) with the two neighbours covering exactly the two
halves.  Chain of existing results used:

* `exists_two_factor_letter` + `aggregate_confined_factor` (T1,
  general-`k`): some standard generator `a_m` has an aggregate with a
  confined factor `j`;
* `aggregate_element_dichotomy` / `confined_zero_strict` /
  `confined_last_strict`: a confined factor (boundary or interior) whose
  junction product is strictly shorter than a neighbouring factor (the
  Fall-I/strict phase) yields a *single elementary move* strictly decreasing
  `N` — **impossible under `NoEndCancel`** (`noEndCancel_*_strict` below
  contradict the strict junction inequalities directly with the
  `NoEndCancel` conjuncts);
* so only the balanced (Fall-II) disjunct survives, giving `FallTwoConfig α`,
  and `StrictDescent.fallTwoConfig_to_state` packages it as an ordered state
  `S` (`S.α = α`) with an exactly-half-absorbed row position `p`
  (`ExactlyHalfAbsorbed S p`).

This is the state-level existence half of the classical "some element is
absorbed between two others" step (machine-validated: every residual
non-letter basis state has a balanced element, 455/455 at n = 3, 351/351 at
n = 4 — `/tmp/fg2`, `valL1.py`); it lets the residual run always continue to
a next balanced element.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

open scoped BigOperators

/-- **A `NoEndCancel` state has no strictly shortening product at a left
junction.**  If `x = ±w_p`, `y = ±w_q` (`p ≠ q`) and `|x·y| < |x|`, the four
sign cases each contradict one of the four `NoEndCancel` conjuncts (with the
inverse-of-the-product identities when the first factor is `w_p⁻¹`).  This is
the word-level content that the Fall-I strict phase (a single elementary
move strictly decreasing `N`) cannot fire in a residual state. -/
theorem noEndCancel_no_left_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hnec : NoEndCancel n α) {p q : Fin n} (hpq : p ≠ q)
    {x y : FreeGroup (Fin n)}
    (hx : x = α (FreeGroup.of p) ∨ x = (α (FreeGroup.of p))⁻¹)
    (hy : y = α (FreeGroup.of q) ∨ y = (α (FreeGroup.of q))⁻¹)
    (hshort : FreeGroup.norm (x * y) < FreeGroup.norm x) : False := by
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · -- x = w_p, y = w_q : |w_p·w_q| < |w_p| contradicts |w_p| ≤ |w_p·w_q|
      have h2 : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of q))
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        rw [hx, hy] at hshort
        exact hshort
      exact (not_lt_of_ge (hnec p q hpq).2.1) h2
    · -- x = w_p, y = w_q⁻¹ : |w_p·w_q⁻¹| < |w_p| contradicts |w_p| ≤ |w_p·w_q⁻¹|
      have h1 : FreeGroup.norm (α (FreeGroup.of p) * (α (FreeGroup.of q))⁻¹)
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        rw [hx, hy] at hshort
        exact hshort
      exact (not_lt_of_ge (hnec p q hpq).1) h1
  · rcases hy with hy | hy
    · -- x = w_p⁻¹, y = w_q : |w_p⁻¹·w_q| < |w_p| ; inverse gives |w_q⁻¹·w_p| < |w_p|
      have hs : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of q))
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        rw [hx, hy] at hshort
        rwa [norm_inv_eq] at hshort
      have h3 : FreeGroup.norm ((α (FreeGroup.of q))⁻¹ * α (FreeGroup.of p))
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        have hflip : FreeGroup.norm ((α (FreeGroup.of q))⁻¹ * α (FreeGroup.of p)) =
            FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of q)) := by
          simpa using (norm_mul_flip (a := (α (FreeGroup.of p))⁻¹)
            (b := α (FreeGroup.of q))).symm
        rw [hflip]
        exact hs
      exact (not_lt_of_ge (hnec p q hpq).2.2.1) h3
    · -- x = w_p⁻¹, y = w_q⁻¹ : |w_p⁻¹·w_q⁻¹| < |w_p| ; inverse gives |w_q·w_p| < |w_p|
      have hs : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of q))⁻¹)
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        rw [hx, hy] at hshort
        rwa [norm_inv_eq] at hshort
      have h4 : FreeGroup.norm (α (FreeGroup.of q) * α (FreeGroup.of p))
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        have hflip : FreeGroup.norm (α (FreeGroup.of q) * α (FreeGroup.of p)) =
            FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of q))⁻¹) :=
          norm_mul_flip (a := α (FreeGroup.of q)) (b := α (FreeGroup.of p))
        rw [hflip]
        exact hs
      exact (not_lt_of_ge (hnec p q hpq).2.2.2) h4

/-- **A `NoEndCancel` state has no strictly shortening product at a right
junction.**  Mirror of `noEndCancel_no_left_strict` with the *right* factor
shortened: if `x = ±w_p`, `y = ±w_q` (`p ≠ q`) and `|x·y| < |y|`, the four
sign cases contradict the `NoEndCancel` conjuncts at the shortened
coordinate `q` (the conjuncts paired with `p`). -/
theorem noEndCancel_no_right_strict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hnec : NoEndCancel n α) {p q : Fin n} (hpq : p ≠ q)
    {x y : FreeGroup (Fin n)}
    (hx : x = α (FreeGroup.of p) ∨ x = (α (FreeGroup.of p))⁻¹)
    (hy : y = α (FreeGroup.of q) ∨ y = (α (FreeGroup.of q))⁻¹)
    (hshort : FreeGroup.norm (x * y) < FreeGroup.norm y) : False := by
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · -- x = w_p, y = w_q : |w_p·w_q| < |w_q| contradicts |w_q| ≤ |w_p·w_q|
      have h4 : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of q))
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        rw [hx, hy] at hshort
        exact hshort
      exact (not_lt_of_ge (hnec q p (fun h => hpq h.symm)).2.2.2) h4
    · -- x = w_p, y = w_q⁻¹ : |w_p·w_q⁻¹| < |w_q| ; inverse/flip gives |w_q·w_p⁻¹| < |w_q|
      have hs : FreeGroup.norm (α (FreeGroup.of p) * (α (FreeGroup.of q))⁻¹)
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        rw [hx, hy] at hshort
        rwa [norm_inv_eq] at hshort
      have h1 : FreeGroup.norm (α (FreeGroup.of q) * (α (FreeGroup.of p))⁻¹)
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        have hflip : FreeGroup.norm (α (FreeGroup.of q) * (α (FreeGroup.of p))⁻¹) =
            FreeGroup.norm (α (FreeGroup.of p) * (α (FreeGroup.of q))⁻¹) := by
          simpa using (norm_mul_flip (a := α (FreeGroup.of p))
            (b := (α (FreeGroup.of q))⁻¹)).symm
        rw [hflip]
        exact hs
      exact (not_lt_of_ge (hnec q p (fun h => hpq h.symm)).1) h1
  · rcases hy with hy | hy
    · -- x = w_p⁻¹, y = w_q : |w_p⁻¹·w_q| < |w_q| contradicts |w_q| ≤ |w_p⁻¹·w_q|
      have h3 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of q))
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        rw [hx, hy] at hshort
        exact hshort
      exact (not_lt_of_ge (hnec q p (fun h => hpq h.symm)).2.2.1) h3
    · -- x = w_p⁻¹, y = w_q⁻¹ : |w_p⁻¹·w_q⁻¹| < |w_q| ; inverse/flip gives |w_q·w_p| < |w_q|
      have hs : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of q))⁻¹)
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        rw [hx, hy] at hshort
        rwa [norm_inv_eq] at hshort
      have h2 : FreeGroup.norm (α (FreeGroup.of q) * α (FreeGroup.of p))
          < FreeGroup.norm (α (FreeGroup.of q)) := by
        have hflip : FreeGroup.norm (α (FreeGroup.of q) * α (FreeGroup.of p)) =
            FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of q))⁻¹) :=
          norm_mul_flip (a := α (FreeGroup.of q)) (b := α (FreeGroup.of p))
        rw [hflip]
        exact hs
      exact (not_lt_of_ge (hnec q p (fun h => hpq h.symm)).2.1) h2

/-- **L1: a residual state with a long basis image has a Fall-II
configuration.**  `NoEndCancel α` (no single elementary strict move) with a
basis image of reduced length ≥ 2: the aggregate analysis
(`exists_two_factor_letter`, `aggregate_confined_factor`,
`aggregate_element_dichotomy` / the boundary `confined_*_strict` junctions)
yields a confined factor whose only surviving disjunct is the balanced one —
the strict (Fall-I) disjuncts contradict `NoEndCancel`
(`noEndCancel_no_left_strict` / `noEndCancel_no_right_strict`).  So some
standard generator `a_m` has a confined interior factor `j` with word
`A ++ B` (`|A| = |B|`), the left neighbour `X ++ invRev A`, the right
neighbour `invRev B ++ Z`. -/
theorem residual_has_fallTwo {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hnec : NoEndCancel n α)
    (hlong : ∃ i : Fin n, 1 < FreeGroup.norm (α (FreeGroup.of i))) :
    FallTwoConfig α := by
  classical
  rcases exists_two_factor_letter α hlong with ⟨m, hlen⟩
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have hk : 2 ≤ es.length := by
    dsimp [es]
    rw [imageAggregate_length]
    exact hlen
  have hprod : es.prod = FreeGroup.of m := by
    dsimp [es]
    exact imageAggregate_prod_letter α m
  have himg : ImageAggregate α es := by
    dsimp [es]
    exact imageAggregate_isImageAggregate α m
  have hred : SystemReduced es := by
    dsimp [es]
    exact SystemReduced_imageAggregate α m
  rcases aggregate_confined_factor es m hprod hk with ⟨j, hj, hconf⟩
  by_cases hj0 : 0 < j
  · by_cases hjk : j + 1 < es.length
    · -- interior confined factor j
      have hm : j - 1 < es.length := by omega
      rcases aggregate_element_dichotomy es hj hj0 hjk hm hconf with hsL | hsR | hbal
      · -- strict left junction: contradict NoEndCancel
        rcases aggregate_factor_coordinate α es himg hm with ⟨p, hp⟩
        rcases aggregate_factor_coordinate α es himg hj with ⟨q, hq⟩
        have hpq : p ≠ q := strict_left_coord_ne α es hred hj hj0 hm hp hq hsL
        exact False.elim (noEndCancel_no_left_strict α hnec hpq hp hq hsL)
      · -- strict right junction: contradict NoEndCancel
        rcases aggregate_factor_coordinate α es himg hj with ⟨p, hp⟩
        rcases aggregate_factor_coordinate α es himg hjk with ⟨q, hq⟩
        have hpq : p ≠ q := strict_right_coord_ne α es hred hj hjk hp hq hsR
        exact False.elim (noEndCancel_no_right_strict α hnec hpq hp hq hsR)
      · -- balanced (Fall-II) content
        refine ⟨m, j, ?hjE, hj0, hjk, ?hconfE, ?_⟩
        · simpa [es] using hj
        · simpa [es] using hconf
        · rcases hbal with ⟨A, B, X, Z, hA, hAB, hX, hZ⟩
          refine ⟨A, B, X, Z, ?_, hAB, ?_, ?_⟩
          · simpa [es] using hA
          · simpa [es] using hX
          · simpa [es] using hZ
    · -- right boundary factor (j + 1 = es.length): confined_last_strict
      -- gives |es[j-1]·es[j]| < |es[j-1]| — contradicts NoEndCancel
      exfalso
      have hm : j - 1 < es.length := by omega
      have hstrict : FreeGroup.norm (es[j - 1] * es[j]) < FreeGroup.norm (es[j - 1]) := by
        simpa [es] using (confined_last_strict es hred hk hj (by omega) (by simpa [es] using hconf))
      rcases aggregate_factor_coordinate α es himg hm with ⟨p, hp⟩
      rcases aggregate_factor_coordinate α es himg hj with ⟨q, hq⟩
      have hpq : p ≠ q := strict_left_coord_ne α es hred hj (by omega) hm hp hq hstrict
      exact noEndCancel_no_left_strict α hnec hpq hp hq hstrict
  · -- left boundary factor (j = 0): confined_zero_strict gives
    -- |es[0]·es[1]| < |es[1]| — contradicts NoEndCancel
    exfalso
    have hjz : j = 0 := by omega
    subst j
    have hb1 : 1 < es.length := by omega
    have hstrict : FreeGroup.norm ((es[0]) * (es[1])) < FreeGroup.norm (es[1]) :=
      confined_zero_strict es hred hk hconf
    rcases aggregate_factor_coordinate α es himg hj with ⟨p, hp⟩
    rcases aggregate_factor_coordinate α es himg hb1 with ⟨q, hq⟩
    have hpq : p ≠ q := strict_right_coord_ne α es hred hj hb1 hp hq hstrict
    exact noEndCancel_no_right_strict α hnec hpq hp hq hstrict

/-- **L1, state level: a residual non-letter state has an exactly-half-absorbed
element.**  From `residual_has_fallTwo` the Fall-II configuration packages as
an ordered state `S` (`S.α = α`, `ExactlyHalfAbsorbed S p` via
`fallTwoConfig_to_state`).  This is the state-level existence half of the
classical step — the residual run can always continue to a balanced row. -/
theorem residual_state_balanced_exists {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hnec : NoEndCancel n α)
    (hlong : ∃ i : Fin n, 1 < FreeGroup.norm (α (FreeGroup.of i))) :
    ∃ S : RebalanceState n, S.α = α ∧ ∃ p : Fin n, ExactlyHalfAbsorbed S p := by
  exact fallTwoConfig_to_state α (residual_has_fallTwo α hnec hlong)

end Submission.Nielsen
