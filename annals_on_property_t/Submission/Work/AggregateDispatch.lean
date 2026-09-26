import Submission.Work.NormSelf
import Submission.Work.StrictAttach
import Submission.Work.AggregateCoordinate

open FreeGroup
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# Aggregate → move: the strict/balanced dispatch of a confined factor

`ImageAggregate.aggregate_element_dichotomy` analyses a confined interior
factor of an image aggregate: either a product of two adjacent factors is
*strictly* shorter than one of them (the strict phase), or the balanced
half-half state holds.  This module *dispatches* that dichotomy to the level
of closure moves:

* every factor of the aggregate is a basis image up to sign
  (`ImageAggregate`), so the two factors of a strict junction are `±w_p`,
  `±w_q`;
* the two coordinates are distinct: `p = q` would make the strict inequality
  impossible — in the same-sign cases by `|x·x| ≥ |x|`
  (`NormSelf.norm_mul_self_ge`), in the mixed-sign cases by the adjacent
  inverse pair being forbidden (`SystemReduced`);
* `StrictAttach.strict_attach_left/right` then realise the strict inequality
  as right composition by the corresponding elementary move: `∃ γ ∈ AutClosure
  n, N (α·γ) < N α`.

The assembled theorem `confined_factor_dispatch` states the whole content of
the dichotomy at the *system* level: from a confined interior factor of an
image aggregate `es` (with `ImageAggregate` and `SystemReduced`), either a
single closure move strictly decreases `N`, or the balanced content
(`es[j] = A ++ B`, `|A| = |B|`, neighbours covering the two halves) holds —
exactly the two-phase input of the reduction protocol (strict phase / T3
rebalancing).

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

private lemma getElem_index_congr {α : Type*} {l : List α} {i j : ℕ} (h : i = j)
    (hi : i < l.length) (hj : j < l.length) : l[i]'(hi) = l[j]'(hj) := by
  subst j
  rfl

/-- A `SystemReduced` factor list cannot contain an adjacent inverse pair at
the junction `(j-1, j)`. -/
private lemma adj_inv_forbidden_left {n : ℕ} (es : List (FreeGroup (Fin n)))
    (hred : SystemReduced es) {j : ℕ} (hj : j < es.length) (hj0 : 0 < j)
    (hm : j - 1 < es.length) (h : es[j]'(hj) = (es[j - 1]'(hm))⁻¹) : False := by
  have hi : (j - 1) + 1 < es.length := by omega
  have hne := hred.2 (j - 1) hi
  have hcong : es[(j - 1) + 1]'(hi) = es[j]'(hj) := by
    exact getElem_index_congr (l := es) (i := (j - 1) + 1) (j := j) (by omega) hi hj
  have h2 : es[(j - 1) + 1]'(hi) = (es[j - 1]'(hm))⁻¹ := hcong.trans h
  exact hne h2

/-- A `SystemReduced` factor list cannot contain an adjacent inverse pair at
the junction `(j, j+1)`. -/
private lemma adj_inv_forbidden_right {n : ℕ} (es : List (FreeGroup (Fin n)))
    (hred : SystemReduced es) {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (h : es[j + 1]'(hjk) = (es[j]'(hj))⁻¹) : False := by
  have hne := hred.2 j hjk
  exact hne h

/-- **Left strict junction: distinct coordinates.**  If `es[j-1]` and `es[j]`
are basis images up to sign and their product is strictly shorter than
`es[j-1]`, then the two coordinates are different: `p = q` would make the two
factors the same basis image up to sign — the same-sign cases contradict
`|x·x| ≥ |x|`, the mixed-sign cases are an adjacent inverse pair forbidden by
`SystemReduced`. -/
theorem strict_left_coord_ne {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hm : j - 1 < es.length)
    {p q : Fin n}
    (hp : es[j - 1] = α (FreeGroup.of p) ∨ es[j - 1] = (α (FreeGroup.of p))⁻¹)
    (hq : es[j] = α (FreeGroup.of q) ∨ es[j] = (α (FreeGroup.of q))⁻¹)
    (hstrict : FreeGroup.norm ((es[j - 1]) * (es[j])) < FreeGroup.norm (es[j - 1])) :
    p ≠ q := by
  intro hpq
  subst q
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · -- (+, +): es[j-1] = es[j] = w_p; |w_p·w_p| < |w_p| contradicts |x·x| ≥ |x|
      have hlt : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of p)))
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        rw [hp, hq] at hstrict
        exact hstrict
      exact (not_lt_of_ge (norm_mul_self_ge (α (FreeGroup.of p)))) hlt
    · -- (+, −): es[j] = w_p⁻¹ = (es[j-1])⁻¹ : adjacent inverse pair
      have h : es[j]'(hj) = (es[j - 1]'(hm))⁻¹ := by
        calc
          es[j]'(hj) = (α (FreeGroup.of p))⁻¹ := hq
          _ = (es[j - 1]'(hm))⁻¹ := by rw [hp]
      exact adj_inv_forbidden_left es hred hj hj0 hm h
  · rcases hq with hq | hq
    · -- (−, +): es[j] = w_p = (es[j-1])⁻¹ : adjacent inverse pair
      have h : es[j]'(hj) = (es[j - 1]'(hm))⁻¹ := by
        calc
          es[j]'(hj) = α (FreeGroup.of p) := hq
          _ = (es[j - 1]'(hm))⁻¹ := by
                rw [hp]
                simp
      exact adj_inv_forbidden_left es hred hj hj0 hm h
    · -- (−, −): es[j-1] = es[j] = w_p⁻¹; |w_p⁻¹·w_p⁻¹| < |w_p⁻¹| contradicts |x·x| ≥ |x|
      have hlt : FreeGroup.norm (((α (FreeGroup.of p))⁻¹) * ((α (FreeGroup.of p))⁻¹))
          < FreeGroup.norm ((α (FreeGroup.of p))⁻¹) := by
        rw [hp, hq] at hstrict
        exact hstrict
      exact (not_lt_of_ge (norm_mul_self_ge ((α (FreeGroup.of p))⁻¹))) hlt

/-- **Right strict junction: distinct coordinates.**  Mirror of
`strict_left_coord_ne` at `(es[j], es[j+1])`. -/
theorem strict_right_coord_ne {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    {p q : Fin n}
    (hp : es[j] = α (FreeGroup.of p) ∨ es[j] = (α (FreeGroup.of p))⁻¹)
    (hq : es[j + 1] = α (FreeGroup.of q) ∨ es[j + 1] = (α (FreeGroup.of q))⁻¹)
    (hstrict : FreeGroup.norm ((es[j]) * (es[j + 1])) < FreeGroup.norm (es[j + 1])) :
    p ≠ q := by
  intro hpq
  subst q
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · -- (+, +)
      have hlt : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of p)))
          < FreeGroup.norm (α (FreeGroup.of p)) := by
        rw [hp, hq] at hstrict
        exact hstrict
      exact (not_lt_of_ge (norm_mul_self_ge (α (FreeGroup.of p)))) hlt
    · -- (+, −): es[j+1] = w_p⁻¹ = (es[j])⁻¹
      have h : es[j + 1]'(hjk) = (es[j]'(hj))⁻¹ := by
        calc
          es[j + 1]'(hjk) = (α (FreeGroup.of p))⁻¹ := hq
          _ = (es[j]'(hj))⁻¹ := by rw [hp]
      exact adj_inv_forbidden_right es hred hj hjk h
  · rcases hq with hq | hq
    · -- (−, +): es[j+1] = w_p = (es[j])⁻¹
      have h : es[j + 1]'(hjk) = (es[j]'(hj))⁻¹ := by
        calc
          es[j + 1]'(hjk) = α (FreeGroup.of p) := hq
          _ = (es[j]'(hj))⁻¹ := by
                rw [hp]
                simp
      exact adj_inv_forbidden_right es hred hj hjk h
    · -- (−, −)
      have hlt : FreeGroup.norm (((α (FreeGroup.of p))⁻¹) * ((α (FreeGroup.of p))⁻¹))
          < FreeGroup.norm ((α (FreeGroup.of p))⁻¹) := by
        rw [hp, hq] at hstrict
        exact hstrict
      exact (not_lt_of_ge (norm_mul_self_ge ((α (FreeGroup.of p))⁻¹))) hlt

/-- **Strict-left dispatch.**  A confined factor whose left junction product
is strictly shorter than the left factor is shortened by a single elementary
move: the two factors are `±w_p`, `±w_q` with `p ≠ q`, so
`strict_attach_left` supplies `γ ∈ AutClosure n` with `N (α·γ) < N α`. -/
theorem confined_strict_left_move {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (himg : ImageAggregate α es)
    (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hm : j - 1 < es.length)
    (hstrict : FreeGroup.norm ((es[j - 1]) * (es[j])) < FreeGroup.norm (es[j - 1])) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  rcases aggregate_factor_coordinate α es himg hm with ⟨p, hp⟩
  rcases aggregate_factor_coordinate α es himg hj with ⟨q, hq⟩
  have hneq : p ≠ q := strict_left_coord_ne α es hred hj hj0 hm hp hq hstrict
  exact strict_attach_left α es hj hm hneq hp hq hstrict

/-- **Strict-right dispatch.**  Mirror of `confined_strict_left_move` at the
junction `(es[j], es[j+1])`: the strictly shortening product shortens the
*right* factor, and the corresponding elementary move gives
`N (α·γ) < N α`. -/
theorem confined_strict_right_move {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (himg : ImageAggregate α es)
    (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (hstrict : FreeGroup.norm ((es[j]) * (es[j + 1])) < FreeGroup.norm (es[j + 1])) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α := by
  rcases aggregate_factor_coordinate α es himg hj with ⟨p, hp⟩
  rcases aggregate_factor_coordinate α es himg hjk with ⟨q, hq⟩
  have hneq : p ≠ q := strict_right_coord_ne α es hred hj hjk hp hq hstrict
  exact strict_attach_right α es hj hjk hneq hp hq hstrict

/-- **The confined-factor dispatch (system level).**  For a confined interior
factor of an image aggregate, either the strict phase holds — a single
elementary closure move strictly decreases `N` (`∃ γ ∈ AutClosure n,
N (α·γ) < N α`) — or the balanced (Fall II) content holds: the balanced
factor's word splits `es[j] = A ++ B` (`|A| = |B|`), the left neighbour's
word is `X ++ invRev A` and the right neighbour's is `invRev B ++ Z` (each
neighbour covers exactly its half).  This is the two-phase input of the
reduction protocol. -/
theorem confined_factor_dispatch {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (himg : ImageAggregate α es)
    (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hjk : j + 1 < es.length)
    (hm : j - 1 < es.length) (hconf : Confined (aggregateWords es) j) :
    (∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ N (α * γ) < N α) ∨
    (∃ (A B X Z : List (Fin n × Bool)),
      (es[j]).toWord = A ++ B ∧ A.length = B.length ∧
      (es[j - 1]).toWord = X ++ FreeGroup.invRev A ∧
      (es[j + 1]).toWord = FreeGroup.invRev B ++ Z) := by
  rcases aggregate_element_dichotomy es hj hj0 hjk hm hconf with hsL | hsR | hbal
  · left
    exact confined_strict_left_move α es himg hred hj hj0 hm hsL
  · left
    exact confined_strict_right_move α es himg hred hj hjk hsR
  · right
    exact hbal

end Submission.Nielsen
