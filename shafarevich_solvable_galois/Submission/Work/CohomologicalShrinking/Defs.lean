/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cohomological shrinking: the refined `p`-central filtration and its graded pieces

This is the first file of the chapter `Work.CohomologicalShrinking`, which formalizes
§2 of A. Schmidt and K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*
(arXiv:math/9809211): Definition 3, Lemma 4, Proposition 5, Proposition 6 and Proposition 7.

The mathematical content of §2 is pure algebra: finite groups, `𝔽_p[G]`-modules and group
cohomology.  Nothing in this chapter uses class field theory or number theory.

## Conventions (see `NOTES.md` for the full dictionary with the paper)

* `p` is a natural number used as a prime (`[Fact p.Prime]` where needed), `G` a group.
* `Work.Shrinking.pCentralSeries p P n` is the descending `p`-central series **0-indexed**,
  so that `pCentralSeries p P n` is the paper's `P_{n+1}`; `pSeries p P i` denotes the paper's
  `P_i`, i.e. `pSeries p P i = pCentralSeries p P (i-1)`.
* `centralSeries P j` is the paper's `P^j`, the *descending central series* (lower central
  series): `P^1 = P`, `P^{j+1} = [P^j, P]`.  In Mathlib this is
  `(⊤ : Subgroup P).lowerCentralSeries (j-1)`.
* `refinedTerm p P i j` is the paper's `P_{(i,j)} = (P_i ∩ P^j) P_{i+1}`.
* `tauSucc i j` is the paper's `τ + 1`: `(i, j+1)` if `i > j`, and `(i+1, 1)` if `i = j`.
* `refinedQuotient p P i j` is the graded piece `P_{(i,j)}/P_{(i,j)+1}`.
* `E p G d i j` is that graded piece for `P = F(d)`, the free `G`-operator group of rank `d`
  (`Work.Shrinking.freeOperatorGroup G d`), written as an `𝔽_p`-vector space
  (`Additive` of the multiplicative quotient).  It is the paper's `E(d,τ)`.
* `squareQuotient p G d` is the paper's `F(d)/F(d)^2 = F(d)/F(d)_2` (`F(d)_2 = F(d)^p[F(d),F(d)]`),
  the source of Proposition 5.
-/

import Mathlib
import Submission.Work.Shrinking.Basic
import Submission.Work.Shrinking.PCentral
import Submission.Work.Shrinking.PCentralQuotient
import Submission.Work.Shrinking.Refined
import Submission.Work.Shrinking.FreeOperator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 1000000

open scoped TensorProduct

universe u v w

variable {p : ℕ}

/-! ## The index set `{(i,j) | i ≥ j ≥ 1}` and its successor function -/

/-- The successor of a pair `τ = (i,j)` with `i ≥ j ≥ 1` in the lexicographic order used by
Schmidt–Wingberg: `τ + 1 = (i, j+1)` if `i > j`, and `τ + 1 = (i+1, 1)` if `τ = (i,i)`.

The lexicographic order on `{(i,j) | i ≥ j ≥ 1}` is
`(1,1) < (2,1) < (2,2) < (3,1) < (3,2) < (3,3) < …`, and `tauSucc` is its successor
function. -/
def tauSucc (i j : ℕ) : ℕ × ℕ := if j < i then (i, j + 1) else (i + 1, 1)

@[simp] theorem tauSucc_fst (i j : ℕ) : (tauSucc i j).1 = if j < i then i else i + 1 := by
  by_cases h : j < i <;> simp [tauSucc, h]

@[simp] theorem tauSucc_snd (i j : ℕ) : (tauSucc i j).2 = if j < i then j + 1 else 1 := by
  by_cases h : j < i <;> simp [tauSucc, h]

theorem tauSucc_of_lt {i j : ℕ} (h : j < i) : tauSucc i j = (i, j + 1) := by
  simp [tauSucc, h]

theorem tauSucc_of_le {i j : ℕ} (h : i ≤ j) : tauSucc i j = (i + 1, 1) := by
  simp [tauSucc, Nat.not_lt.mpr h]

/-! ## The two series and the refinement of Definition 3 -/

/-- The paper's `P^j`: the descending central series (lower central series) of `P`,
`P^1 = P`, `P^{j+1} = [P^j, P]`.  It refines the second index of the `p`-central series. -/
abbrev centralSeries (P : Type*) [Group P] (j : ℕ) : Subgroup P :=
  (⊤ : Subgroup P).lowerCentralSeries (j - 1)

/-- The paper's `P_i`: the descending `p`-central series of `P`,
`P_1 = P`, `P_{i+1} = (P_i)^p [P_i, P]`, in the 0-indexed convention of `Work.Shrinking`. -/
abbrev pSeries (p : ℕ) (P : Type*) [Group P] (i : ℕ) : Subgroup P :=
  Work.Shrinking.pCentralSeries p P (i - 1)

@[simp] theorem centralSeries_zero (P : Type*) [Group P] : centralSeries P 0 = ⊤ := rfl

@[simp] theorem centralSeries_one (P : Type*) [Group P] : centralSeries P 1 = ⊤ := rfl

@[simp] theorem centralSeries_succ_succ (P : Type*) [Group P] (j : ℕ) :
    centralSeries P (j + 2) = ⁅centralSeries P (j + 1), ⊤⁆ := by
  rw [show centralSeries P (j + 2) = (⊤ : Subgroup P).lowerCentralSeries (j + 1) from rfl,
    show centralSeries P (j + 1) = (⊤ : Subgroup P).lowerCentralSeries j from rfl]
  exact Subgroup.lowerCentralSeries_succ ⊤ j

@[simp] theorem pSeries_zero (p : ℕ) (P : Type*) [Group P] : pSeries p P 0 = ⊤ := rfl

@[simp] theorem pSeries_one (p : ℕ) (P : Type*) [Group P] : pSeries p P 1 = ⊤ := rfl

@[simp] theorem pSeries_succ_succ (p : ℕ) (P : Type*) [Group P] (i : ℕ) :
    pSeries p P (i + 2) = Work.Shrinking.pCentralStep p (pSeries p P (i + 1)) := by
  rw [show pSeries p P (i + 2) = Work.Shrinking.pCentralSeries p P (i + 1) from rfl,
    show pSeries p P (i + 1) = Work.Shrinking.pCentralSeries p P i from rfl]
  rfl

theorem centralSeries_antitone (P : Type*) [Group P] : Antitone (centralSeries P) :=
  fun _ _ h => Subgroup.lowerCentralSeries_antitone ⊤ (Nat.sub_le_sub_right h 1)

theorem pSeries_antitone (p : ℕ) (P : Type*) [Group P] : Antitone (pSeries p P) :=
  fun _ _ h => Work.Shrinking.pCentralSeries_antitone p P (Nat.sub_le_sub_right h 1)

/-- `P_{(i,j)} = (P_i ∩ P^j) P_{i+1}`: Schmidt–Wingberg's refinement of the descending
`p`-central series (Definition 3 of arXiv:math/9809211). -/
def refinedTerm (p : ℕ) (P : Type*) [Group P] (i j : ℕ) : Subgroup P :=
  (pSeries p P i ⊓ centralSeries P j) ⊔ pSeries p P (i + 1)

/-- `P_{(i,j)} ≤ P_i`. -/
theorem refinedTerm_le_pSeries (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    refinedTerm p P i j ≤ pSeries p P i :=
  sup_le inf_le_left (pSeries_antitone p P (Nat.le_succ i))

/-- The refinement is descending in the second index: `P_{(i,j+1)} ≤ P_{(i,j)}`. -/
theorem refinedTerm_antitone_snd (p : ℕ) (P : Type*) [Group P] (i j : ℕ) :
    refinedTerm p P i (j + 1) ≤ refinedTerm p P i j :=
  sup_le_sup (inf_le_inf_left _ (centralSeries_antitone P (Nat.le_succ j))) le_rfl

/-- `P_{(i,1)} = P_i`: the refinement starts at the `p`-central series itself. -/
theorem refinedTerm_one (p : ℕ) (P : Type*) [Group P] (i : ℕ) :
    refinedTerm p P i 1 = pSeries p P i := by
  rw [refinedTerm, centralSeries_one, inf_top_eq, sup_eq_left]
  exact pSeries_antitone p P (Nat.le_succ i)

/-! ## The graded pieces -/

/-- The graded piece `P_{(i,j)}/P_{(i,j)+1}` of Schmidt–Wingberg's refinement. -/
abbrev refinedQuotient (p : ℕ) (P : Type*) [Group P] (i j : ℕ) : Type _ :=
  refinedTerm p P i j ⧸
    (refinedTerm p P (tauSucc i j).1 (tauSucc i j).2).subgroupOf (refinedTerm p P i j)

/-- The paper's `F(d)/F(d)^2`: the quotient of the free `G`-operator group of rank `d` by
`F(d)^p [F(d),F(d)]`, i.e. by the second term of its descending `p`-central series, written as
an `𝔽_p`-vector space.  This is the source of the maps of Proposition 5. -/
abbrev squareQuotient (p : ℕ) (G : Type*) [Group G] (d : ℕ) : Type _ :=
  Additive (Work.Shrinking.pCentralQuotient p (Work.Shrinking.freeOperatorGroup G d) 0)

/-- The paper's `E(d,τ) = F(d)_{(i,j)}/F(d)_{(i,j)+1}`: the graded piece of the refined
filtration of the free `G`-operator group of rank `d`, as an `𝔽_p`-vector space. -/
abbrev E (p : ℕ) (G : Type*) [Group G] (d i j : ℕ) : Type _ :=
  Additive (refinedQuotient p (Work.Shrinking.freeOperatorGroup G d) i j)

end Work.CohomologicalShrinking
