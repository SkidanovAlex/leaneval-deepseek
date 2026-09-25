import Mathlib
import Submission.Work.HopfGaschutz.Defs
import Submission.Work.HopfGaschutz.Setup

/-!
# Finiteness of the relation-Frattini quotient `K ⧸ K²[K,F]`

**Module** `Submission.Work.HopfGaschutz.finite_quotient_relFrattiniIn`.

For a finite-index normal subgroup `K` of a finitely generated free group `F = FreeGroup α`,
this file proves that the *relation-Frattini quotient*

  `K ⧸ K²[K,F]`

is **finite**.  Here `K² [K,F] = relFrattini 2 K = pPower 2 K ⊔ ⁅K,⊤⁆` (see
`Work.HopfGaschutz.Defs`); the quotient is the (dual of the) transgression image of the
presentation `1 → K → F → Q → 1`, i.e. the space in which the relation rank
`dim_{𝔽₂} H²(Q,𝔽₂)` of the finite quotient `Q = F/K` lives.

## The mathematics

`K ⧸ K²[K,F]` is an *elementary abelian* 2-group, i.e. an abelian group of exponent dividing
`2`:

* it is abelian because `[K,K] ≤ [K,F] = ⁅K,⊤⁆ ≤ K²[K,F]`;
* every element has order dividing `2` because `K² ≤ K²[K,F]`.

Moreover it is finitely generated: `K` is, by Schreier's lemma
(`Subgroup.fg_of_index_ne_zero`) applied to the finite-index subgroup `K` of the finitely
generated group `FreeGroup α` (`α` finite).  A finitely generated abelian group of exponent
dividing `2` is finite -- this is `card_dvd_exponent_pow_rank'`
(`Nat.card G ∣ n ^ Group.rank G` for a commutative f.g. group with `g ^ n = 1` for all `g`),
applied with `n = 2`.

Note that *no hypothesis* is placed on `Q` other than finiteness -- in particular `Q` need not
be a `2`-group, and the statement is even true for the trivial group (`α` empty, or `Q`
trivial).

## Main results

* `Work.HopfGaschutz.finite_quotient_relFrattiniIn_of_finiteIndex` -- the general form, for an
  arbitrary finite-index normal subgroup `K ≤ FreeGroup α`;
* `Work.HopfGaschutz.finite_quotient_relFrattiniIn` -- the requested form, for the presentation
  kernel `K = presKernel gen` of a surjective generating family `gen : α → Q` of a finite group
  `Q`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped IsMulCommutative
open scoped commutatorElement

namespace Work.HopfGaschutz

variable {α : Type*}

/-- **Finiteness of the relation-Frattini quotient.**  For a finite-index normal subgroup `K` of
a finitely generated free group, the elementary abelian 2-group `K ⧸ K²[K,F]` is finite.

This is the relation-rank space of the presentation `1 → K → FreeGroup α → Q → 1` (`Q = F/K`
finite): it is abelian of exponent `2` (because `[K,K] ≤ [K,F] ≤ K²[K,F]` and `K² ≤ K²[K,F]`)
and finitely generated (Schreier's lemma: `K` is a finite-index subgroup of the f.g. group
`FreeGroup α`), and a finitely generated abelian group of exponent dividing `2` is finite. -/
theorem finite_quotient_relFrattiniIn_of_finiteIndex [Fintype α]
    (K : Subgroup (FreeGroup α)) [K.Normal] [K.FiniteIndex] :
    Finite (↥K ⧸ relFrattiniIn 2 K) := by
  classical
  -- `FreeGroup α` is finitely generated, `α` being finite.
  haveI hfgF : Group.FG (FreeGroup α) := by
    rw [Group.fg_iff]
    exact ⟨Set.range FreeGroup.of, FreeGroup.closure_range_of α, Set.finite_range _⟩
  -- Schreier's lemma: the finite-index subgroup `K` is finitely generated.
  haveI hfgK : Group.FG ↥K := Subgroup.fg_of_index_ne_zero K
  -- `K²[K,F]` contains the commutator subgroup of `K`, so `K ⧸ K²[K,F]` is commutative.
  have hcomm : commutator ↥K ≤ relFrattiniIn 2 K := by
    show ⁅⊤, ⊤⁆ ≤ relFrattiniIn 2 K
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [mem_relFrattiniIn]
    show ⁅(x : FreeGroup α), (y : FreeGroup α)⁆ ∈ relFrattini 2 K
    exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top y))
  haveI : IsMulCommutative (↥K ⧸ relFrattiniIn 2 K) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  -- A quotient of a finitely generated group is finitely generated.
  haveI : Group.FG (↥K ⧸ relFrattiniIn 2 K) :=
    Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  -- `K²` is killed, so every element of the quotient has order dividing `2`.
  have hsq : ∀ x : (↥K ⧸ relFrattiniIn 2 K), x ^ 2 = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (relFrattiniIn 2 K) x
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [mem_relFrattiniIn]
    show (y : FreeGroup α) ^ 2 ∈ relFrattini 2 K
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨(y : FreeGroup α), y.2, rfl⟩)
  -- A finitely generated commutative group of exponent dividing `2` is finite.
  have hcard := card_dvd_exponent_pow_rank' _ (n := 2) hsq
  exact Nat.finite_of_card_ne_zero (Nat.pos_of_dvd_of_pos hcard (pow_pos (by norm_num) _)).ne'

/-- The relation-Frattini quotient of the presentation kernel of a surjective generating family
`gen : α → Q` of a finite group `Q` is finite.

The kernel `K = presKernel gen = ker (FreeGroup.lift gen)` has finite index in `FreeGroup α`
(`FreeGroup α ⧸ K ≃* Q`), so `finite_quotient_relFrattiniIn_of_finiteIndex` applies. -/
theorem finite_quotient_relFrattiniIn {α Q : Type*} [Group Q] [Fintype α] [Fintype Q]
    (gen : α → Q) (hgen : Function.Surjective gen) :
    Finite (↥(Work.HopfGaschutz.presKernel gen) ⧸
      Work.HopfGaschutz.relFrattiniIn 2 (Work.HopfGaschutz.presKernel gen)) := by
  haveI hquot : Finite (FreeGroup α ⧸ presKernel gen) :=
    Finite.of_equiv Q (QuotientGroup.quotientKerEquivOfSurjective (FreeGroup.lift gen)
      (FreeGroup.lift_surjective_of_surjective hgen)).symm.toEquiv
  haveI : (presKernel gen).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact finite_quotient_relFrattiniIn_of_finiteIndex (presKernel gen)

end Work.HopfGaschutz
