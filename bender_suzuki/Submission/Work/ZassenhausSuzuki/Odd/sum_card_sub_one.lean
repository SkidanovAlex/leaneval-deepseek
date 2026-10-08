import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.isCZ_basic
import Submission.Work.ZassenhausSuzuki.Odd.eq_of_mem_FinsetCZ
import Submission.Work.ZassenhausSuzuki.Odd.SRodd_iff_mem_FinsetCZ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.Odd.sum_card_sub_one`

Suzuki's first counting law for the `Sz(q)` configuration (Huppert–Blackburn XI.11.6 (a), the
element count of Suzuki 1962 §10), in the form used to force the set of odd-order elements that
are *not* strongly real to be empty:

`Σ_{A ∈ ℱ} (|A| - 1) + 1 = #{x : G // x strongly real of odd order}`.

Here `ℱ = FinsetCZ` is the family of centralisers `C_G(x)` of the non-identity strongly real
elements `x` with `x² ≠ 1`.  By `isCZ_basic` every `A ∈ ℱ` is abelian of odd order and every
`a ∈ A`, `a ≠ 1` is again strongly real with `C_G(a) = A`.  Hence

* a non-identity strongly real element `x` of odd order lies in the member `C_G(x)` of `ℱ`
  (it is not an involution: `x² = 1` would give `orderOf x ∣ 2` against oddness) — this is
  `SRodd_iff_mem_FinsetCZ`,
* conversely every non-identity element of a member of `ℱ` is strongly real of odd order, again
  by `isCZ_basic` and the fact that `orderOf x` divides `|A|`,
* two members of `ℱ` sharing a non-identity element are equal (`eq_of_mem_FinsetCZ`), i.e. the
  sets `A#` are pairwise disjoint.

So `{x // SRodd x}` is the disjoint union of `{1}` (the identity is strongly real, of order `1`)
and the `A#` for `A ∈ ℱ`: counting the disjoint union with `Finset.card_biUnion` gives the stated
identity.
-/

namespace Work.ZassenhausSuzuki.Odd

set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

theorem sum_card_sub_one (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) :
    (∑ A ∈ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G), (Nat.card ↥A - 1)) + 1
      = Nat.card {x : G // Work.ZassenhausSuzuki.Odd.SRodd x} := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  -- the strongly real elements of odd order are `1` together with the `A#`, `A ∈ ℱ`
  have hiff := SRodd_iff_mem_FinsetCZ h
  -- the set of non-identity elements of a member of `ℱ`
  let g : Subgroup G → Finset G := fun A => (Finset.univ.filter (fun y : G => y ∈ A)).erase 1
  -- distinct members of `ℱ` have disjoint sets of non-identity elements
  have hdisj : ∀ A ∈ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G),
      ∀ B ∈ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G), A ≠ B → Disjoint (g A) (g B) := by
    intro A hA B hB hAB
    rw [Finset.disjoint_left]
    intro y hyA hyB
    rw [Finset.mem_erase] at hyA hyB
    obtain ⟨hy1, hyA'⟩ := hyA
    obtain ⟨-, hyB'⟩ := hyB
    exact hAB (eq_of_mem_FinsetCZ h hA hB (Finset.mem_filter.mp hyA').2
      (Finset.mem_filter.mp hyB').2 hy1)
  have hT : (Finset.univ.filter (fun x : G => Work.ZassenhausSuzuki.Odd.SRodd x)) =
      insert (1 : G) (Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G).biUnion g) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_biUnion, g, Finset.mem_erase]
    rw [hiff y]
    constructor
    · rintro (rfl | ⟨A, hA, hyA⟩)
      · exact Or.inl rfl
      · by_cases hy1 : y = 1
        · exact Or.inl hy1
        · exact Or.inr ⟨A, hA, hy1, hyA⟩
    · rintro (rfl | ⟨A, hA, hy1, hyA⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨A, hA, hyA⟩
  have h1notin : (1 : G) ∉ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G).biUnion g := by
    intro h1
    obtain ⟨A, _hA, h1A⟩ := Finset.mem_biUnion.mp h1
    exact (Finset.mem_erase.mp h1A).1 rfl
  -- card of the disjoint union, displayed as the sum of the cardinalities
  have hcardT : (Finset.univ.filter (fun x : G => Work.ZassenhausSuzuki.Odd.SRodd x)).card =
      (Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G).biUnion g).card + 1 := by
    rw [hT, Finset.card_insert_of_notMem h1notin]
  have hcardB : (Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G).biUnion g).card =
      ∑ A ∈ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G), (g A).card :=
    Finset.card_biUnion hdisj
  -- the set of non-identity elements of `A ∈ ℱ` has `|A| - 1` elements
  have hgcard : ∀ A ∈ Work.ZassenhausSuzuki.Odd.FinsetCZ (G := G),
      (g A).card = Nat.card ↥A - 1 := by
    intro A _hA
    have h1A : (1 : G) ∈ Finset.univ.filter (fun y : G => y ∈ A) := by simp
    have hcardA : (Finset.univ.filter (fun y : G => y ∈ A)).card = Nat.card ↥A := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    show ((Finset.univ.filter (fun y : G => y ∈ A)).erase 1).card = Nat.card ↥A - 1
    rw [Finset.card_erase_of_mem h1A, hcardA]
  have htarget : Nat.card {x : G // Work.ZassenhausSuzuki.Odd.SRodd x} =
      (Finset.univ.filter (fun x : G => Work.ZassenhausSuzuki.Odd.SRodd x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [htarget, hcardT, hcardB]
  congr 1
  exact Finset.sum_congr rfl fun A hA => (hgcard A hA).symm

end Work.ZassenhausSuzuki.Odd
