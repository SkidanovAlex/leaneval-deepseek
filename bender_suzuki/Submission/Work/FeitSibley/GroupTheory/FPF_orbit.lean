import Submission.Work.FeitSibley.GroupTheory.S_Q1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley`: `D` acts freely on `Q₁`, so cardinalities are `≡ 1 mod |D|`

`D` acts by conjugation on `Q₁` (`Q₁ ⊴ H`), and the action is free away from `1`
(`h.D_fpf_Q1`).  Hence every `D`-invariant subgroup `A ≤ Q₁` has `|A| = 1 + k·|D|`; in particular
`|D| ∣ |A| - 1` and, when `A ≠ ⊥`, `|D| + 1 ≤ |A|`.

The count is Burnside's lemma applied to the conjugation action of `D` on `↥A`: only `1` is fixed
by a nontrivial element of `D`, so the sum of the numbers of fixed points is `|A| + (|D| - 1)`.
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.FeitSibley

variable {G : Type} [Group G] [Fintype G]

namespace FSData

variable (h : FSData G)

theorem conj_smul_mem (A : Subgroup G) (hAn : h.D ≤ Subgroup.normalizer (A : Set G))
    (d : ↥h.D) (x : ↥A) : (d : G) * (x : G) * (d : G)⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.mp (hAn d.2) (x : G)).mp x.2

/-- The conjugation action of `D` on a `D`-invariant subgroup `A ≤ Q₁`. -/
noncomputable def conjAct (A : Subgroup G) (hAn : h.D ≤ Subgroup.normalizer (A : Set G)) :
    MulAction ↥h.D ↥A where
  smul d x := ⟨(d : G) * (x : G) * (d : G)⁻¹, h.conj_smul_mem A hAn d x⟩
  one_smul x := by
    apply Subtype.ext
    show (1 : G) * (x : G) * (1 : G)⁻¹ = (x : G)
    simp
  mul_smul d e x := by
    apply Subtype.ext
    show ((d : G) * (e : G)) * (x : G) * ((d : G) * (e : G))⁻¹
      = (d : G) * ((e : G) * (x : G) * (e : G)⁻¹) * (d : G)⁻¹
    group

/-- Only the identity of `A` is fixed by a nontrivial element of `D`. -/
theorem fixedBy_card_eq_one (A : Subgroup G) (hA : A ≤ h.Q1)
    (hAn : h.D ≤ Subgroup.normalizer (A : Set G)) (d : ↥h.D) (hd : (d : G) ≠ 1) :
    Nat.card {x : ↥A // (d : G) * (x : G) * (d : G)⁻¹ = (x : G)} = 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
  refine ⟨⟨1, by simp⟩, fun y => ?_⟩
  refine Subtype.ext (Subtype.ext ?_)
  exact h.D_fpf_Q1 (d : G) d.2 hd (y : G) (hA y.1.2) y.2

/-- A nontrivial subgroup has at least two elements. -/
theorem two_le_card_of_ne_bot (A : Subgroup G) (hAne : A ≠ ⊥) : 2 ≤ Nat.card ↥A := by
  obtain ⟨x, hx⟩ : ∃ x : ↥A, x ≠ 1 := by
    by_contra h
    push_neg at h
    refine hAne (le_antisymm ?_ bot_le)
    intro y hy
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (h ⟨y, hy⟩))
  have hsub : ({1, x} : Finset ↥A).card ≤ Nat.card ↥A := by
    have h1 := Finset.card_le_card (Finset.subset_univ ({1, x} : Finset ↥A))
    rw [Finset.card_univ] at h1
    rwa [Nat.card_eq_fintype_card]
  rw [Finset.card_pair (Ne.symm hx)] at hsub
  exact hsub

end FSData

end Work.FeitSibley
