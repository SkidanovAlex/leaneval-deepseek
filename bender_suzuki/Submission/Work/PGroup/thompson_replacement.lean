import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.CommClosure
import Submission.Work.PGroup.thompson_product_centralizer
import Submission.Work.PGroup.exists_mem_notMem_commutator_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Thompson's replacement theorem

Let `P` be a finite `p`-group, `A ≤ P` an abelian subgroup of maximal order, and `B ≤ P` an
abelian subgroup which is normalized by `A` but does not normalize `A`.  Thompson's replacement
theorem produces a new abelian subgroup `A' ≤ P` of maximal order which lives in `⟨A, B⟩`,
normalizes `A`, and meets `B` strictly more than `A` does:

`∃ A' ≤ P, A'` abelian, `Nat.card A' = maxAbelianOrder P`, `A' ≤ A ⊔ B`,
`A' ≤ N_G(A)`, `A ⊓ B < A' ⊓ B`.

The proof follows the classical one (Gorenstein, *Finite Groups*, Theorem 2.5 / J. G. Thompson,
*A replacement theorem for p-groups and a conjecture*, J. Algebra 13 (1969) 149–151).

Put `C = A ⊔ B`; by hypothesis `B ◁ C`.  Let `N = N_G(A) ⊓ B`; then `N ◁ C` and `N < B`, so
`B/N` is a nontrivial normal subgroup of the nilpotent group `C/N`; hence it meets the centre of
`C/N` nontrivially, and we find `x ∈ B \ N` with `[x, C] ≤ N`
(`Work.PGroup.exists_mem_notMem_commutator_le`).  The subgroup `M = [x, A] ≤ N ≤ B` is abelian,
and Thompson's product lemma
(`Work.PGroup.thompson_product_centralizer`) says that `A' = M · C_A(M)` is abelian of maximal
order.  It is contained in `AB`, normalizes `A`, and `M ≤ A' ∩ B` while `M ⊄ A`, so that
`A ∩ B < A' ∩ B`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup

/-- If `[x, A] ≤ A` then `x` normalizes `A` (for finite `A`): the map `a ↦ x a x⁻¹` injects `A`
into `A`, hence is bijective. -/
private theorem mem_normalizer_of_commClosure_le {G : Type*} [Group G] {x : G} {A : Subgroup G}
    [Finite ↥A] (h : commClosure x A ≤ A) : x ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    intro a ha
    show (MulAut.conj x) a ∈ A
    rw [conj_eq_commutatorElement_mul]
    exact A.mul_mem (h (mem_commClosure ha)) ha
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

theorem thompson_replacement {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (P A B : Subgroup G) [Finite P] (hP : IsPGroup p P) (hA : A ≤ P)
    (hAab : IsMulCommutative A) (hAmax : Nat.card A = Work.PGroup.maxAbelianOrder P) (hB : B ≤ P)
    (hBab : IsMulCommutative B) (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hBA : ¬ B ≤ Subgroup.normalizer (A : Set G)) :
    ∃ A' : Subgroup G, A' ≤ P ∧ IsMulCommutative A' ∧
      Nat.card A' = Work.PGroup.maxAbelianOrder P ∧ A' ≤ A ⊔ B ∧
      A' ≤ Subgroup.normalizer (A : Set G) ∧ A ⊓ B < A' ⊓ B := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfinA : Finite ↥A :=
    Finite.of_injective (Subgroup.inclusion hA) (Subgroup.inclusion_injective hA)
  -- `C = A ⊔ B` is a finite p-group, hence nilpotent.
  have hCP : A ⊔ B ≤ P := sup_le hA hB
  haveI hfinC : Finite ↥(A ⊔ B) :=
    Finite.of_injective (Subgroup.inclusion hCP) (Subgroup.inclusion_injective hCP)
  have hPC : IsPGroup p ↥(A ⊔ B) :=
    hP.of_injective (Subgroup.inclusion hCP) (Subgroup.inclusion_injective hCP)
  haveI hnilC : Group.IsNilpotent ↥(A ⊔ B) := hPC.isNilpotent
  -- `B` is normal in `C`.
  have hBn : (B.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hAB Subgroup.le_normalizer)
  -- `N = N_G(A) ⊓ B` is normal in `C`: both `A` and `B` normalize it.
  have hAnorm :
      A ≤ Subgroup.normalizer (((Subgroup.normalizer (A : Set G) ⊓ B : Subgroup G)) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha n hn
    rw [Subgroup.mem_inf] at hn ⊢
    have haN : a ∈ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer ha
    exact ⟨(Subgroup.normalizer (A : Set G)).mul_mem
              ((Subgroup.normalizer (A : Set G)).mul_mem haN hn.1)
              ((Subgroup.normalizer (A : Set G)).inv_mem haN),
           (Subgroup.le_normalizer_iff.mp hAB) a ha n hn.2⟩
  have hBnorm :
      B ≤ Subgroup.normalizer (((Subgroup.normalizer (A : Set G) ⊓ B : Subgroup G)) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb n hn
    rw [Subgroup.mem_inf] at hn ⊢
    have h_eq : b * n * b⁻¹ = n := by
      have hcomm : (⟨b, hb⟩ : ↥B) * ⟨n, hn.2⟩ = ⟨n, hn.2⟩ * ⟨b, hb⟩ :=
        isMulCommutative_iff.mp hBab _ _
      have hbn : b * n = n * b := congrArg Subtype.val hcomm
      rw [hbn, mul_assoc, mul_inv_cancel, mul_one]
    rw [h_eq]
    exact hn
  have hN0B : (Subgroup.normalizer (A : Set G) ⊓ B : Subgroup G) ≤ B := inf_le_right
  have hN0C : (Subgroup.normalizer (A : Set G) ⊓ B : Subgroup G) ≤ A ⊔ B :=
    hN0B.trans le_sup_right
  have hNn : ((Subgroup.normalizer (A : Set G) ⊓ B : Subgroup G).subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN0C).mpr (sup_le hAnorm hBnorm)
  have hBN : ¬ B ≤ (Subgroup.normalizer (A : Set G) ⊓ B : Subgroup G) :=
    fun h => hBA (le_trans h inf_le_left)
  -- An element `x ∈ B \ N` with `[x, C] ≤ N`.
  obtain ⟨x, hxB, hxN0, hxcomm⟩ :=
    exists_mem_notMem_commutator_le (A ⊔ B) B (Subgroup.normalizer (A : Set G) ⊓ B)
      hN0B le_sup_right hBn hNn hBN hnilC
  -- `M = [x, A] ⊆ N ⊆ B` is abelian.
  let M : Subgroup G := commClosure x A
  have hM_le_N0 : M ≤ Subgroup.normalizer (A : Set G) ⊓ B := by
    rw [le_commClosure_iff]
    intro a ha
    exact hxcomm a (Subgroup.mem_sup_left ha)
  have hM_le_B : M ≤ B := hM_le_N0.trans inf_le_right
  have hM_le_P : M ≤ P := hM_le_B.trans hB
  have hMab : IsMulCommutative M := isMulCommutative_of_le hBab hM_le_B
  -- Thompson's product lemma.
  obtain ⟨hA'ab, hA'card⟩ := thompson_product_centralizer hA hAab hAmax hM_le_P hMab
  refine ⟨M ⊔ (A ⊓ Subgroup.centralizer (M : Set G)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sup_le hM_le_P (inf_le_left.trans hA)
  · exact hA'ab
  · exact hA'card
  · exact sup_le (hM_le_B.trans le_sup_right) (inf_le_left.trans le_sup_left)
  · exact sup_le (hM_le_N0.trans inf_le_left) (inf_le_left.trans Subgroup.le_normalizer)
  · refine lt_of_le_not_ge ?_ ?_
    · -- `A ⊓ B ≤ A' ⊓ B`
      refine le_inf ?_ inf_le_right
      have hAB_le_C0 : A ⊓ B ≤ A ⊓ Subgroup.centralizer ((M : Subgroup G) : Set G) := by
        refine le_inf inf_le_left ?_
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have hcomm : (⟨m, hM_le_B hm⟩ : ↥B) * ⟨y, (Subgroup.mem_inf.mp hy).2⟩
            = ⟨y, (Subgroup.mem_inf.mp hy).2⟩ * ⟨m, hM_le_B hm⟩ :=
          isMulCommutative_iff.mp hBab _ _
        simpa using congrArg Subtype.val hcomm
      exact hAB_le_C0.trans le_sup_right
    · -- `A' ⊓ B ≰ A ⊓ B`, since `M ≤ A' ⊓ B` but `M ⊄ A`
      intro hcontra
      have hM_le_A : M ≤ A :=
        (le_inf le_sup_left hM_le_B).trans (hcontra.trans inf_le_left)
      have hxn : x ∈ Subgroup.normalizer (A : Set G) := mem_normalizer_of_commClosure_le hM_le_A
      exact hxN0 (Subgroup.mem_inf.mpr ⟨hxn, hxB⟩)

end Work.PGroup
