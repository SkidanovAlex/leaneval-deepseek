import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.cor3_1
import Submission.Work.GlaubermanZJ.isAbelianSubgroup_iff
import Submission.Work.GlaubermanZJ.ZJ_le
import Submission.Work.GlaubermanZJ.thompsonJ_eq
import Submission.Work.PGroup.All
import Submission.Work.GlaubermanZJ.Thm41.PComm
import Submission.Work.GlaubermanZJ.Thm41.Symmetry
import Submission.Work.GlaubermanZJ.Thm41.IterComm
import Submission.Work.GlaubermanZJ.Thm41.Structure
import Submission.Work.GlaubermanZJ.Thm41.NumBound
import Submission.Work.GlaubermanZJ.Thm41.replacement_step
import Submission.Work.GlaubermanZJ.Thm41.PcFinal
import Submission.Work.GlaubermanZJ.Thm41.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

open scoped commutatorElement
open Subgroup

-- Glauberman 1968, Theorem 4.1 (p. 1111): S a finite p-group, `A ∈ 𝒜(S)`, `B ⊴ S` of
-- nilpotence class at most two with `[B,B] ⊆ Z(J(S))`, and `[B,A;3] ≠ 1` or (`p` odd and
-- `[B,A,A] ≠ 1`); then some `A* ∈ 𝒜(S)` has `A ∩ B ⊊ A* ∩ B` and `[A*,A,A] = 1`.
theorem theorem4_1 {G : Type*} [Group G] (p : ℕ) (hp : p.Prime) (hpne : p ≠ 2)
    (S A B : Subgroup G) [Finite S] (hS : IsPGroup p S)
    (hA : Work.GlaubermanZJ.IsMaxAbelianSubgroup S A) (hB : B ≤ S)
    (hBn : S ≤ Subgroup.normalizer (B : Set G)) (hBp : IsPGroup p B)
    (hclass : ⁅B, B⁆ ≤ Work.PGroup.centerIn B)
    (hcenter : ⁅B, B⁆ ≤ Submission.Blueprint.ZJ S)
    (hcomm : ⁅⁅⁅B, A⁆, A⁆, A⁆ ≠ ⊥ ∨ ⁅⁅B, A⁆, A⁆ ≠ ⊥) :
    ∃ A' : Subgroup G, Work.GlaubermanZJ.IsMaxAbelianSubgroup S A' ∧ A ⊓ B < A' ⊓ B ∧
      ⁅⁅A', A⁆, A⁆ = ⊥ := by
  classical
  have hAmax : ∀ C : Subgroup G, C ≤ S → Submission.Blueprint.IsAbelianSubgroup C →
      Nat.card C ≤ Nat.card A := hA.2.2
  obtain ⟨hAS, hAab', hAcard⟩ := (isMaxAbelianSubgroup_iff S A).mp hA
  have hAab : IsMulCommutative A := isAbelianSubgroup_iff.mp hAab'
  -- `A ≤ J(S)`
  have hAJ : A ≤ Submission.Blueprint.thompsonJ S := le_blueprint_thompsonJ hAS hAab' hAmax
  -- replace `S` by the subgroup `A ⊔ B ⊆ S`
  have hS₀S : A ⊔ B ≤ S := sup_le hAS hB
  haveI : Finite ↥(A ⊔ B) :=
    Finite.of_injective (Subgroup.inclusion hS₀S) (Subgroup.inclusion_injective hS₀S)
  have hS₀ : IsPGroup p ↥(A ⊔ B) :=
    hS.of_injective (Subgroup.inclusion hS₀S) (Subgroup.inclusion_injective hS₀S)
  -- `A ∈ 𝒜(A ⊔ B)`
  have hcard₀ : Nat.card A = Work.PGroup.maxAbelianOrder (A ⊔ B) := by
    refine le_antisymm ?_ ?_
    · exact Work.PGroup.le_maxAbelianOrder (A ⊔ B) A le_sup_left hAab
    · obtain ⟨C, hC, hCcom, hCcard⟩ := Work.PGroup.maxAbelianOrder_attained (A ⊔ B)
      rw [← hCcard, hAcard]
      exact Work.PGroup.le_maxAbelianOrder S C (hC.trans hS₀S) hCcom
  have hA₀ : Work.GlaubermanZJ.IsMaxAbelianSubgroup (A ⊔ B) A :=
    (isMaxAbelianSubgroup_iff (A ⊔ B) A).mpr ⟨le_sup_left, hAab', hcard₀⟩
  -- `[B,B]` is central in `A ⊔ B`
  have hBBcentA : ⁅B, B⁆ ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp ((Subgroup.mem_inf.mp (hcenter hx)).2) y (hAJ hy)
  have hBBcentB : ⁅B, B⁆ ≤ Subgroup.centralizer (B : Set G) :=
    hclass.trans (centerIn_le_centralizer B)
  have hZ₀ : ⁅B, B⁆ ≤ Work.PGroup.centerIn (A ⊔ B) := by
    intro x hx
    have hxB : x ∈ B := Subgroup.commutator_le_self B hx
    have hxAB : x ∈ A ⊔ B := (le_sup_right : B ≤ A ⊔ B) hxB
    have hxcent : x ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
      rw [centralizer_sup]
      exact ⟨hBBcentA hx, hBBcentB hx⟩
    rw [Work.PGroup.centerIn, Subgroup.mem_map]
    refine ⟨⟨x, hxAB⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxcent (z : G) z.2)
  -- the reduced theorem
  obtain ⟨A', hA'max, hlt, hcomm0⟩ :=
    theorem4_1_central (G := G) p hp hpne (A ⊔ B) A B hS₀ hA₀ le_sup_right
      (hS₀S.trans hBn) hZ₀ hcomm
  refine ⟨A', ?_, hlt, hcomm0⟩
  obtain ⟨hA'S₀, hA'ab, hA'card⟩ := (isMaxAbelianSubgroup_iff (A ⊔ B) A').mp hA'max
  refine (isMaxAbelianSubgroup_iff S A').mpr ⟨hA'S₀.trans hS₀S, hA'ab, ?_⟩
  rw [hA'card, ← hcard₀, hAcard]

end Work.GlaubermanZJ
