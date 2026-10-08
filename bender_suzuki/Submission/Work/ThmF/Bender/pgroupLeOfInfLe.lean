import Mathlib
import Submission.Work.ThmF.Bender.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Bender

/-- If `R` is a `p`-subgroup of a finite group `G`, and `P ≤ R` is a subgroup such that
`N_G(P) ≤ N`, then `R ⊓ N ≤ P` forces `R ≤ P`.

Indeed, `R` is a nilpotent group, so by the normalizer condition a proper subgroup of `R` is
properly contained in its `R`-normalizer. If `P < R`, then `N_R(P) = R ⊓ N_G(P) > P`, and any
element of `N_R(P) \ P` lies in `R ⊓ N`, hence in `P`, a contradiction. -/
theorem pgroupLeOfInfLe {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {P N R : Subgroup G} (hR : IsPGroup p R) (hPR : P ≤ R) (hN : Subgroup.normalizer (P : Set G) ≤ N) (hinf : R ⊓ N ≤ P) : R ≤ P := by
  by_contra hle
  -- `P` is a proper subgroup of `R`
  have hne : P ≠ R := fun h => hle (le_of_eq h.symm)
  -- `R` is a nilpotent group, hence satisfies the normalizer condition
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  have hnc : NormalizerCondition R := Group.normalizerCondition_of_isNilpotent
  -- the corresponding subgroup of `R`
  have hP'ne : P.subgroupOf R ≠ ⊤ := by
    intro h
    apply hne
    refine le_antisymm hPR ?_
    intro x hx
    have hx' : (⟨x, hx⟩ : R) ∈ P.subgroupOf R := h ▸ trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  have hP'lt : P.subgroupOf R < ⊤ := lt_top_iff_ne_top.mpr hP'ne
  have hlt : P.subgroupOf R < Subgroup.normalizer (P.subgroupOf R : Subgroup R) := hnc _ hP'lt
  obtain ⟨y, hyN, hyP'⟩ := SetLike.exists_of_lt hlt
  -- `y` normalizes `P` in `G`
  have hyN' : (y : G) ∈ Subgroup.normalizer (P : Set G) := by
    have h2 : y ∈ (Subgroup.normalizer (P : Set G)).subgroupOf R := by
      rw [Subgroup.subgroupOf_normalizer_eq hPR]
      exact hyN
    exact Subgroup.mem_subgroupOf.mp h2
  have hyR : (y : G) ∈ R := y.2
  have hyN'' : (y : G) ∈ N := hN hyN'
  have hyP : (y : G) ∈ P := hinf ⟨hyR, hyN''⟩
  exact hyP' (Subgroup.mem_subgroupOf.mpr hyP)

end Work.ThmF.Bender
