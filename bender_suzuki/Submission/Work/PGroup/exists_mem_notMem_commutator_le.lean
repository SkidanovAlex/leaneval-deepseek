import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PGroup.exists_mem_notMem_commutator_le`

A nontrivial normal subgroup `B / N₀` of a nilpotent group `C` contains a nonidentity element
whose image in `C / N₀` is central.  Equivalently, some `x ∈ B \ N₀` commutes with all of `C`
modulo `N₀`.

This is the standard "every nontrivial normal subgroup of a nilpotent group meets the centre
nontrivially" fact (`Group.IsNilpotent.inf_center_ne_bot_of_normal`), applied to the quotient
`C / N₀` and the normal subgroup `B·N₀ / N₀`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.PGroup

theorem exists_mem_notMem_commutator_le {G : Type*} [Group G]
    (C B N0 : Subgroup G) (hN0B : N0 ≤ B) (hBC : B ≤ C)
    (hBn : (B.subgroupOf C).Normal) (hNn : (N0.subgroupOf C).Normal)
    (hBN : ¬ B ≤ N0) (hnil : Group.IsNilpotent ↥C) :
    ∃ x : G, x ∈ B ∧ x ∉ N0 ∧ ∀ c : G, c ∈ C → x * c * x⁻¹ * c⁻¹ ∈ N0 := by
  classical
  -- view everything inside `C`
  haveI hCnil : Group.IsNilpotent ↥C := hnil
  let M : Subgroup ↥C := N0.subgroupOf C
  haveI hMn : M.Normal := hNn
  let B' : Subgroup ↥C := B.subgroupOf C
  haveI hB'n : B'.Normal := hBn
  -- the quotient `Q := C ⧸ N₀` and the image `BQ` of `B`
  let φ : ↥C →* (↥C ⧸ M) := QuotientGroup.mk' M
  let BQ : Subgroup (↥C ⧸ M) := B'.map φ
  haveI hBQn : BQ.Normal := hB'n.map φ (QuotientGroup.mk'_surjective M)
  -- `BQ` is nontrivial, because `B ⊄ N₀`
  have hBQne : BQ ≠ ⊥ := by
    intro h
    apply hBN
    intro g hg
    have hgC : g ∈ C := hBC hg
    have hmem : φ (⟨g, hgC⟩ : ↥C) ∈ BQ := by
      change φ (⟨g, hgC⟩ : ↥C) ∈ Subgroup.map φ B'
      exact Subgroup.mem_map.mpr ⟨⟨g, hgC⟩, by rw [Subgroup.mem_subgroupOf]; exact hg, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have hker : (⟨g, hgC⟩ : ↥C) ∈ φ.ker := MonoidHom.mem_ker.mpr hmem
    have hM : (⟨g, hgC⟩ : ↥C) ∈ M := by
      rwa [show φ.ker = M from QuotientGroup.ker_mk' M] at hker
    rwa [Subgroup.mem_subgroupOf] at hM
  -- the centre of the nilpotent quotient `Q` meets `BQ` nontrivially
  have hne : BQ ⊓ Subgroup.center (↥C ⧸ M) ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥C ⧸ M) (H := BQ) hBQne
  obtain ⟨y, hy_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hyBQ : (y : ↥C ⧸ M) ∈ BQ := (Subgroup.mem_inf.mp y.2).1
  have hyZ : (y : ↥C ⧸ M) ∈ Subgroup.center (↥C ⧸ M) := (Subgroup.mem_inf.mp y.2).2
  -- lift a representative `b ∈ B`
  obtain ⟨b, hbB', hbφ⟩ := Subgroup.mem_map.mp hyBQ
  refine ⟨(b : G), ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp hbB'
  · -- `b ∉ N₀` because its image `y` is nontrivial
    intro hbN0
    have hbM : b ∈ M := by
      change b ∈ N0.subgroupOf C
      exact Subgroup.mem_subgroupOf.mpr hbN0
    have hker : b ∈ φ.ker := by
      rw [show φ.ker = M from QuotientGroup.ker_mk' M]
      exact hbM
    have hb1 : φ b = 1 := MonoidHom.mem_ker.mp hker
    have hy1 : (y : ↥C ⧸ M) = 1 := by rw [← hbφ, hb1]
    exact hy_ne (Subtype.ext hy1)
  · -- `b` commutes with `C` modulo `N₀`, since its image is central
    intro c hc
    let c' : ↥C := ⟨c, hc⟩
    have hcy : φ c' * (y : ↥C ⧸ M) = (y : ↥C ⧸ M) * φ c' :=
      Subgroup.mem_center_iff.mp hyZ (φ c')
    have hcomm : (y : ↥C ⧸ M) * φ c' = φ c' * (y : ↥C ⧸ M) := hcy.symm
    have hker2 : ⁅b, c'⁆ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, hbφ]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
    have hbcM : ⁅b, c'⁆ ∈ M := by
      rwa [show φ.ker = M from QuotientGroup.ker_mk' M] at hker2
    have hmemN0 : ((⁅b, c'⁆ : ↥C) : G) ∈ N0 := Subgroup.mem_subgroupOf.mp hbcM
    have hcoe : ((⁅b, c'⁆ : ↥C) : G) = (b : G) * c * (b : G)⁻¹ * c⁻¹ := by
      rw [commutatorElement_def]
      simp [c']
    rwa [hcoe] at hmemN0

end Work.PGroup
