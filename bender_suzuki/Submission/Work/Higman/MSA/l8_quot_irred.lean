/-
Higman's Lemma 8: irreducibility of the `ξ`-module `C / A`.

In the configuration of Higman's auxiliary result 8 (`S : MSA.L8.D h A C`), the quotient
`V = C / A` carries the induced `ξ`-action `MSA.L8.xiQuot`.  The minimality hypothesis
`S.hcover` (together with the fact that `P` acts trivially on `C/A`, so that every subgroup of
`C` containing `A` is normal in `P`, `MSA.L8.commutator_top_C_le`) makes `V` irreducible: the
only `ξ`-invariant subgroups of `V` are `⊥` and `⊤`.

The proof lifts a `ξ`-invariant subgroup `K ≤ V` to a subgroup `D ≤ C` with `A ≤ D` via the
correspondence theorem, shows `D` is normal and `ξ`-invariant, and applies `S.hcover`.
-/

import Mathlib
import Submission.Work.Higman.MSA.l8_local
import Submission.Work.Higman.MSA.l8_triv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.MSA

variable {P : Type} [Group P] [Finite P]

/-- The induced automorphism `xiQuot` of `C/A` on representatives: it sends the class of `u` to
the class of `xiSubAut h hCinv u`. -/
theorem l8_xiQuot_mk {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (u : ↥C) :
    L8.xiQuot h hAinv hCinv (QuotientGroup.mk u)
      = QuotientGroup.mk (L8.xiSubAut h hCinv u) :=
  QuotientGroup.congr_mk (A.subgroupOf C) (A.subgroupOf C) (L8.xiSubAut h hCinv) _ u

/-- **Irreducibility of `C/A` under `ξ`.**  The only `ξ`-invariant subgroups of the quotient
`C/A` are `⊥` and `⊤`. -/
theorem l8_quot_irred {P : Type} [Group P] [Finite P]
    {h : Work.Higman.IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : Work.Higman.MSA.L8.D h A C) {K : Subgroup (↥C ⧸ A.subgroupOf C)}
    (hK : K.map (Work.Higman.MSA.L8.xiQuot h S.hA.map_eq S.hCinv).toMonoidHom = K) :
    K = ⊥ ∨ K = ⊤ := by
  -- `K` is stable under the action on elements.
  have hW : ∀ v ∈ K, L8.xiQuot h S.hA.map_eq S.hCinv v ∈ K := by
    intro v hv
    have h1 := Subgroup.mem_map_of_mem (L8.xiQuot h S.hA.map_eq S.hCinv).toMonoidHom hv
    rwa [hK] at h1
  -- Lift `K` to a subgroup `D` of `↥C`, then to a subgroup `Dp` of `P`.
  set D : Subgroup ↥C := K.comap (QuotientGroup.mk' (A.subgroupOf C)) with hD
  have hmemD : ∀ u : ↥C, u ∈ D ↔ QuotientGroup.mk' (A.subgroupOf C) u ∈ K := fun u => Iff.rfl
  set Dp : Subgroup P := D.map C.subtype with hDp
  have hAD : (A.subgroupOf C) ≤ D := by
    intro x hx
    rw [hmemD]
    have hx1 : QuotientGroup.mk' (A.subgroupOf C) x = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact K.one_mem
  have hADp : A ≤ Dp := by
    intro a ha
    rw [hDp]
    exact Subgroup.mem_map.mpr ⟨⟨a, S.hAC ha⟩, hAD (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hDpC : Dp ≤ C := by
    rw [hDp]
    exact Subgroup.map_subtype_le D
  -- `Dp` is `ξ`-invariant.
  have hDpinv_le : Dp.map (h.xi : MulAut P).toMonoidHom ≤ Dp := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hDp]
    refine Subgroup.mem_map.mpr ⟨(L8.xiSubAut h S.hCinv d : ↥C), ?_, rfl⟩
    rw [hmemD] at hd ⊢
    have h1 : L8.xiQuot h S.hA.map_eq S.hCinv (QuotientGroup.mk' (A.subgroupOf C) d) ∈ K :=
      hW _ hd
    simpa [QuotientGroup.mk'_apply, l8_xiQuot_mk] using h1
  have hDpinv : Dp.map (h.xi : MulAut P).toMonoidHom = Dp :=
    Subgroup.eq_of_le_of_card_ge hDpinv_le
      (le_of_eq (Subgroup.card_map_of_injective (h.xi : MulAut P).injective).symm)
  -- `K` is the image of `D` under the quotient map.
  have hKD : K = D.map (QuotientGroup.mk' (A.subgroupOf C)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf C) v
      exact ⟨u, (hmemD u).mpr hv, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact (hmemD u).mp hu
  -- `Dp` is normal (`P` acts trivially on `C/A`) and lies between `A` and `C`, so `hcover` applies.
  have hPC : ⁅(⊤ : Subgroup P), C⁆ ≤ A :=
    L8.commutator_top_C_le h S.hA S.hCn S.hCinv S.hAC S.hCA S.hcover S.hC2 S.hCd S.hAne
  rcases S.hcover Dp (L8.normal_of_le_of_contains hPC hADp hDpC) hDpinv hADp hDpC with h | h
  · left
    have hmap : D.map C.subtype = (A.subgroupOf C).map C.subtype := by
      rw [← hDp, h, Subgroup.map_subgroupOf_eq_of_le S.hAC]
    have hDA : D = A.subgroupOf C := Subgroup.map_injective C.subtype_injective hmap
    rw [hKD, hDA, Subgroup.map_eq_bot_iff]
    intro x hx
    rw [QuotientGroup.ker_mk']
    exact hx
  · right
    have hDtop : D = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      have hx : C.subtype x ∈ Dp := by rw [h]; exact x.2
      rw [hDp] at hx
      obtain ⟨d, hd, hdx⟩ := Subgroup.mem_map.mp hx
      rwa [C.subtype_injective hdx] at hd
    rw [hKD, hDtop, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (A.subgroupOf C))

end Work.Higman.MSA
