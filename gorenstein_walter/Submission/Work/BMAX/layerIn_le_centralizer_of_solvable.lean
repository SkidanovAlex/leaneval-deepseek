/-
# The layer commutes with a solvable subgroup that it normalizes and is normalized by

This file proves

* `Work.BMAX.layerIn_le_centralizer_of_solvable` :
  if `L ≤ G` is solvable and `L` and the layer `E(A) = Work.GW2.layerIn A` normalize each
  other, then `E(A) ≤ C_G(L)`.

## Mathematics

Write `S := E(A)` and `M := ⁅S, L⁆ ≤ S ⊓ L`.  Because `S` and `L` normalize each other, both
are normal in `H = S ⊔ L`, so `M` is normal in `S` (and in `L`); and `M` is solvable since
`M ≤ L`.

*Every normal quasisimple subgroup `E ≤ S` centralizes `M`.*  `M ⊓ E` is normal in `E`, hence
subnormal, and solvable (it is contained in `M ≤ L`); the dichotomy
`subnormal_le_centralizer_or_eq_of_isQuasisimple` therefore gives
`M ⊓ E ≤ C(E)` — the alternative `E ≤ M ⊓ E` is impossible since a quasisimple group is not
solvable.  Then `⁅M,E⁆ ≤ M ⊓ E ≤ C(E)`, and the Three Subgroups Lemma (in the "rotate" form,
using `E = ⁅E,E⁆`) yields `⁅M,E⁆ = 1`.  As `S` is the join of these `E`, `⁅M,S⁆ = 1`.

*Conclusion.*  `M ≤ S` and `M ≤ C(S)`, so `M ≤ Z(S)`.  Since `S` is perfect (it is the join of
perfect subgroups), the Three Subgroups Lemma applied to `(S, S, L)` gives
`⁅S,L⁆ = ⁅⁅S,S⁆,L⁆ = 1`, i.e. `S ≤ C(L)`.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.LayerCentralizesFitting
import Submission.Work.BMAX.commutator_eq_bot_of_isQuasisimple_of_isQuasisimple
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le
import Submission.Work.BMAX.Components.subnormal_le_centralizer_or_eq_of_isQuasisimple
import Submission.Work.BMAX.Components.isComponent_map_subtype

set_option linter.style.haveILetI false

namespace Work.BMAX

open Subgroup

theorem layerIn_le_centralizer_of_solvable {G : Type} [Group G] [Finite G] {A L : Subgroup G}
    (hL : Group.IsSolvable ↥L)
    (hLn : L ≤ Subgroup.normalizer ((Work.GW2.layerIn A : Subgroup G) : Set G))
    (hEn : Work.GW2.layerIn A ≤ Subgroup.normalizer (L : Set G)) :
    Work.GW2.layerIn A ≤ Subgroup.centralizer (L : Set G) := by
  haveI : Group.IsSolvable ↥L := hL
  set S : Subgroup G := Work.GW2.layerIn A with hSdef
  set M : Subgroup G := ⁅S, L⁆ with hMdef
  have hSnL : S ≤ Subgroup.normalizer (L : Set G) := hEn
  have hLnS : L ≤ Subgroup.normalizer (S : Set G) := hLn
  -- `M ≤ S` and `M ≤ L`
  have hMS : M ≤ S := by
    rw [hMdef, Subgroup.commutator_comm S L]
    exact (Subgroup.le_normalizer_iff_commutator_le_right (H := L) (K := S)).mp hLnS
  have hML : M ≤ L := by
    rw [hMdef, Subgroup.commutator_comm S L]
    exact (Subgroup.le_normalizer_iff_commutator_le_left (H := S) (K := L)).mp hSnL
  -- `S ≤ N(M)`, `L ≤ N(M)`
  have hSnM : S ≤ Subgroup.normalizer (M : Set G) := by
    rw [hMdef]; exact Subgroup.normalizer_commutator_ge_left S L
  -- `M` is solvable
  haveI : Group.IsSolvable ↥M :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hML).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hML).symm.injective
  -- Step 1: every normal quasisimple `E ≤ ↥A` has `M ≤ C(E.map A.subtype)`
  have key : ∀ E : Subgroup ↥A, E.Normal → Work.GW2.IsQuasisimple E →
      E.map A.subtype ≤ Subgroup.centralizer (M : Set G) := by
    intro E hEnE hEqE
    have hE'q : Work.GW2.IsQuasisimple (E.map A.subtype) :=
      Work.BMAX.Components.isQuasisimple_map_subtype hEqE
    have hE'leS : E.map A.subtype ≤ S :=
      Subgroup.map_mono (le_sSup (⟨hEnE, hEqE⟩ :
        E ∈ {F : Subgroup ↥A | F.Normal ∧ Work.GW2.IsQuasisimple F}))
    have hAnormE' : A ≤ Subgroup.normalizer ((E.map A.subtype : Subgroup G) : Set G) :=
      le_normalizer_map_subtype_of_normal hEnE
    have hSA : S ≤ A := Subgroup.map_subtype_le (Work.GW2.layer ↥A)
    have hMnE' : M ≤ Subgroup.normalizer ((E.map A.subtype : Subgroup G) : Set G) :=
      le_trans hMS (le_trans hSA hAnormE')
    have hE'nM : E.map A.subtype ≤ Subgroup.normalizer (M : Set G) := le_trans hE'leS hSnM
    -- `M ⊓ E'` is normal in `E'`
    have hinf_normal : ((M ⊓ E.map A.subtype).subgroupOf (E.map A.subtype)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right, Subgroup.le_normalizer_iff]
      intro e he x hx
      exact ⟨(Subgroup.le_normalizer_iff.mp hE'nM) e he x hx.1,
        (E.map A.subtype).mul_mem ((E.map A.subtype).mul_mem he hx.2)
          ((E.map A.subtype).inv_mem he)⟩
    rcases Work.BMAX.Components.subnormal_le_centralizer_or_eq_of_isQuasisimple
        (H := M ⊓ E.map A.subtype) (Q := E.map A.subtype) inf_le_right
        hinf_normal.isSubnormal hE'q with hcase | hcase
    · -- `M ⊓ E' ≤ C(E')`: then `⁅M,E'⁆ = 1` by the Three Subgroups Lemma
      have hAQ : ⁅M, E.map A.subtype⁆ ≤ M ⊓ E.map A.subtype :=
        le_inf
          ((Subgroup.le_normalizer_iff_commutator_le_left (H := E.map A.subtype)
            (K := M)).mp hE'nM)
          ((Subgroup.le_normalizer_iff_commutator_le_right (H := M)
            (K := E.map A.subtype)).mp hMnE')
      have hAcent : ⁅M, E.map A.subtype⁆
          ≤ Subgroup.centralizer ((E.map A.subtype : Subgroup G) : Set G) := le_trans hAQ hcase
      have hA : ⁅⁅M, E.map A.subtype⁆, E.map A.subtype⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAcent
      have h1 : ⁅⁅E.map A.subtype, M⁆, E.map A.subtype⁆ = ⊥ := by
        rw [Subgroup.commutator_comm (E.map A.subtype) M]; exact hA
      have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate
        (H₁ := E.map A.subtype) (H₂ := E.map A.subtype) (H₃ := M) h1 hA
      rw [hE'q.1] at hrot
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hrot
    · -- `E' ≤ M ⊓ E' ≤ L` would make the quasisimple `E'` solvable
      exfalso
      have hle : E.map A.subtype ≤ L := le_trans (le_trans hcase inf_le_left) hML
      haveI : Group.IsSolvable ↥((E.map A.subtype).subgroupOf L) := inferInstance
      have hsol : Group.IsSolvable ↥(E.map A.subtype) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hle).symm.injective
      haveI : Group.IsPerfect ↥(E.map A.subtype) := Subgroup.isPerfect_iff.mpr hE'q.1
      haveI : Nontrivial (↥(E.map A.subtype) ⧸ Subgroup.center ↥(E.map A.subtype)) :=
        hE'q.2.toNontrivial
      haveI : Nontrivial ↥(E.map A.subtype) :=
        Function.Surjective.nontrivial
          (QuotientGroup.mk'_surjective (Subgroup.center ↥(E.map A.subtype)))
      exact Group.IsPerfect.not_isSolvable ↥(E.map A.subtype) hsol
  -- Step 2: `S ≤ C(M)`, hence `M ≤ C(S)`
  have hSM : S ≤ Subgroup.centralizer (M : Set G) := by
    show (Work.GW2.layer ↥A).map A.subtype ≤ Subgroup.centralizer (M : Set G)
    rw [Subgroup.map_le_iff_le_comap, Work.GW2.layer]
    refine sSup_le ?_
    rintro E ⟨hEnE, hEqE⟩
    intro x hx
    rw [Subgroup.mem_comap]
    exact key E hEnE hEqE (Subgroup.mem_map_of_mem A.subtype hx)
  have hMS' : M ≤ Subgroup.centralizer (S : Set G) := Subgroup.le_centralizer_iff.mp hSM
  have hMSbot : ⁅M, S⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hMS'
  -- `S` is perfect: it is the join of perfect subgroups
  have hSperf : ⁅S, S⁆ = S := by
    refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) ?_
    show (Work.GW2.layer ↥A).map A.subtype ≤ ⁅S, S⁆
    rw [Subgroup.map_le_iff_le_comap, Work.GW2.layer]
    refine sSup_le ?_
    rintro E ⟨hEnE, hEqE⟩
    intro x hx
    rw [Subgroup.mem_comap]
    have hE'leS : E.map A.subtype ≤ S :=
      Subgroup.map_mono (le_sSup (⟨hEnE, hEqE⟩ :
        E ∈ {F : Subgroup ↥A | F.Normal ∧ Work.GW2.IsQuasisimple F}))
    have hperf' : ⁅E.map A.subtype, E.map A.subtype⁆ = E.map A.subtype := by
      rw [← Subgroup.map_commutator E E A.subtype, hEqE.1]
    have hle : E.map A.subtype ≤ ⁅S, S⁆ := by
      rw [← hperf']
      exact Subgroup.commutator_mono hE'leS hE'leS
    exact hle (Subgroup.mem_map_of_mem A.subtype hx)
  -- Step 3: Three Subgroups Lemma on `(S, S, L)`
  have h1 : ⁅⁅S, L⁆, S⁆ = ⊥ := hMSbot
  have h2 : ⁅⁅L, S⁆, S⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L S]; exact h1
  have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := S) (H₂ := S) (H₃ := L) h1 h2
  rw [hSperf] at hrot
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hrot

end Work.BMAX
