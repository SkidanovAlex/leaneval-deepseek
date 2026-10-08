import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.DSTR.map_fittingPiIn_le
import Submission.Work.CORE2A.d16_case_a_false
import Submission.Work.CORE2A.fstar_eq_pCore_of_isPGroup

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE3

open Subgroup
open Work.GW2

/-! ## Elementary `p`-core API in this universe

The lemmas below are local copies of facts proved in `Work.CORE2A`; the `Work.BMAX` versions of
the same statements (`Work.BMAX.PiCoreOfNilpotent`, `Work.BMAX.PcoreMapSubtype`,
`Work.BMAX.PiCoreJoin`) cannot be imported here because the `BMAX` files pull in
`Submission.Work.GLUE.Defs`, which re-declares the `Work.GW2` vocabulary already provided by
`Submission.Work.ASM.Defs`. -/

/-- `O_p(G)` is characteristic in a finite group: it only depends on the isomorphism type. -/
theorem pCore_characteristic_core3 (p : ℕ) (G : Type) [Group G] [Finite G] [Fact p.Prime] :
    (Work.GW2.pCore p G).Characteristic := by
  rw [Work.CORE2A.pCore_eq_opCore]
  exact OddOrder.Isaacs.Ch01.opCore.characteristic p G

/-- For a normal subgroup `F ⊴ G`, the image of `O_q(F)` under the inclusion `F ↪ G` lies in
`O_q(G)`.  The image is normal in `G` (it is characteristic in `F`, which is normal in `G`) and
is a `q`-group (a homomorphic image of one), so the universal property of `O_q(G)` applies. -/
theorem pCore_map_subtype_le_core3 {G : Type} [Group G] [Finite G] (F : Subgroup G) [F.Normal]
    {q : ℕ} [Fact q.Prime] :
    (Work.GW2.pCore q ↥F).map F.subtype ≤ Work.GW2.pCore q G := by
  haveI : Finite ↥F := inferInstance
  haveI hchar : (Work.GW2.pCore q ↥F).Characteristic := pCore_characteristic_core3 q ↥F
  exact Work.CORE2A.le_pCore_of_normal_isPGroup
    ((Work.CORE2A.pCore_isPGroup_of_finite (H := ↥F) (p := q)).map F.subtype)

/-- **A `π`-subgroup of a finite nilpotent group lies in the join of the prime cores.**  This is
`Work.CORE2A.le_iSup_pCore_of_isPiSubgroup` with the (redundant) `q.Prime` binder removed — it is
supplied by `hπ` — which makes it usable as a rewriting step below. -/
theorem le_iSup_pCore_of_isPiSubgroup_core3 {H : Type} [Group H] [Finite H]
    [Group.IsNilpotent H] (π : Set ℕ) (hπ : ∀ q ∈ π, q.Prime) (N : Subgroup H)
    (hNπ : ∀ q ∈ (Nat.card ↥N).primeFactors, q ∈ π) :
    N ≤ ⨆ (q : ℕ) (_ : q ∈ π), Work.GW2.pCore q H := by
  have htop : (⊤ : Subgroup ↥N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← htop, ← OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥N,
    Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨p, hp⟩
  have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hpP⟩
  have hpπ : p ∈ π := hNπ p hp
  have hpg : IsPGroup p ↥(((default : Sylow p ↥N) : Subgroup ↥N).map N.subtype) :=
    IsPGroup.map (default : Sylow p ↥N).isPGroup' N.subtype
  refine (Work.CORE2A.le_pCore_of_isPGroup_of_isNilpotent hpg).trans ?_
  exact le_iSup_of_le p (le_iSup_of_le hpπ le_rfl)

/-- In a finite group the `π`-part of the Fitting subgroup is the join of the prime cores:
`F_π(X) = O_π(F(X)) = ⨆_{q ∈ π} O_q(X)`, for a set `π` of primes.

This is the `Submission.Work.ASM.Defs`-universe counterpart of
`Submission.Work.BMAX.PiCoreJoin` (mathematically verbatim: that file proves the same identity
for the same definitions); it cannot be imported here because it pulls in
`Submission.Work.GLUE.Defs`, which duplicates the `Work.GW2` vocabulary of
`Submission.Work.ASM.Defs`.  Ingredients: `Work.DSTR.FittingPiImg.fitting_eq_isaacsFitting`
(so `F(X)` is nilpotent), `Work.DSTR.FittingPiImg.piCore_eq_oPiCore`,
`OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent`,
`IsPGroup.le_sylow_of_normal`, and `Subgroup.map_subtype_le_map_subtype` for the `…In`
transport.  Related proved material in this universe:
`Work.CORE2A.le_iSup_pCore_of_isPiSubgroup`, `Work.CORE2A.pCore_le_fitting`,
`Work.CORE2A.pCore_isPGroup_of_finite`,
`Work.DSTR.FittingPiImg.isPiSubgroup_piCore`. -/
theorem fittingPiIn_eq_iSup_pCoreIn {G : Type} [Group G] [Finite G] (X : Subgroup G) {π : Set ℕ}
    (hπ : ∀ q ∈ π, q.Prime) : fittingPiIn π X = ⨆ (q : ℕ) (_ : q ∈ π), pCoreIn q X := by
  haveI : Finite ↥X := inferInstance
  -- `F(X)` is nilpotent and normal in `↥X`
  haveI hFnil : Group.IsNilpotent ↥(Work.GW2.fitting ↥X) := by
    rw [Work.DSTR.FittingPiImg.fitting_eq_isaacsFitting]
    infer_instance
  haveI hFnorm : (Work.GW2.fitting ↥X).Normal := by
    rw [Work.DSTR.FittingPiImg.fitting_eq_isaacsFitting]
    exact OddOrder.Isaacs.Ch01.fitting.normal ↥X
  -- the identity stated inside the group `↥X`
  have key : Work.GW2.fittingPi π ↥X
      = ⨆ (q : ℕ) (_ : q ∈ π), Work.GW2.pCore q ↥X := by
    refine le_antisymm ?_ ?_
    · -- `O_π(F(X)) ≤ ⨆_{q ∈ π} O_q(X)`: `O_π(F(X))` is a `π`-subgroup of the nilpotent `F(X)`,
      -- so it lies in the join of the `O_q(F(X))`, whose images in `↥X` lie in `O_q(X)`.
      calc Work.GW2.fittingPi π ↥X
          = (Work.GW2.piCore π ↥(Work.GW2.fitting ↥X)).map
              (Work.GW2.fitting ↥X).subtype := rfl
        _ ≤ (⨆ (q : ℕ) (_ : q ∈ π), Work.GW2.pCore q ↥(Work.GW2.fitting ↥X)).map
              (Work.GW2.fitting ↥X).subtype :=
            Subgroup.map_mono (le_iSup_pCore_of_isPiSubgroup_core3 π hπ _
              (Work.DSTR.FittingPiImg.isPiSubgroup_piCore π))
        _ = ⨆ (q : ℕ) (_ : q ∈ π), (Work.GW2.pCore q ↥(Work.GW2.fitting ↥X)).map
              (Work.GW2.fitting ↥X).subtype := by
            simp only [Subgroup.map_iSup, iSup_subtype']
        _ ≤ ⨆ (q : ℕ) (_ : q ∈ π), Work.GW2.pCore q ↥X := by
            refine iSup_le fun q => iSup_le fun hq => ?_
            haveI : Fact q.Prime := ⟨hπ q hq⟩
            exact le_iSup_of_le q (le_iSup_of_le hq
              (pCore_map_subtype_le_core3 (Work.GW2.fitting ↥X)))
    · -- `O_q(X) ≤ O_π(F(X))`: `O_q(X) ≤ F(X)` (`pCore_le_fitting`) and, viewed inside `F(X)`, it
      -- is a normal `q`-subgroup, hence a normal `π`-subgroup.
      refine iSup_le fun q => iSup_le fun hq => ?_
      haveI : Fact q.Prime := ⟨hπ q hq⟩
      exact Work.DSTR.FittingPiImg.le_map_piCore_of_le_of_normal π
        (Work.CORE2A.pCore_le_fitting (G := ↥X) (p := q))
        (Subgroup.isPiSubgroup_of_isPGroup_of_mem
          (Work.CORE2A.pCore_isPGroup_of_finite (H := ↥X) (p := q)) hq)
  -- transport along the inclusion `↥X ↪ G`
  have hR : (⨆ (q : ℕ) (_ : q ∈ π), Work.GW2.pCoreIn q X)
      = (⨆ (q : ℕ) (_ : q ∈ π), Work.GW2.pCore q ↥X).map X.subtype := by
    simp only [Work.GW2.pCoreIn, Subgroup.map_iSup, iSup_subtype']
  apply le_antisymm
  · rw [hR]
    exact (Subgroup.map_subtype_le_map_subtype).mpr (le_of_eq key)
  · rw [hR]
    exact (Subgroup.map_subtype_le_map_subtype).mpr (le_of_eq key.symm)

end Work.CORE3
