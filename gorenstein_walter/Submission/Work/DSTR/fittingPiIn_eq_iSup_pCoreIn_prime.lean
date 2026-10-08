import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.DSTR.map_fittingPiIn_le

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# `F_π` as the join of the prime cores

`F_π(X) = O_π(F(X)) = ⨆_{q ∈ π, q prime} O_q(X)`.  The existing
`Work.CORE3.fittingPiIn_eq_iSup_pCoreIn` states this under the hypothesis that every element of
`π` is prime; here `π` is arbitrary (composites and `0` in `π` are irrelevant for `O_π`), which is
the form needed for the `2'`-part `π = {n | n ≠ 2}`.

The elementary `O_p`-API used below (`O_p(G)` is a `p`-group, the universal property of `O_p`,
`O_p ≤ F`, every `p`-subgroup of a nilpotent group lies in `O_p`, and `O_p(K)` maps into `O_p(X)`
for `K ⊴ X`) is proved here again rather than imported from `Work.CORE2A`/`Work.DSTR.d110iOdd`,
because the copies in those files are *universe-monomorphic* (`{G : Type}`), whereas the target
statement below is universe-polymorphic (`{G H : Type*}`).
-/

namespace Work.DSTR

open Subgroup

namespace FittingPiImg

/-! ## Universe-polymorphic copies of the elementary `O_p`-API -/

/-- `O_p(G)` in the contract's sense is Isaacs' `p`-core. -/
theorem pCore_eq_opCore' {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.GW2.pCore p G = OddOrder.Isaacs.Ch01.opCore p G := by
  have hS : sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}
      = OddOrder.Isaacs.Ch01.opCore p G := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hpN⟩
      exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore (N := N) hpN
    · exact ⟨OddOrder.Isaacs.Ch01.opCore.normal p G,
        OddOrder.Isaacs.Ch01.opCore_isPGroup p G⟩
  rw [Work.GW2.pCore, hS]
  exact Subgroup.normalCore_eq_self _

/-- `O_p(G)` is a `p`-group. -/
theorem pCore_isPGroup' {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    IsPGroup p ↥(Work.GW2.pCore p G) := by
  rw [pCore_eq_opCore']
  exact OddOrder.Isaacs.Ch01.opCore_isPGroup p G

/-- **Universal property of `O_p(G)`**: every normal `p`-subgroup lies in `O_p(G)`. -/
theorem le_pCore_of_normal_isPGroup' {G : Type*} [Group G] {p : ℕ} {N : Subgroup G}
    [N.Normal] (hN : IsPGroup p N) : N ≤ Work.GW2.pCore p G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- `O_p(G) ≤ F(G)`: a normal `p`-subgroup is nilpotent. -/
theorem pCore_le_fitting' {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.GW2.pCore p G ≤ Work.GW2.fitting G := by
  refine Subgroup.normal_le_normalCore.mpr ?_
  refine (Subgroup.normalCore_le _).trans ?_
  refine sSup_le ?_
  intro N hN
  exact le_sSup ⟨hN.1, hN.2.isNilpotent⟩

/-- Every `p`-subgroup of a finite nilpotent group lies in its `p`-core. -/
theorem le_pCore_of_isPGroup_of_isNilpotent' {H : Type*} [Group H] [Finite H]
    [Group.IsNilpotent H] {p : ℕ} [Fact p.Prime] {X : Subgroup H} (hX : IsPGroup p X) :
    X ≤ Work.GW2.pCore p H := by
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  haveI : (Q : Subgroup H).Normal := OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent Q
  exact hXQ.trans (le_pCore_of_normal_isPGroup' Q.isPGroup')

/-- Every `π`-subgroup of a finite nilpotent group lies in the join of the prime `q`-cores for
primes `q ∈ π` (`N` is nilpotent, hence the join of its own Sylow subgroups,
`iSup_default_sylow_eq_top_of_nilpotent`; each of these maps into `H` as a `q`-subgroup). -/
theorem le_iSup_pCore_of_isPiSubgroup' {H : Type*} [Group H] [Finite H] [Group.IsNilpotent H]
    (π : Set ℕ) (N : Subgroup H) (hNπ : ∀ q ∈ (Nat.card ↥N).primeFactors, q ∈ π) :
    N ≤ ⨆ (q : ℕ) (_ : q ∈ π) (_ : q.Prime), Work.GW2.pCore q H := by
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
  refine (le_pCore_of_isPGroup_of_isNilpotent' hpg).trans ?_
  exact le_iSup_of_le p (le_iSup_of_le hpπ (le_iSup_of_le hpP le_rfl))

/-- **Transfer of the `p`-core along an inclusion.**  For `K ◁ X`, the image of `O_p(K)` in `X`
is a normal `p`-subgroup of `X`, hence lies in `O_p(X)`. -/
theorem pCore_map_subtype_le' {X : Type*} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    {p : ℕ} [Fact p.Prime] :
    (Work.GW2.pCore p ↥K).map K.subtype ≤ Work.GW2.pCore p X := by
  haveI hchar : (Work.GW2.pCore p ↥K).Characteristic := by
    rw [pCore_eq_opCore']
    exact OddOrder.Isaacs.Ch01.opCore.characteristic p ↥K
  haveI hnorm : ((Work.GW2.pCore p ↥K).map K.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  exact le_pCore_of_normal_isPGroup' ((pCore_isPGroup' (G := ↥K) (p := p)).map K.subtype)

/-! ## The join decomposition of `F_π` -/

/-- For an arbitrary set `π` of natural numbers, `F_π(X)` is the join of the images of the prime
cores `O_q(X)` over the primes `q ∈ π`.

Direction `≤`: `O_π(F(X))` is a `π`-subgroup of the nilpotent group `F(X)`, hence contained in
the join of the `q`-cores of `F(X)` for primes `q ∈ π` (`le_iSup_pCore_of_isPiSubgroup'`); each of
these maps into `O_q(X)` because `F(X) ⊴ X` (`pCore_map_subtype_le'`).
Direction `≥`: `O_q(X) ≤ F(X)` for a prime `q`, and it is a normal `q`-subgroup, hence a normal
`π`-subgroup, so it lies in the image of `O_π(F(X))` (`le_map_piCore_of_le_of_normal`). -/
theorem fittingPiIn_eq_iSup_pCoreIn' {G : Type*} [Group G] [Finite G] (X : Subgroup G)
    (π : Set ℕ) :
    Work.GW2.fittingPiIn π X
      = ⨆ (q : ℕ) (_ : q ∈ π) (_ : q.Prime), Work.GW2.pCoreIn q X := by
  haveI : Finite ↥X := inferInstance
  haveI hFnil : Group.IsNilpotent ↥(Work.GW2.fitting ↥X) := by
    rw [FittingPiImg.fitting_eq_isaacsFitting]
    infer_instance
  haveI hFnorm : (Work.GW2.fitting ↥X).Normal := by
    rw [FittingPiImg.fitting_eq_isaacsFitting]
    exact OddOrder.Isaacs.Ch01.fitting.normal ↥X
  -- the identity stated inside the group `↥X`
  have key : Work.GW2.fittingPi π ↥X
      = ⨆ (q : ℕ) (_ : q ∈ π) (_ : q.Prime), Work.GW2.pCore q ↥X := by
    refine le_antisymm ?_ ?_
    · calc Work.GW2.fittingPi π ↥X
          = (Work.GW2.piCore π ↥(Work.GW2.fitting ↥X)).map
              (Work.GW2.fitting ↥X).subtype := rfl
        _ ≤ (⨆ (q : ℕ) (_ : q ∈ π) (_ : q.Prime),
              Work.GW2.pCore q ↥(Work.GW2.fitting ↥X)).map
              (Work.GW2.fitting ↥X).subtype :=
            Subgroup.map_mono
              (le_iSup_pCore_of_isPiSubgroup' π _ (isPiSubgroup_piCore π))
        _ = ⨆ (q : ℕ) (_ : q ∈ π) (_ : q.Prime),
              (Work.GW2.pCore q ↥(Work.GW2.fitting ↥X)).map
                (Work.GW2.fitting ↥X).subtype := by
            simp only [Subgroup.map_iSup]
        _ ≤ ⨆ (q : ℕ) (_ : q ∈ π) (_ : q.Prime), Work.GW2.pCore q ↥X := by
            refine iSup_le fun q => iSup_le fun hqπ => iSup_le fun hq => ?_
            haveI : Fact q.Prime := ⟨hq⟩
            exact le_iSup_of_le q (le_iSup_of_le hqπ (le_iSup_of_le hq
              (pCore_map_subtype_le' (X := ↥X) (K := Work.GW2.fitting ↥X) (p := q))))
    · refine iSup_le fun q => iSup_le fun hqπ => iSup_le fun hq => ?_
      haveI : Fact q.Prime := ⟨hq⟩
      exact FittingPiImg.le_map_piCore_of_le_of_normal π
        (pCore_le_fitting' (G := ↥X) (p := q))
        (Subgroup.isPiSubgroup_of_isPGroup_of_mem
          (pCore_isPGroup' (G := ↥X) (p := q)) hqπ)
  -- transport along the inclusion `↥X ↪ G`
  have hR : (⨆ (q : ℕ) (_ : q ∈ π) (_ : q.Prime), Work.GW2.pCoreIn q X)
      = (⨆ (q : ℕ) (_ : q ∈ π) (_ : q.Prime), Work.GW2.pCore q ↥X).map X.subtype := by
    simp only [Work.GW2.pCoreIn, Subgroup.map_iSup, iSup_subtype']
  rw [Work.GW2.fittingPiIn, hR, key]

end FittingPiImg

end Work.DSTR
