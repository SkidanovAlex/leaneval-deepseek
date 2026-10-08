import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le

set_option linter.style.haveILetI false

namespace Work.BMAX

/-- **`O_p(Z(F(A))) ≠ 1` for every prime `p` dividing `|F(A)|`.**

Write `F = F(A)`.  `F` is nilpotent, so every prime `p` dividing `|F|` divides `|Z(F)|`
(`Group.IsNilpotent.prime_dvd_card_center`); since `Z(F)` is abelian, Cauchy's theorem yields
an element `z ∈ Z(F)` of order `p`, whose cyclic subgroup is a normal `p`-subgroup of `Z(F)`,
hence lies in `O_p(Z(F))`.  The last step crosses the injective inclusion
`Z(F) ↪ G` via `Subgroup.map_eq_bot_iff_of_injective`. -/
theorem pCoreIn_zcenterIn_fittingIn_ne_bot {G : Type} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) (hpi : p ∈ Work.GW2.primesOf (Work.GW2.fittingIn A)) :
    Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Z := Work.GW2.zcenterIn (Work.GW2.fittingIn A) with hZ
  -- `F(A)` is nilpotent, hence so is its image `fittingIn A` in the ambient group
  haveI hFnil : Group.IsNilpotent ↥(Work.GW2.fitting ↥A) := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥A)]
    infer_instance
  have hNilp : Group.IsNilpotent ↥(Work.GW2.fittingIn A) := by
    rw [Work.GW2.fittingIn]
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (Work.GW2.fitting ↥A) A.subtype A.subtype_injective)
  -- `p ∣ |F(A)|` gives `p ∣ |Z(F(A))|`
  have hpdvd : p ∣ Nat.card ↥(Work.GW2.fittingIn A) := (Nat.mem_primeFactors.mp hpi).2.1
  have hzdvd : p ∣ Nat.card ↥(Subgroup.center ↥(Work.GW2.fittingIn A)) := by
    haveI := hNilp
    exact Group.IsNilpotent.prime_dvd_card_center hpdvd
  -- `|zcenterIn (fittingIn A)| = |Z(F(A))|`, since `zcenterIn` is the image of the centre
  have hcardZ : Nat.card ↥Z = Nat.card ↥(Subgroup.center ↥(Work.GW2.fittingIn A)) := by
    rw [hZ, Work.BMAX.zcenterIn_eq_map_center,
      Subgroup.card_map_of_injective (Work.GW2.fittingIn A).subtype_injective]
  have hpZ : p ∣ Nat.card ↥Z := by rw [hcardZ]; exact hzdvd
  -- `Z(F(A))` is abelian (it is the centre of a group)
  haveI hZcomm : IsMulCommutative ↥Z :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext ((Work.GW2.mem_zcenterIn.mp a.2).2 b.1 (Work.GW2.mem_zcenterIn.mp b.2).1)
  -- the `p`-core of the abelian group `Z(F(A))` is non-trivial
  have hne : Work.GW2.pCore p ↥Z ≠ ⊥ := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpZ
    have hNpg : IsPGroup p ↥(Subgroup.zpowers z) :=
      IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hz, pow_one]⟩
    haveI hNnormal : (Subgroup.zpowers z).Normal := Subgroup.normal_of_isMulCommutative _
    have hNle : Subgroup.zpowers z ≤ Work.GW2.pCore p ↥Z := by
      rw [Work.CORE2A.pCore_eq_opCore (G := ↥Z) (p := p)]
      exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hNpg
    intro hbot
    have hz1 : z = 1 := by
      have : z ∈ (⊥ : Subgroup ↥Z) := hbot ▸ hNle (Subgroup.mem_zpowers z)
      simpa using this
    have : orderOf z = 1 := by rw [hz1, orderOf_one]
    rw [hz] at this
    exact hp.ne_one this
  -- transport across the injective inclusion `Z(F(A)) ↪ G`
  intro hbot
  rw [Work.GW2.pCoreIn] at hbot
  exact hne ((Subgroup.map_eq_bot_iff_of_injective _ Z.subtype_injective).mp hbot)

end Work.BMAX
