import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.EscapeCoreLib.charSeparation
import Submission.Work.SSGRoute.N2v2.isUnramifiedIn_of_notMem_Tprime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.N2v2

/-- **A finite abelian extension of `↥K` whose norm class subgroup contains the idèle classes of
`powTIdeles` is unramified outside `T'`.**

This is the variant of `Work.SSGRoute.N2v2.isUnramifiedIn_of_notMem_Tprime` in which the exact
norm group `N_{M/↥K}C_M = gesUPow ↥K p T'` is weakened to the inclusion
`im(Kˣ · E) ≤ N_{M/↥K}C_M` (`E = powTIdeles ↥K p T'`: the idèles that are `p`-th powers at the
primes of `T'` and local units at every other place).  It applies in particular to the level field
`F` of `Work.SSGRoute.N2v2.exists_levelField_of_gesUPow_subfield_N`, whose norm class subgroup is
`im(Kˣ · E) ⊔ (p-th powers) ⊔ N_{N/↥K}C_N ⊇ im(Kˣ · E)`.

The proof is the one of `isUnramifiedIn_of_notMem_Tprime`, with the equality replaced by the
inclusion: the one-place idèle at a local unit outside `T'` lies in `powTIdeles ↥K p T'`
(`Work.SSGRoute.N2v2.onePlace_ofFinite_mem_powTIdeles`), so its class lies in the right-hand side
of the hypothesis, hence in `N_{M/↥K}C_M`; local faithfulness at one place for abelian extensions
(`ZDataMup.localFaithful_abelian`) upgrades this to membership in the local norm subgroup
(`Work.SSGRoute.N2v2.onePlace_mem_localNormSubgroup_of_mem_normClassSubgroup`, whose hypothesis is
exactly that membership), and then the norm-index criterion
(`Work.SSGRoute.N2v2.ramificationIdx_eq_one_of_localUnits_le_localNormSubgroup`) gives
`ramificationIdx = 1`, i.e. `IsUnramifiedIn`. -/
theorem isUnramifiedIn_of_unitIdeles_le_normClassSubgroup (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (M : IntermediateField ↥K Ω) [FiniteDimensional ↥K M] [IsGalois ↥K M] [NumberField ↥M]
    [IsMulCommutative (↥M ≃ₐ[↥K] ↥M)]
    (hM : ((NK.GlobalCFT.Idele.principalSubgroup ↥K ⊔ Work.SSGRoute.powTIdeles ↥K p T').map
        (NK.GlobalCFT.IdeleClassGroup.mk ↥K)) ≤ NK.GlobalCFT.Idele.normClassSubgroup ↥K ↥M)
    (𝔮 : NK.Chebotarev.PrimeIdeal ↥K) (h𝔮 : 𝔮 ∉ T') :
    NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M) 𝔮 := by
  -- every local unit at `𝔮` is a local norm
  have hloc : NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔮) ≤
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥M)
        (NK.GlobalCFT.Place.ofFinite 𝔮) := by
    intro u hu
    -- the one-place idèle at the local unit `u` lies in `powTIdeles`
    have hz : NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) u ∈
        Work.SSGRoute.powTIdeles ↥K p T' :=
      onePlace_ofFinite_mem_powTIdeles p T' 𝔮 h𝔮 u hu
    -- hence its class lies in `im(Kˣ · E)`, and so in `N_{M/↥K}C_M` by the hypothesis
    have hz' : (NK.GlobalCFT.IdeleClassGroup.mk ↥K)
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔮) u) ∈
        ((NK.GlobalCFT.Idele.principalSubgroup ↥K ⊔
          Work.SSGRoute.powTIdeles ↥K p T').map
            (NK.GlobalCFT.IdeleClassGroup.mk ↥K)) :=
      Subgroup.mem_map.mpr ⟨_, Subgroup.mem_sup_right hz, rfl⟩
    -- local faithfulness upgrades this to membership in the local norm subgroup
    exact onePlace_mem_localNormSubgroup_of_mem_normClassSubgroup 𝔮 u (hM hz')
  -- and the ramification criterion concludes
  exact ramificationIdx_eq_one_of_localUnits_le_localNormSubgroup 𝔮 hloc

end Work.SSGRoute.N2v2
