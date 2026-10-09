import Mathlib
import Submission.Work.SSGRoute.LevelInertiaProEll.Defs
import Submission.Work.SSGRoute.LevelInertiaProEll.levelRingBasic
import Submission.Work.SSGRoute.LevelInertiaProEll.levelRingInertiaIdent
import Submission.Work.SSGRoute.LevelInertiaProEll.levelRingUniformizerData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise NumberField

namespace Work.SSGRoute

/-- **Structure of the inertia subgroup of a finite level: a normal pro-`ℓ` subgroup with cyclic
quotient**, where `ℓ` is the residue characteristic of the place.

`k` a number field, `Ω` an algebraic closure, `A` a finite place of `Ω` over `k` (`hA`) in which
`p` is a unit (`h`), `M/k` a finite normal level.

The proof exhibits the wild inertia subgroup `W = G_1` of the inertia subgroup `I_M` of
`Gal(M/k)` at the prime of `𝓞 M` below `A`, as a subgroup of the group `Gal(M/k)`; `W` is the
image of the first higher ramification subgroup of the level valuation ring
`A_M = A.comap (algebraMap ↥M Ω)` under the inclusion of the decomposition subgroup, and the
tame quotient `I_M/W = G_0/G_1` is cyclic by `NK.RamificationDeep`. -/
theorem levelInertiaNormalProEll
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    ∃ (W : Subgroup (↥M ≃ₐ[k] ↥M)) (ℓ a : ℕ),
      W ≤ Work.SSGRoute.levelInertiaOf k Ω A hA M ∧
      (∀ δ ∈ Work.SSGRoute.levelInertiaOf k Ω A hA M, ∀ u ∈ W, δ * u * δ⁻¹ ∈ W) ∧
      ℓ.Prime ∧ ℓ ≠ p ∧ Nat.card W = ℓ ^ a ∧
      (∃ g ∈ Work.SSGRoute.levelInertiaOf k Ω A hA M,
        ∀ δ ∈ Work.SSGRoute.levelInertiaOf k Ω A hA M,
          ∃ m : ℤ, δ⁻¹ * g ^ m ∈ W) := by
  classical
  obtain ⟨hdvr, hnoeth, hperf, hfinres, ⟨ℓ, f, hℓprime, hℓne, hℓcard⟩⟩ :=
    LevelInertiaProEll.levelRingBasic p k Ω A hA h M
  haveI : IsDiscreteValuationRing (A.comap (algebraMap ↥M Ω)) := hdvr
  haveI : IsNoetherianRing (A.comap (algebraMap ↥M Ω)) := hnoeth
  haveI : PerfectField (IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) := hperf
  haveI : Finite (IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) := hfinres
  haveI hgal : IsGalois k ↥M := inferInstance
  haveI hGfin : Fintype (↥M ≃ₐ[k] ↥M) := AlgEquiv.fintype k ↥M
  haveI hDfin : Finite ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k) :=
    Finite.of_injective
      (fun x : ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k) => (x : ↥M ≃ₐ[k] ↥M))
      Subtype.val_injective
  obtain ⟨π, E, hD⟩ := LevelInertiaProEll.levelRingUniformizerData p k Ω A hA h M
  have hident := LevelInertiaProEll.levelRingInertiaIdent p k Ω A hA h M
  obtain ⟨N₀, hN₀⟩ :=
    NK.RamificationAudit.exists_ramificationSubgroup_eq_bot_of_isDiscreteValuationRing
      (K := k) (A.comap (algebraMap ↥M Ω))
  have hbot : NK.Ramification.ramificationSubgroup (K := k)
      (A.comap (algebraMap ↥M Ω)) (1 + N₀) = ⊥ :=
    le_bot_iff.mp (hN₀ ▸ NK.Ramification.ramificationSubgroup_antitone
      (A.comap (algebraMap ↥M Ω)) (Nat.le_add_left N₀ 1))
  obtain ⟨j, hj⟩ := NK.RamificationDeep.exists_natCard_one_eq_prime_pow (K := k) hD
    hℓprime hℓcard hbot
  -- the residue field of the level ring is a finite field, so its units are cyclic
  haveI hfinQ : Finite ((A.comap (algebraMap ↥M Ω)) ⧸
      IsLocalRing.maximalIdeal (A.comap (algebraMap ↥M Ω))) := hfinres
  haveI hcycU : IsCyclic (((A.comap (algebraMap ↥M Ω)) ⧸
      IsLocalRing.maximalIdeal (A.comap (algebraMap ↥M Ω)))ˣ) := instIsCyclicUnitsOfFinite
  have hcyc := NK.RamificationDeep.isCyclic_quotient_ramificationSubgroup (K := k)
    (A.comap (algebraMap ↥M Ω)) π E hD hcycU
  refine ⟨(NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1).map
      ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype, ℓ, j, ?_, ?_, hℓprime,
    hℓne, ?_, ?_⟩
  · calc (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1).map
          ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype
        ≤ ((A.comap (algebraMap ↥M Ω)).inertiaSubgroup k).map
            ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype :=
          Subgroup.map_mono (NK.Ramification.ramificationSubgroup_le_inertiaSubgroup
            (A.comap (algebraMap ↥M Ω)) 1)
      _ = Ideal.inertia (↥M ≃ₐ[k] ↥M) (levelPrime k Ω A hA M).asIdeal := hident.2
      _ = levelInertiaOf k Ω A hA M := rfl
  · intro δ hδ u hu
    have hδ' : δ ∈ ((A.comap (algebraMap ↥M Ω)).inertiaSubgroup k).map
        ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype := hident.2.symm ▸ hδ
    obtain ⟨δ₀, _, hδ₀eq⟩ := Subgroup.mem_map.mp hδ'
    obtain ⟨u₀, hu₀mem, hu₀eq⟩ := Subgroup.mem_map.mp hu
    have hconj : δ₀ * u₀ * δ₀⁻¹ ∈
        NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1 :=
      (NK.Ramification.ramificationSubgroup_normal (A.comap (algebraMap ↥M Ω)) 1).conj_mem
        u₀ hu₀mem δ₀
    refine Subgroup.mem_map.mpr ⟨δ₀ * u₀ * δ₀⁻¹, hconj, ?_⟩
    simp only [map_mul, map_inv, hδ₀eq, hu₀eq]
  · rw [Subgroup.card_map_of_injective
      (K := NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1)
      (f := ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype) Subtype.val_injective,
      hj]
  · -- cyclicity of the quotient: exhibit a generator modulo the wild inertia
    change ∃ g ∈ Ideal.inertia (↥M ≃ₐ[k] ↥M) (levelPrime k Ω A hA M).asIdeal,
      ∀ δ ∈ Ideal.inertia (↥M ≃ₐ[k] ↥M) (levelPrime k Ω A hA M).asIdeal,
        ∃ m : ℤ, δ⁻¹ * g ^ m ∈
          (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1).map
            ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype
    have hG0eq : (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0).map
        ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype =
        Ideal.inertia (↥M ≃ₐ[k] ↥M) (levelPrime k Ω A hA M).asIdeal := by
      rw [NK.Ramification.ramificationSubgroup_zero]
      exact hident.2
    obtain ⟨q, hq⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective
      ((NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0)) q
    refine ⟨((g₀ : ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k)) : ↥M ≃ₐ[k] ↥M),
      hG0eq ▸ Subgroup.mem_map_of_mem
        (((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype) g₀.2, fun δ hδ => ?_⟩
    have hδ' : δ ∈ (NK.Ramification.ramificationSubgroup (K := k)
        (A.comap (algebraMap ↥M Ω)) 0).map
        ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype := hG0eq.symm ▸ hδ
    obtain ⟨δ₀, hδ₀G0, hδ₀eq⟩ := Subgroup.mem_map.mp hδ'
    have hz : QuotientGroup.mk' ((NK.Ramification.ramificationSubgroup (K := k)
          (A.comap (algebraMap ↥M Ω)) 1).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0))
        (⟨δ₀, hδ₀G0⟩ : ↥(NK.Ramification.ramificationSubgroup (K := k)
          (A.comap (algebraMap ↥M Ω)) 0)) ∈ Subgroup.zpowers q := by
      rw [hq]; exact Subgroup.mem_top _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨m, ?_⟩
    set x : ↥(NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0) :=
      (⟨δ₀, hδ₀G0⟩ : ↥(NK.Ramification.ramificationSubgroup (K := k)
        (A.comap (algebraMap ↥M Ω)) 0))⁻¹ * g₀ ^ m with hxdef
    have h1 : (QuotientGroup.mk' ((NK.Ramification.ramificationSubgroup (K := k)
          (A.comap (algebraMap ↥M Ω)) 1).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0))) x = 1 := by
      rw [hxdef, map_mul, map_inv, map_zpow, hg₀, ← hm, inv_mul_cancel]
    have hx : x ∈ (NK.Ramification.ramificationSubgroup (K := k)
        (A.comap (algebraMap ↥M Ω)) 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0) := by
      have h2 : x ∈ (QuotientGroup.mk' ((NK.Ramification.ramificationSubgroup (K := k)
            (A.comap (algebraMap ↥M Ω)) 1).subgroupOf
            (NK.Ramification.ramificationSubgroup (K := k)
              (A.comap (algebraMap ↥M Ω)) 0))).ker := MonoidHom.mem_ker.mpr h1
      rwa [QuotientGroup.ker_mk'] at h2
    refine Subgroup.mem_map.mpr ⟨(x : ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k)),
      Subgroup.mem_subgroupOf.mp hx, ?_⟩
    have hxval : (x : ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k)) = δ₀⁻¹ * g₀ ^ m := by
      rw [hxdef]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    rw [hxval, map_mul, map_inv, map_zpow, hδ₀eq]
    rfl

end Work.SSGRoute