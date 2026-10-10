import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Commons.RepresentationTheory.GroupCohomology

theorem exists_addOrderOf_eq_card_of_cyclic_norm_quotient
    {B E : Type} [Field B] [Field E] [Algebra B E] [FiniteDimensional B E] [IsGalois B E]
    [IsCyclic (E ≃ₐ[B] E)] (x : Bˣ)
    (hx : ∀ k : ℕ, x ^ k ∈ MonoidHom.range (Units.map (Algebra.norm B : E →* B)) ↔
      Nat.card (E ≃ₐ[B] E) ∣ k) :
    ∃ α : groupCohomology (Rep.ofAlgebraAutOnUnits B E) 2,
      addOrderOf α = Nat.card (E ≃ₐ[B] E) := by
  classical
  letI : CommGroup (E ≃ₐ[B] E) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E ≃ₐ[B] E)
  let w : Eˣ := Units.map (algebraMap B E : B →* E) x
  have hfix : (Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)).ρ g (Additive.ofMul w)
      = Additive.ofMul w := by
    show Additive.ofMul (g • w) = Additive.ofMul w
    congr 1
    rw [AlgEquiv.smul_units_def]
    ext
    simp [w, AlgEquiv.commutes]
  have hmk : (Rep.Hom.hom ((Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)).applyAsHom g
        - 𝟙 (Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)))).toLinearMap
        (Additive.ofMul w) = 0 := by
    have h : Rep.Hom.hom ((Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)).applyAsHom g
          - 𝟙 (Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)))
        = Rep.Hom.hom ((Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)).applyAsHom g)
          - Rep.Hom.hom (𝟙 (Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ))) := rfl
    rw [h]
    show (Rep.Hom.hom ((Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)).applyAsHom g)
        - Rep.Hom.hom (𝟙 (Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)))).toLinearMap
        (Additive.ofMul w) = 0
    rw [Representation.IntertwiningMap.sub_toLinearMap, LinearMap.sub_apply]
    change (Rep.Hom.hom ((Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)).applyAsHom g))
        (Additive.ofMul w)
      - (Rep.Hom.hom (𝟙 (Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)))) (Additive.ofMul w) = 0
    rw [Rep.applyAsHom_apply, Rep.hom_id, Representation.IntertwiningMap.id_apply]
    rw [hfix]
    exact sub_self _
  let u : LinearMap.ker (Rep.Hom.hom ((Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)).applyAsHom g
        - 𝟙 (Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)))).toLinearMap :=
    ⟨Additive.ofMul w, LinearMap.mem_ker.mpr hmk⟩
  let π := Rep.FiniteCyclicGroup.groupCohomologyπEven
    (Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)) g hg 2 (by norm_num)
  refine ⟨π u, ?_⟩
  have hdvd : addOrderOf (π u) ∣ Nat.card (E ≃ₐ[B] E) :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr
      (natCard_nsmul_H2_eq_zero (Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)) (π u))
  have hkill : ∀ k : ℕ, k • (π u) = 0 → Nat.card (E ≃ₐ[B] E) ∣ k := by
    intro k hk
    have hk0 : π (k • u) = 0 := by
      rw [show π (k • u) = k • π u from map_nsmul (ConcreteCategory.hom π) k u, hk]
    rw [Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff] at hk0
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hk0
    set y : Eˣ := Additive.toMul (Rep.toAdditive z) with hy
    have hnorm : Additive.toMul (Rep.toAdditive
        ((Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)).norm.hom
          (Rep.toAdditive.symm (Additive.ofMul y))))
        = Units.map (algebraMap B E : B →* E) (Units.map (Algebra.norm B : E →* B) y) := by
      apply Units.ext
      rw [Units.coe_map, Units.coe_map]
      exact groupCohomology.norm_ofAlgebraAutOnUnits_eq (K := B) (L := E) y
    have hsymm : Rep.toAdditive.symm (Additive.ofMul y) = z := by
      simp only [hy, ofMul_toMul, Rep.toAdditive_symm_apply, Rep.toAdditive_apply]
    rw [hsymm] at hnorm
    have hzu : (k • u).1 = Additive.ofMul (w ^ k) := by
      have h1 : (k • u).1 = (k • Additive.ofMul w : Additive (Eˣ)) := rfl
      rw [h1, ← ofMul_pow]
    have hza : (Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)).norm.hom z = Additive.ofMul (w ^ k) := by
      have h1 : (Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)).norm.hom z = (k • u).1 := by
        rw [← hz]; rfl
      rw [h1, hzu]
    have hL : Additive.toMul (Rep.toAdditive
        ((Rep.ofMulDistribMulAction (E ≃ₐ[B] E) (Eˣ)).norm.hom z)) = w ^ k := by
      rw [hza, Rep.toAdditive_apply, toMul_ofMul]
    have hnorm' : w ^ k = Units.map (algebraMap B E : B →* E)
        (Units.map (Algebra.norm B : E →* B) y) := by
      rw [← hL]
      exact hnorm
    have hwk : w ^ k = Units.map (algebraMap B E : B →* E) (x ^ k) := by
      simp only [w, map_pow]
    have hinj : Function.Injective (Units.map (algebraMap B E : B →* E)) := by
      intro a b hab
      ext
      exact FaithfulSMul.algebraMap_injective B E
        (by simpa using congrArg (fun u : Eˣ => (u : E)) hab)
    have heq : Units.map (algebraMap B E : B →* E) (Units.map (Algebra.norm B) y)
        = Units.map (algebraMap B E : B →* E) (x ^ k) := by
      rw [← hnorm', ← hwk]
    exact (hx k).mp (MonoidHom.mem_range.mpr ⟨y, hinj heq⟩)
  exact Nat.dvd_antisymm hdvd (hkill (addOrderOf (π u)) (addOrderOf_nsmul_eq_zero (π u)))

end Commons.RepresentationTheory.GroupCohomology
