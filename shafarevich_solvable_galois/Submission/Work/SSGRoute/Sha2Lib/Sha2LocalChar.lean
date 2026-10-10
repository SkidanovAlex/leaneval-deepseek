import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.inertiaSub_frobenius_complement_inf_free
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local unramified character at a finite place

For a number field `k`, an algebraic closure `Ω`, a finite place `A` of `Ω` and a prime `p`, we
produce an additive map `φ : G_k → ZMod p` which is additive on the decomposition group
`D_A = decomp k A`, vanishes on the inertia subgroup `I_A = inertiaSub k Ω A`, is non-zero somewhere
on `D_A`, is conjugation invariant on `D_A`, and is locally constant on `D_A`.

The construction goes through a finite normal level `L ⊆ Ω` with `p` dividing the inertia degree
`f_L` of the level prime: on the level decomposition group the composite

`D_A ⟶ levelDecompAt ⟶ levelDecompAt ⧸ levelInertiaInDecompAt`

is surjective onto a finite cyclic group whose order is `f_L`, divisible by `p`, so it can be
composed with a surjection onto `ZMod p` (`Work.SSGRoute.PT.exists_surjective_hom_zmod_of_cyclic`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Pointwise NumberField

namespace Work.SSGRoute.Sha2Lib

open _root_.SSGRoute

/-- **The local unramified character at a finite place** (copied from the sibling
`aux_local_unramified_character.lean`, with the broken `PT.inertiaStructureZhat` import replaced
by an inline proof of the cyclic surjection onto `ZMod p`). -/
theorem localUnramChar (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ φ : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ a b : Ω ≃ₐ[k] Ω, a ∈ SSGRoute.decomp k A → b ∈ SSGRoute.decomp k A →
        φ (a * b) = φ a + φ b) ∧
      (∀ σ : Ω ≃ₐ[k] Ω, σ ∈ Work.SSGRoute.inertiaSub k Ω A → φ σ = 0) ∧
      (∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A ∧ φ σ ≠ 0) ∧
      (∀ σ τ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A → τ ∈ SSGRoute.decomp k A →
        φ (τ * σ * τ⁻¹) = φ σ) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) φ := by
  classical
  haveI : NumberField ↥(⊥ : IntermediateField k Ω) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField
      (K := k) (K' := Ω) (⊥ : IntermediateField k Ω)
  -- ## 1. a finite normal level `L` with `p ∣ f_L`
  obtain ⟨L, hLfd, hLnorm, hLnf, _hLle, hLdvd⟩ :=
    exists_level_inertiaDeg_mul_dvd k Ω A hA (⊥ : IntermediateField k Ω) p
      (show p ≠ 0 from (Fact.out : p.Prime).ne_zero)
  letI : FiniteDimensional k L := hLfd
  letI : Normal k L := hLnorm
  have hpdvd : p ∣ (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) := dvd_trans (dvd_mul_right p _) hLdvd
  -- ## 2. the level quotient `levelDecompAt ⧸ levelInertiaInDecompAt` is cyclic of order `f_L`
  let D : Subgroup (Ω ≃ₐ[k] Ω) := SSGRoute.decomp k A
  let Q : Subgroup (↥L ≃ₐ[k] ↥L) := Work.SSGRoute.levelDecompAt k Ω A hA L
  let R : Subgroup Q := Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L
  obtain ⟨σ, hσ⟩ := exists_isFrobLift k Ω A hA
  have hσbar : AlgEquiv.restrictNormalHom L σ ∈ Q := by
    rw [show Q = ((AlgEquiv.restrictNormalHom L).comp (Subgroup.subtype D)).range from
      (range_restrictNormalHom_eq_stabilizer A hA L).symm]
    exact ⟨⟨σ, hσ.mem_decomp⟩, rfl⟩
  have hgen := levelDecomp_zpowers_generates A hA σ hσ L hσbar
  haveI hcyc : IsCyclic (Q ⧸ R) := by
    refine isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨QuotientGroup.mk' R ⟨AlgEquiv.restrictNormalHom L σ, hσbar⟩, ?_⟩
    rw [Subgroup.eq_top_iff']
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
    obtain ⟨m, hm⟩ := hgen x
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, ?_⟩
    have h1 : (QuotientGroup.mk' R x)⁻¹ *
        (QuotientGroup.mk' R ⟨AlgEquiv.restrictNormalHom L σ, hσbar⟩) ^ m = 1 := by
      rw [← map_inv, ← map_zpow, ← map_mul]
      exact MonoidHom.mem_ker.mp (by rw [QuotientGroup.ker_mk']; exact hm)
    exact (inv_mul_eq_one.mp h1).symm
  have hcard : Nat.card (Q ⧸ R) = (Work.SSGRoute.levelPrime k Ω A hA L).asIdeal.inertiaDeg
      (NumberField.RingOfIntegers k) := by
    rw [← Subgroup.index_eq_card]
    rw [show R = Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L from rfl]
    rw [Work.SSGRoute.levelInertiaInDecompAt_eq]
    exact inertia_relIndex_stabilizer_eq_inertiaDeg A hA L
  have hpdvd' : p ∣ Nat.card (Q ⧸ R) := by rw [hcard]; exact hpdvd
  -- ## 3. a surjection of the level quotient onto `ZMod p`
  have hsurjQR : ∃ φbar : (Q ⧸ R) →* Multiplicative (ZMod p), Function.Surjective φbar := by
    let e : (Q ⧸ R) ≃* Multiplicative (ZMod (Nat.card (Q ⧸ R))) :=
      (zmodCyclicMulEquiv hcyc).symm
    let ψ : Multiplicative (ZMod (Nat.card (Q ⧸ R))) →* Multiplicative (ZMod p) :=
      AddMonoidHom.toMultiplicative ((ZMod.castHom hpdvd' (ZMod p)).toAddMonoidHom)
    refine ⟨ψ.comp e.toMonoidHom, ?_⟩
    intro y
    obtain ⟨x, hx⟩ := ZMod.castHom_surjective hpdvd' y.toAdd
    exact ⟨e.symm (Multiplicative.ofAdd x), by simp [ψ, hx]⟩
  obtain ⟨φbar, hφbar⟩ := hsurjQR
  -- ## 4. the map `D_A → levelDecompAt`
  let ρ : ↥D →* Q :=
    { toFun := fun δ => ⟨AlgEquiv.restrictNormalHom L (δ : Ω ≃ₐ[k] Ω), by
        rw [show Q = ((AlgEquiv.restrictNormalHom L).comp (Subgroup.subtype D)).range from
          (range_restrictNormalHom_eq_stabilizer A hA L).symm]
        exact ⟨δ, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hρsurj : Function.Surjective ρ := by
    intro y
    have hy : (y : ↥L ≃ₐ[k] ↥L) ∈
        ((AlgEquiv.restrictNormalHom L).comp (Subgroup.subtype D)).range := by
      rw [show ((AlgEquiv.restrictNormalHom L).comp (Subgroup.subtype D)).range = Q from
        range_restrictNormalHom_eq_stabilizer A hA L]
      exact y.2
    obtain ⟨δ, hδ⟩ := MonoidHom.mem_range.mp hy
    exact ⟨δ, Subtype.ext hδ⟩
  -- ## 5. the character on `G_k`
  let Φ : ↥D →* Multiplicative (ZMod p) := φbar.comp ((QuotientGroup.mk' R).comp ρ)
  have hΦsurj : Function.Surjective Φ :=
    hφbar.comp ((QuotientGroup.mk'_surjective R).comp hρsurj)
  let φ : (Ω ≃ₐ[k] Ω) → ZMod p := fun δ =>
    if h : δ ∈ D then (Φ ⟨δ, h⟩).toAdd else 0
  -- ## 6. the five properties
  have hadd : ∀ a b : Ω ≃ₐ[k] Ω, a ∈ D → b ∈ D → φ (a * b) = φ a + φ b := by
    intro a b ha hb
    have hab : a * b ∈ D := D.mul_mem ha hb
    simp only [φ, dif_pos ha, dif_pos hb, dif_pos hab]
    have hsub : (⟨a * b, hab⟩ : ↥D) = ⟨a, ha⟩ * ⟨b, hb⟩ := Subtype.ext rfl
    have hstep : Φ (⟨a * b, hab⟩ : ↥D) = Φ ⟨a, ha⟩ * Φ ⟨b, hb⟩ := by
      rw [hsub]
      exact map_mul Φ (⟨a, ha⟩ : ↥D) (⟨b, hb⟩ : ↥D)
    rw [hstep]
    exact rfl
  have hzero : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ Work.SSGRoute.inertiaSub k Ω A → φ σ = 0 := by
    intro δ hδ
    have hδD : δ ∈ D := inertiaSub_le_decomp k Ω A hδ
    simp only [φ, dif_pos hδD]
    have hmem : ρ ⟨δ, hδD⟩ ∈ R := by
      have h1 : (ρ ⟨δ, hδD⟩ : ↥L ≃ₐ[k] ↥L) ∈
          (Work.SSGRoute.inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom L) :=
        ⟨δ, hδ, rfl⟩
      rw [inertiaSub_image_eq_levelInertia k Ω A hA L] at h1
      rw [show R = Work.SSGRoute.levelInertiaInDecompAt k Ω A hA L from rfl,
        Work.SSGRoute.levelInertiaInDecompAt_eq, Subgroup.mem_subgroupOf]
      exact h1
    have hq : (QuotientGroup.mk' R) (ρ ⟨δ, hδD⟩) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
    have hΦ1 : Φ ⟨δ, hδD⟩ = 1 := by
      show φbar ((QuotientGroup.mk' R) (ρ ⟨δ, hδD⟩)) = 1
      rw [hq, map_one]
    rw [hΦ1]
    rfl
  have hne : ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ D ∧ φ σ ≠ 0 := by
    obtain ⟨x, hx⟩ := hΦsurj (Multiplicative.ofAdd (1 : ZMod p))
    refine ⟨(x : Ω ≃ₐ[k] Ω), x.2, ?_⟩
    have hφx : φ (x : Ω ≃ₐ[k] Ω) = (Φ x).toAdd := dif_pos x.2
    rw [hφx, hx]
    exact one_ne_zero
  have hconj : ∀ σ τ : Ω ≃ₐ[k] Ω, σ ∈ D → τ ∈ D → φ (τ * σ * τ⁻¹) = φ σ := by
    intro σ τ hσD hτD
    have h1 : τ * σ * τ⁻¹ ∈ D := D.mul_mem (D.mul_mem hτD hσD) (D.inv_mem hτD)
    simp only [φ, dif_pos hσD, dif_pos h1]
    have hsub : (⟨τ * σ * τ⁻¹, h1⟩ : ↥D) = ⟨τ, hτD⟩ * ⟨σ, hσD⟩ * ⟨τ, hτD⟩⁻¹ :=
      Subtype.ext rfl
    have hstep : Φ (⟨τ * σ * τ⁻¹, h1⟩ : ↥D)
        = Φ ⟨τ, hτD⟩ * Φ ⟨σ, hσD⟩ * (Φ ⟨τ, hτD⟩)⁻¹ := by
      rw [hsub, map_mul, map_mul, map_inv]
    rw [hstep]
    rw [mul_comm (Φ ⟨τ, hτD⟩) (Φ ⟨σ, hσD⟩), mul_assoc, mul_inv_cancel, mul_one]
  have hlc : SSGRoute.IsLocConstOn D φ := by
    refine ⟨L.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen L, ?_⟩
    intro g hg u hu huH
    have hgu : g * u ∈ D := D.mul_mem hg huH
    simp only [φ, dif_pos hg, dif_pos huH, dif_pos hgu]
    have hu1 : AlgEquiv.restrictNormalHom L u = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
      exact hu
    have h2 : ρ ⟨g * u, hgu⟩ = ρ ⟨g, hg⟩ := by
      apply Subtype.ext
      show AlgEquiv.restrictNormalHom L (g * u) = AlgEquiv.restrictNormalHom L g
      rw [map_mul, hu1, mul_one]
    have h3 : Φ ⟨g * u, hgu⟩ = Φ ⟨g, hg⟩ := by
      show φbar ((QuotientGroup.mk' R) (ρ ⟨g * u, hgu⟩)) =
        φbar ((QuotientGroup.mk' R) (ρ ⟨g, hg⟩))
      rw [h2]
    rw [h3]
  exact ⟨φ, hadd, hzero, hne, hconj, hlc⟩

end Work.SSGRoute.Sha2Lib
