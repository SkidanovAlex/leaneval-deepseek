import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.NK.TameStructureDeep.Tame.Unconditional
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.PTW.Prelude
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **From the global inertia condition to fixing the prime-to-`p` roots of unity.**

Let `K` be a number field, `Ω` a separable closure of `K`, `A` a finite place of `Ω` over `K`
and `p = resCharAt (primeOf A.1 A.2)` its residue characteristic, and assume (`hunit`) that every
natural number `n` prime to `p` is a unit of the valuation ring `↥A.1`.  Then every element `σ` of
the decomposition group of `A` that acts trivially on the residue field of `A`
(`SSGRoute.IsInertia K A.1 σ`) fixes every root of unity of `Ω` of order prime to `p`.

Intended proof: a primitive `n`-th root of unity `ζ` with `p ∤ n` lies in `A.1`
(`NK.TameStructureDeep.Tame.mem_valuationSubring_of_isPrimitiveRoot`), and is a unit of `A.1`;
`σ ∈ D_A` so `σ ζ ∈ A.1`, and `A.1.valuation (σ ζ - ζ) < 1`; hence `(σ ζ)/ζ ∈ ↥A.1` is a root of
unity of order `n` whose residue is `1`, and since `n` is a unit of `A.1`, reduction modulo the
maximal ideal is injective on the `n`-torsion (`NK.ResidueFrob.residue_injective_on_torsion` or
`NK.TameStructureDeep.Tame.eq_of_residue_eq_of_pow_eq_one`), giving `σ ζ = ζ`. -/
theorem fixes_rootsOfUnity_of_isInertia {K : Type} [Field K] [NumberField K] {Ω : Type}
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (A : NK.FrobeniusBridge.FinitePlaceOf K Ω)
    (hunit : ∀ n : ℕ, ¬ (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A.1 A.2)) ∣ n →
      IsUnit (n : ↥A.1))
    (σ : ↥(SSGRoute.decomp K A.1))
    (h : SSGRoute.IsInertia K A.1 (σ : Ω ≃ₐ[K] Ω)) :
    ∀ (n : ℕ), ¬ (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A.1 A.2)) ∣ n →
      ∀ ζ : Ω, IsPrimitiveRoot ζ n → (σ : Ω ≃ₐ[K] Ω) ζ = ζ := by
  intro n hn ζ hζ
  -- the order `n` is nonzero, as the residue characteristic divides `0`
  have hn0 : n ≠ 0 := fun h0 => hn ⟨0, by rw [h0, mul_zero]⟩
  -- a root of unity of order prime to the residue characteristic lies in the valuation ring
  have hmem : ζ ∈ A.1 :=
    NK.TameStructureDeep.Tame.mem_valuationSubring_of_isPrimitiveRoot A.1 hζ hn0
  let ζA : ↥A.1 := ⟨ζ, hmem⟩
  have hpow : ζA ^ n = 1 := by
    apply Subtype.ext
    change (A.1.subtype (ζA ^ n)) = (A.1.subtype 1)
    rw [map_pow, map_one]
    exact hζ.pow_eq_one
  -- `σ` as an element of the decomposition subgroup of `A.1`
  let g : ↥(A.1.decompositionSubgroup K) := ⟨(σ : Ω ≃ₐ[K] Ω), h.1⟩
  have hy_pow : (g • ζA) ^ n = 1 := by
    have hh := map_pow (MulSemiringAction.toRingHom ↥(A.1.decompositionSubgroup K) ↥A.1 g) ζA n
    rw [hpow, map_one] at hh
    rw [MulSemiringAction.toRingHom_apply] at hh
    exact hh.symm
  -- `σ ∈ I_A` acts trivially on the residue field, so `ζA` and `g • ζA` have equal residues
  have hres : IsLocalRing.residue ↥A.1 ζA = IsLocalRing.residue ↥A.1 (g • ζA) := by
    have hmem_m : (g • ζA) - ζA ∈ IsLocalRing.maximalIdeal ↥A.1 := by
      rw [ValuationSubring.valuation_lt_one_iff]
      rw [AddSubgroupClass.coe_sub, NK.Ramification.coe_smul]
      simp only [g, ζA]
      exact h.2 ζ hmem
    have hzero : IsLocalRing.residue ↥A.1 ((g • ζA) - ζA) = 0 :=
      (IsLocalRing.residue_eq_zero_iff ((g • ζA) - ζA)).mpr hmem_m
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  -- reduction modulo the maximal ideal is injective on the `n`-torsion since `(n : ↥A.1)` is a unit
  have heq : ζA = g • ζA :=
    NK.TameStructureDeep.Tame.eq_of_residue_eq_of_pow_eq_one (hunit n hn) hpow hy_pow hres
  have h2 : ((g • ζA : ↥A.1) : Ω) = (ζA : Ω) := by rw [← heq]
  rw [NK.Ramification.coe_smul] at h2
  simpa only [g, ζA] using h2

end Work.SSGRoute
