import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.NK.RamificationAudit.Vocab
import Submission.NK.RamificationDeep.isCyclic_quotient_ramificationSubgroup
import Submission.NK.RamificationDeep.uniformizerData_of_isGalois
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.levelInertia_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise NumberField

namespace Work.SSGRoute.LevelInertiaProEll

/-! ## Auxiliary: the action on valuation subrings and on residue fields only depends on the
underlying field automorphism

The decomposition subgroup `A.decompositionSubgroup K` depends on the base field `K`, but if two
automorphisms (with respect to two different base fields) have the same underlying function on the
field `L`, then they act in the same way on every valuation subring of `L` and on the residue
field of `A`.  These two facts are what let us compare the inertia subgroups of `A` with respect
to different base fields. -/

/-- Two field automorphisms with the same underlying function act in the same way on a valuation
subring. -/
theorem smul_valring_ext {K K' L : Type*} [Field K] [Field K'] [Field L] [Algebra K L]
    [Algebra K' L] (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (τ : L ≃ₐ[K'] L)
    (h : ∀ x : L, σ • x = τ • x) : σ • A = τ • A := by
  ext y
  rw [ValuationSubring.mem_smul_pointwise_iff_exists, ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, hz, hzy⟩; exact ⟨z, hz, by rw [← h z, hzy]⟩
  · rintro ⟨z, hz, hzy⟩; exact ⟨z, hz, by rw [h z, hzy]⟩

/-- Two elements of the decomposition subgroup (with respect to two different base fields) acting
by the same function on `L` act in the same way on the residue field of `A`. -/
theorem residue_smul_eq_of_field_eq {K K' L : Type*} [Field K] [Field K'] [Field L] [Algebra K L]
    [Algebra K' L] (A : ValuationSubring L)
    (σ : A.decompositionSubgroup K) (τ : A.decompositionSubgroup K')
    (h : ∀ x : L, (σ : L ≃ₐ[K] L) x = (τ : L ≃ₐ[K'] L) x)
    (w : IsLocalRing.ResidueField A) : σ • w = τ • w := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective w
  rw [← IsLocalRing.ResidueField.residue_smul, ← IsLocalRing.ResidueField.residue_smul]
  congr 1
  apply Subtype.ext
  rw [NK.Ramification.coe_smul, NK.Ramification.coe_smul]
  exact h (x : L)

/-- Membership in the inertia subgroup is acting trivially on the residue field. -/
theorem mem_inertiaSubgroup_iff_smul {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : A.decompositionSubgroup K) :
    σ ∈ A.inertiaSubgroup K ↔ ∀ w : IsLocalRing.ResidueField A, σ • w = w := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  constructor
  · intro h w
    have := DFunLike.congr_fun h w
    simpa [MulSemiringAction.toRingAut_apply] using this
  · intro h
    ext w
    simpa [MulSemiringAction.toRingAut_apply] using h w

/-- **The inertia subgroups with respect to two base fields coincide** as soon as the two
automorphisms have the same underlying function on `L`. -/
theorem mem_inertiaSubgroup_congr {K K' L : Type*} [Field K] [Field K'] [Field L] [Algebra K L]
    [Algebra K' L] (A : ValuationSubring L)
    (σ : A.decompositionSubgroup K) (τ : A.decompositionSubgroup K')
    (h : ∀ x : L, (σ : L ≃ₐ[K] L) x = (τ : L ≃ₐ[K'] L) x) :
    (σ ∈ A.inertiaSubgroup K) ↔ (τ ∈ A.inertiaSubgroup K') := by
  rw [mem_inertiaSubgroup_iff_smul, mem_inertiaSubgroup_iff_smul]
  constructor <;> intro hh w
  · rw [← residue_smul_eq_of_field_eq A σ τ h w, hh w]
  · rw [residue_smul_eq_of_field_eq A σ τ h w, hh w]

/-! ## The uniformizer data at a finite level

`B := A.comap (algebraMap ↥M Ω)` is a valuation subring of the finite normal extension `M/k`.  It
is not in general stable under all of `Gal(M/k)`, but it *is* stable under the Galois group of `M`
over the fixed field `Z` of its decomposition subgroup `D = B.decompositionSubgroup k`: over `Z`
the extension is Galois with group `D`, and `D` is by definition the stabiliser of `B`.  Applying
the uniformizer criterion over `Z` (`NK.RamificationDeep.uniformizerData_of_isGalois`) and then
viewing the resulting inertia field as an intermediate field of `M/k` gives the statement: the
`fixes` clause transfers because the inertia subgroup with respect to `k` is the inertia subgroup
with respect to `Z`, and the two remaining clauses do not see the base field. -/

theorem levelRingUniformizerData
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M]
    [IsDiscreteValuationRing (A.comap (algebraMap ↥M Ω))]
    [IsNoetherianRing (A.comap (algebraMap ↥M Ω))]
    [PerfectField (IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω)))]
    [Finite ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k)] :
    ∃ (π : A.comap (algebraMap ↥M Ω)) (E : IntermediateField k ↥M),
      NK.RamificationDeep.UniformizerData (K := k) (A.comap (algebraMap ↥M Ω)) π E := by
  haveI hgal : IsGalois k ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  let B : ValuationSubring ↥M := A.comap (algebraMap ↥M Ω)
  haveI : IsDiscreteValuationRing B := ‹IsDiscreteValuationRing (A.comap (algebraMap ↥M Ω))›
  haveI : IsNoetherianRing B := ‹IsNoetherianRing (A.comap (algebraMap ↥M Ω))›
  haveI : PerfectField (IsLocalRing.ResidueField B) :=
    ‹PerfectField (IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω)))›
  haveI : Finite ↥(B.decompositionSubgroup k) :=
    ‹Finite ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k)›
  -- the decomposition subgroup of `B` over `k`, and the fixed field `Z` of `B`
  let D : Subgroup (↥M ≃ₐ[k] ↥M) := B.decompositionSubgroup k
  haveI hDfin : Finite ↥D := ‹Finite ↥(B.decompositionSubgroup k)›
  let Z : IntermediateField k ↥M := IntermediateField.fixedField D
  have hZ : Z.fixingSubgroup = D := IntermediateField.fixingSubgroup_fixedField D
  haveI : Fintype (↥M ≃ₐ[k] ↥M) := AlgEquiv.fintype k ↥M
  haveI : Finite (↥M ≃ₐ[Z] ↥M) :=
    Finite.of_injective (AlgEquiv.restrictScalars k) (AlgEquiv.restrictScalars_injective k)
  -- `B` is stable under `Gal(M/Z) = D`
  have htop : B.decompositionSubgroup Z = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro τ
    have hfix : τ.restrictScalars k ∈ Z.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have h1 : τ x = x := by
        have := AlgEquiv.commutes τ (⟨x, hx⟩ : Z)
        simpa using this
      simpa using h1
    have hD : τ.restrictScalars k ∈ B.decompositionSubgroup k := by
      rw [show B.decompositionSubgroup k = Z.fixingSubgroup from hZ.symm]
      exact hfix
    have hstab : τ.restrictScalars k • B = B := hD
    rw [MulAction.mem_stabilizer_iff]
    trans τ.restrictScalars k • B
    · exact (smul_valring_ext B (τ.restrictScalars k) τ (fun x => rfl)).symm
    · exact hstab
  haveI : Finite ↥(B.decompositionSubgroup Z) := by
    rw [htop]
    exact Finite.of_injective (fun x => (x : ↥M ≃ₐ[Z] ↥M)) Subtype.val_injective
  haveI : IsGalois Z ↥M := IsGalois.tower_top_intermediateField Z
  obtain ⟨π, E', hUD⟩ := NK.RamificationDeep.uniformizerData_of_isGalois (K := ↥Z) B htop
  refine ⟨π, E'.restrictScalars k, hUD.maximalIdeal_eq, ?_, ?_⟩
  · -- `E := E'` is pointwise fixed by the inertia subgroup of `B` over `k`
    intro σ hσmem x
    have hσG0' : σ ∈ B.inertiaSubgroup k := by
      rw [← NK.Ramification.ramificationSubgroup_zero]
      exact hσmem
    have hσZ : (σ : ↥M ≃ₐ[k] ↥M) ∈ Z.fixingSubgroup := by rw [hZ]; exact σ.2
    let τ : ↥M ≃ₐ[↥Z] ↥M := IntermediateField.fixingSubgroupEquiv Z ⟨(σ : ↥M ≃ₐ[k] ↥M), hσZ⟩
    have hτcoe : ∀ y : ↥M, τ y = (σ : ↥M ≃ₐ[k] ↥M) y := fun y => rfl
    have hτtop : τ ∈ B.decompositionSubgroup ↥Z := by rw [htop]; exact Subgroup.mem_top _
    have hτG0 : (⟨τ, hτtop⟩ : B.decompositionSubgroup ↥Z)
        ∈ NK.Ramification.ramificationSubgroup (K := ↥Z) B 0 := by
      rw [NK.Ramification.ramificationSubgroup_zero]
      exact (mem_inertiaSubgroup_congr B σ ⟨τ, hτtop⟩ (fun y => (hτcoe y).symm)).mp hσG0'
    rw [← hτcoe (x : ↥M)]
    exact hUD.fixes ⟨τ, hτtop⟩ hτG0 x
  · -- the monogeneity clause does not see the base field
    intro x
    obtain ⟨q, hq1, hq2⟩ := hUD.generated x
    exact ⟨q, hq1, hq2⟩

end Work.SSGRoute.LevelInertiaProEll
