import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
import Submission.Work.SSGRoute.ZConstruction.AuxChase
import Submission.Work.SSGRoute.ZConstruction.AuxAssembly
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.Work.SSGRoute.ZConstruction.LevelKRealisationCounting
import Submission.Work.SSGRoute.eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The realisation gate of the `z`-construction in its *honest* dual form

`Work.SSGRoute.AuxRealisationNoInv` (`ZConstruction/AuxAssembly.lean`) is the gate carrying the
realisation obligation of Schmidt--Wingberg's §4 for odd `p`, in the vocabulary of the node
`Work.SSGRoute.shafarevich_z_construction`.  As filed it takes as its orthogonality hypothesis

  `∀ b, IsRelaxedDual K Λ T b → ∑_{A ∈ T'} pair (D_A ⊓ G_K) (f A) b = 0`,

i.e. orthogonality of the prescribed datum against the *relaxed dual* classes of the p. 18 chase
(`Work.SSGRoute.auxDatum_orthogonal_of_productFormula`), and its conclusion prescribes the local
data at the *enlarged* place set `T'` (in particular, `0` at `T'∖T`).

The present file makes the realisation half of the gate independent of the chase: it proves the
degree-one realisation of prescribed local data from the *honest* dual condition

  `Work.SSGRoute.ZDataMup.IsOrthogonalToDual K pair T f`,

orthogonality against *every* global cocycle unramified outside the level-`K` classes of `T`.  The
arithmetic consumed is `Work.SSGRoute.ZConstruction.levelK_realisation_of_counting`
(`ZConstruction/LevelKRealisationCounting.lean`), which is the level-`K` degree-one realisation of
the `ZDataMup` lane with the level-`K` counting inequality as an **explicit hypothesis** -- the
standing version of that rung (`ZDataMup/tatePoitou_h1_realisation.lean`) was removed from the
workspace after its standing assumption was shown to be false without an `hSram`-type hypothesis on
`T` (see `ZDataMup/TATEPOITOU_STATUS.md`, section "The counterexample"); the statement here carries
that hypothesis explicitly, so no false standing assumption is used.

Consequently the content of this file is purely formal:

* `Work.SSGRoute.ZConstruction.exists_realisation_of_orthogonalToDual` -- realisation at the base
  place set `T`: pointwise agreement on the local groups of `cs(T)` and unramifiedness at every
  finite place outside `cs(T)`;
* `Work.SSGRoute.ZConstruction.exists_realisation_of_orthogonalToDual_odd` -- the same with the
  *relaxation* and the *involution* clauses of `Work.SSGRoute.AuxRealisationExt`, for odd `p`.  The
  relaxation is weaker than the unramifiedness already obtained; the involution clause is free for
  odd `p` by `Work.SSGRoute.eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot` (no element of order
  two of `G_K` fixes a primitive `p`-th root of unity), exactly as in
  `Work.SSGRoute.auxRealisationExt_of_noInv`.

## What this says about the node

The obligation is the *auxiliary class* of p. 18: a class with the local data of the line component
`y₁` on `cs(S)`, with inertia-killing (respectively vanishing) on `cs(S') ∖ cs(S)`, and satisfying
`ZHyp` at `(N, S')`.  The realisation half is proved here; what is *not* proved here is the passage
from the relaxed-dual orthogonality produced by the chase to the honest one consumed above -- the
two families are different: every relaxed dual is unramified outside `cs(T)`, so relaxed-dual
orthogonality is orthogonality against a family *contained* in the family of `IsOrthogonalToDual`,
i.e. a *weaker* hypothesis.  The chase therefore has to be strengthened, and the place sets of the
gate re-chosen; see `ZConstruction/NOTE_p18_interface.lean` for the analysis.
-/

open scoped Pointwise BigOperators

open Classical

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- **The degree-one realisation of prescribed local data at level `K`, from orthogonality against
the honest dual.**  For odd `p`, local data `f` at a finite, level-`K`-nonsingular set `T` of finite
places which is orthogonal (`ZDataMup.IsOrthogonalToDual`) to every global cocycle unramified
outside the level-`K` classes of `T` is realised by a global cocycle `z` which agrees with `f` on
the level-`K` local group of every place of `T` and is unramified at every finite place outside
`cs(T)`.  The counting inequality of the level-`K` localisation is an explicit hypothesis
(`Work.SSGRoute.ZConstruction.levelK_realisation_of_counting`); the `hSram`-type hypothesis records
the place set for which it is satisfiable (see the module docstring). -/
theorem exists_realisation_of_orthogonalToDual (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : ZDataMup.IsProductFormula p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, KConj K A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ T, KConj K A B)
    {f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p}
    (hf : ∀ A ∈ T, SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A))
    (horth : ZDataMup.IsOrthogonalToDual p k Ω K pair T f)
    (hcount : Module.finrank (ZMod p)
        (↥(ZDataMup.localDataSpace (p := p) K T) ⧸ ZDataMup.localVanish (p := p) K T) ≤
      2 * Module.finrank (ZMod p)
        (((ZDataMup.localImageIn (p := p) K T) ⊔ ZDataMup.localVanish (p := p) K T).map
          (Submodule.mkQ (ZDataMup.localVanish (p := p) K T)))) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = f A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∀ A ∈ T, ¬ KConj K A B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  obtain ⟨z, hzc, hzl, hzcob, hzunr⟩ :=
    levelK_realisation_of_counting p hp k Ω K pair hpair hrec T hTfin
      (fun A hA B hB h => hTdisj A hA B hB (kConj_of_forall_mem h)) f hf horth hcount
  refine ⟨z, hzc, hzl, ?_, ?_⟩
  · intro A hA σ hσ
    exact (ZDataMup.sub_isCoboundaryOn_iff_eqOn (K := K) inf_le_right z (f A)).mp
      (hzcob A hA) σ hσ
  · intro B hB hnot σ hσK hσI
    exact hzunr B hB (fun A hA hconj => hnot A hA (kConj_of_forall_mem hconj)) σ hσK hσI

/-- **The realisation with the relaxation and involution clauses of the gate.**  Same statement as
the *conclusion* of `Work.SSGRoute.AuxRealisationNoInv` (and, for odd `p`, of
`Work.SSGRoute.AuxRealisationExt`), with the honest dual hypothesis `IsOrthogonalToDual`. -/
theorem exists_realisation_of_orthogonalToDual_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ M : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [FiniteDimensional k Λ] [IsGalois k Λ] [FiniteDimensional k M] [IsGalois k M] (hKM : K ≤ M)
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hrec : ZDataMup.IsProductFormula p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, KConj K A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ T, KConj K A B)
    {f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p}
    (hf : ∀ A ∈ T, SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A))
    (horth : ZDataMup.IsOrthogonalToDual p k Ω K pair T f)
    (hcount : Module.finrank (ZMod p)
        (↥(ZDataMup.localDataSpace (p := p) K T) ⧸ ZDataMup.localVanish (p := p) K T) ≤
      2 * Module.finrank (ZMod p)
        (((ZDataMup.localImageIn (p := p) K T) ⊔ ZDataMup.localVanish (p := p) K T).map
          (Submodule.mkQ (ZDataMup.localVanish (p := p) K T))))
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = f A σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∀ A ∈ T, ¬ KConj K A B) →
        ¬ SSGRoute.IsSplitIn k M B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  obtain ⟨z, hzc, hzl, hza, hzu⟩ :=
    exists_realisation_of_orthogonalToDual p hp k Ω K Λ pair hpair hrec T hTfin hTdisj hSram
      hf horth hcount
  refine ⟨z, hzc, hzl, hza, ?_, ?_⟩
  · intro c hc hc2
    have hc1 : c = 1 := by
      have hcc : c.toRingEquiv * c.toRingEquiv = 1 := by
        ext x
        have h : c (c x) = x := by
          have h2 := congrArg (fun (g : Ω ≃ₐ[k] Ω) => g x) hc2
          simpa using h2
        simpa using h
      have hfix : c.toRingEquiv ζ = ζ := by
        have h : c ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff K c).mp hc ζ hζK
        simpa using h
      have h := eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot (c.toRingEquiv) hcc
        (Fact.out : p.Prime) hp hζ hfix
      ext x
      have h2 := congrArg (fun (g : Ω ≃+* Ω) => g x) h
      simpa using h2
    rw [hc1]
    exact Work.SSGRoute.z_one (addOn_of_isCocycleOn hzc)
  · intro B hB hnot hns σ hσK hσI
    exact hzu B hB hnot σ hσK hσI

end Work.SSGRoute.ZConstruction
