import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.MupCoreKummer
import Submission.Work.SSGRoute.ZConstruction.MupCoreTwo
import Submission.Work.SSGRoute.ZConstruction.OrthHsplitBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- The heavy input of this file (the `p = 2` orthogonality `Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow`
-- and its companions) is the only reason a module in the node's import cone sees
-- `Submission.Work.SSGRoute.sha2_defs`, which declares the *direct* trivial-action instance
-- `Work.SSGRoute.Triv.instSMulOfOne : SMul Γ (ZMod p)` (for every `One Γ`; `Triv p` is an `abbrev`
-- for `ZMod p`).  That instance competes with the `SMul` derived from a
-- `DistribMulAction (K ≃ₐ[k] K) (ZMod p)` binder (in particular from a *local* one), so instance
-- search can resolve the hidden `SMul (K ≃ₐ[k] K) (ZMod p)` argument of an `SMulCommClass` goal in
-- two ways that must agree --- and downstream modules with the local binders
-- (`ZConstruction/ZDataGeneral.lean`, the node and its importers) then fail with "failed to
-- synthesize instance of type class `SMulCommClass Gal(↥K/k) (ZMod p) (ZMod p)`" although a local
-- instance of that class is in scope.
--
-- The instance below restores determinism by raising the priority of the *projection*
-- `DistribSMul.toSMul` above that direct instance: the `SMul` argument is then always the one derived
-- from the `DistribSMul`/`DistribMulAction` instance in scope, which is exactly what the signatures
-- of the workspace's `IsMupZData`/`IsYRealisation`-style definitions expect.

/-!
# The `z`-construction of the node, above the orthogonality gate

`Work.SSGRoute.ZConstruction.ZDataGeneral` isolates the `z`-construction of Schmidt--Wingberg §4 as
the obligation `Work.SSGRoute.z_data_general` (the raw form, and its ramified half
`Work.SSGRoute.z_data_general_of_ramified`).  With the two `μ_p` cores and the `p = 2` two-field
narrow orthogonality available, that obligation is discharged here, at *every* prime:

* odd `p`: `Work.SSGRoute.z_data_general_of_ramified_of_core_odd` (`ZConstruction/ZDataGeneral.lean`),
  i.e. the Grünwald-with-escape realisation of `Work.SSGRoute.zDataGeneralOfMupAndZeta` with the
  odd `μ_p` core `Work.SSGRoute.z_data_mup_core` as the one-dimensional gate (its `hKimag` hypothesis
  is a function out of the empty type `p = 2`, hence vacuous);
* `p = 2`: the two-field narrow realisation, i.e. `Work.SSGRoute.ZConstruction.mu2EscapeTwoField`
  together with the orthogonality theorem `Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow` (packaged as
  `Work.SSGRoute.ZConstruction.TwoFieldOrthogonalityAll` by
  `ZConstruction/OrthHsplitBridge.lean`) and the `μ₂` core `Work.SSGRoute.shafarevich_z_data_two`.
  The prime-`2` correction (the involutions clause, i.e. total positivity of the escape element) is
  supplied *inside* the realisation, so no `hKimag`-type hypothesis is used --- this is the place
  where the `p = 2` case of the node is closed.

This file lives *above* `ZConstruction/ZDataGeneral.lean` because these two inputs (the orthogonality
theorem, whose `p = 2` companions live in the `NoKimag`/`ZDataTwo`/`H9Narrow` directories) are above
`ZDataGeneral` in the import DAG: the two statements
`Work.SSGRoute.z_data_general` and `Work.SSGRoute.z_data_general_of_ramified` are declared here, with
exactly the statements they have in `ZDataGeneral`'s documentation, so that the node
`Work.SSGRoute.shafarevich_z_construction` (which imports this file) consumes them unchanged. -/

open scoped Pointwise

namespace Work.SSGRoute

/-- A high-priority copy of the projection instance `DistribSMul.toSMul` (see the note at the top of
this file): the `SMul` argument of an `SMulCommClass` goal is resolved from the
`DistribSMul`/`DistribMulAction` instance in scope rather than from the direct instance
`Work.SSGRoute.Triv.instSMulOfOne`. -/
instance (priority := 1300) ssgDistribSMulToSMul {G M : Type*} [AddZeroClass M]
    [inst : DistribSMul G M] : SMul G M :=
  inst.toSMul

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The `z`-data in the ramified case** (the residual obligation of this node): `y` is ramified at
some place outside `cs(S)`, hence (by `hyS`) at a place that is split in `Λ`.  This is the case
that Schmidt--Wingberg's §4 construction handles: the ramification of `y` at the split-in-`Λ`
places outside `cs(S)` has to be moved onto new primes with cyclic local components. -/
theorem z_data_general_of_ramified (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hyram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y σ ≠ 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
            z δ ∈ AddSubgroup.zmultiples (z g)) ∧
        (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)) := by
  classical
  by_cases hp2 : p = 2
  · -- ## `p = 2`: the two-field narrow realisation of the `NoKimag` lane
    --
    -- The prime-`2` correction is *inside* the realisation: `ZConstruction/mu2EscapeTwoField.lean`
    -- produces the escape element totally positive, so that the realised class vanishes on the
    -- involutions (the datum's `hyinf`), and no `hKimag`-type hypothesis is used.  The
    -- orthogonality input is the two-field narrow orthogonality
    -- `Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow`, in the shape of the gate
    -- `Work.SSGRoute.ZConstruction.TwoFieldOrthogonalityAll` (`ZConstruction/OrthHsplitBridge.lean`),
    -- and the one-dimensional gate is the `μ₂` core `Work.SSGRoute.shafarevich_z_data_two`.
    subst hp2
    haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
    have hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (by simpa using hζ)
        (algebraMap ↥K Ω).injective
    have horthAll : ZConstruction.TwoFieldOrthogonalityAll (k := k) (Ω := Ω) K ζ hζ hζK hζK' :=
      ZConstruction.twoFieldOrthogonalityAll_of_orthHsplitTwoNarrow k Ω K ζ hζ hζK hζK'
    have hreal : ZConstruction.AuxRealisationGate (p := 2) (K := K) (ζ := ζ) (hζ := hζ)
        (hζK := hζK) :=
      ZConstruction.auxRealisationGate_of_twoField k Ω hζ hζK hζK' horthAll
    -- the one-dimensional gate at `p = 2`, through the `ZDataTwo` lane's live Kummer core
    -- (`Work.SSGRoute.isMupZData_of_kummerCoreTwo`, `ZConstruction/MupCoreTwo.lean`) rather than
    -- through the `sorry` of `shafarevich_z_data_two.lean`
    have hμ2 : IsMupZData 2 k Ω K := isMupZData_of_kummerCoreTwo k Ω K ζ hζ hζK
    obtain ⟨z, hz⟩ := ZDataGen.zDataGeneralOfMupAndZetaGen (p := 2) (k := k) (Ω := Ω) (K := K)
      ζ hζ hζK hreal hμ2 E Λ hKΛ S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf
    exact ⟨z, hz⟩
  · -- ## odd `p`: the Grünwald-with-escape realisation, with the one-dimensional gate supplied by
    -- the *live* Kummer-core route (`Work.SSGRoute.isMupZData_of_kummerCore`,
    -- `ZConstruction/MupCoreKummer.lean`), i.e. by the `H9` lane's chain, rather than by the stale
    -- sketches of `z_data_mup_arith.lean`
    exact z_data_general_of_ramified_odd p hp2 k Ω ⟨hKΛ, ζ, hζ, hζK, hSfin, hSdisj, hSram⟩
      (isMupZData_of_kummerCore (p := p) (k := k) (Ω := Ω) (K := K) hp2 ζ hζ hζK) E y
      ⟨hy, hyc, hyS, hyT, hy0, hyinf⟩

/-- **Schmidt--Wingberg §4: the auxiliary class `z`** (the sharpened condition (b) with the
ramification trigger), in the generality needed by `Work.SSGRoute.shafarevich_z_construction`. -/
theorem z_data_general (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
            z δ ∈ AddSubgroup.zmultiples (z g)) ∧
        (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)) := by
  classical
  by_cases hram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y σ ≠ 0
  · exact z_data_general_of_ramified p k Ω K Λ hKΛ ζ hζ hζK E S hSfin hSdisj hSram y hy hyc
      hyS hyT hy0 hyinf hram
  · refine z_data_general_of_unramified p k Ω K Λ hKΛ ζ hζ hζK E S hSfin hSdisj hSram y hy hyc
      hyS hyT hy0 hyinf ?_
    intro B hB hconj σ hσK hσI
    by_contra hne
    exact hram ⟨B, hB, hconj, σ, hσK, hσI, hne⟩

end Work.SSGRoute
