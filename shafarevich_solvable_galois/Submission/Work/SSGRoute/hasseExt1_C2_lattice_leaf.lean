import Mathlib
import Submission.Work.SSGRoute.ExtChain.himgIdelesInput_inf
import Submission.Work.SSGRoute.ExtChain.himgExtDeltaInput_inf
import Submission.Work.SSGRoute.ExtChain.hasseExt1_C2_lattice_general
import Submission.Work.SSGRoute.E1aFinal.hasseExt1_C2_lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The involution half of node `E1a` is CLOSED — the `p = 2` leaf, axiom-clean

Written by the agent of `Work.SSGRoute.pt_selmer_relaxed` (2026-10-02/03), as part of rebuilding the
E9 route after the `nsmul_ofMul` fix.

## 0. What is closed here

`Work.SSGRoute.ExtChain.himg_involution_input_two` (`p = 2`, the prime-2 correction — the only
`sorry` of `ExtChain/himgIdelesInput_inf.lean`, at line 587) is **proved, axiom-clean**, as

* `himg_involution_input_two_clean` — from the proved `C₂`-lattice Hasse principle
  `Work.SSGRoute.E1aFinal.hasseExt1_C2_lattice`, via the **proved** reduction
  `ExtChain.himg_involution_input_two_of_latticeHasse`;

and hence so are its two consumers, both stated verbatim as the sorried originals:

* `himgIdelesInput_inf_clean` — the involutive half of the `himg` input
  (drop-in replacement for the sorried `ExtChain.himgIdelesInput_inf`);
* `himgExtDeltaInput_inf_clean` — the `p = 2` branch of `ExtChain.himgExtDeltaInput_inf`
  (`ExtChain/himgExtDeltaInput_inf.lean:50`; the same statement, as that file records).

`#print axioms` of all three is `[propext, Classical.choice, Quot.sound]` (measured).  So the
**involution/archimedean `p = 2` half of E1a is done**, and with it the
`pt_selmer_relaxed → COUNT → tatePoitouEmbedding → E1a → himg_involution_input_two →
pt_selmer_relaxed` cycle of `PING_pt_relaxed_s8_extchain_cycle.md` is broken: the lattice-Hasse
route uses no local pairing and no `pt_selmer_relaxed`.

The two theorems at the end (`…_of_hasseExt1`) state the same two assemblies against the *sorried*
`ExtChain.hasseExt1_C2_lattice_general`; they are kept so the reduction is on record whichever copy
of the `C₂`-lattice Hasse principle is adopted.

## 1. What is *not* closed — and a one-word blocker

**Correction of an earlier claim of mine.**  `ExtChain/himgIdelesInput_fin.lean` is **not**
`sorry`-free: it ends in a `sorry` at line 1635, for `ExtChain.himgIdelesInput_fin` (the
finite-place half of the same `himg` input).  So on the `ext_sha2_bridge` route the finite-place
piece is still missing; per `_lead_design/ssg_pt_design_1002/DESIGN.md` §3 this is the "nonsplit
finite places" crux, also spelled `Work.SSGRoute.E1aClean.finLocalCriterion` (an isolated `sorry`
which imports `himgIdelesInput_fin`).

**Blocker (measured, needs the owner of one of the two files).**
`Work.SSGRoute.ExtChain.extToIdeles_extDelta_eq_zero` is declared **twice** in the same namespace:

* `ExtChain/himgIdelesInput_fin.lean:829` — `(k K : Type) …` (used only inside that file, at
  line 1060, plus one `#print axioms` probe), and
* `ExtChain/himgIdelesInput_inf.lean:306` — `{k Ω K M r}` implicit, `(x)`.

Consequently **no module can import both `ExtChain.himgIdelesInput_fin` and
`ExtChain.himgIdelesInput_inf`** (`environment already contains
'Work.SSGRoute.ExtChain.extToIdeles_extDelta_eq_zero'`).  This matters because the intended
closure of the remaining leaf `ExtChain.extToIdeles_eq_zero_imp_chainC_locallyTrivial` (its own
docstring: "the target closes in two lines as soon as those two land", by applying
`ExtChain.himg_of_ideles_input` to `himgIdelesInput_fin` and `himgIdelesInput_inf`) **cannot even
be written today**.  One-word fix, for the owner of `himgIdelesInput_fin.lean`: make line 829
`private` (its only in-tree uses are line 1060 of the same file and a `#print axioms` probe), or
rename it.  Then my `himgIdelesInput_inf_clean` plus `himgIdelesInput_fin` closes the leaf in the
two lines the docstring prescribes, with `[hRfin : Module.Finite ℤ ↥(kernel (freeCover (e1aN0 …)))]`
supplied explicitly (it is a binder of both inputs and of `himg_of_ideles_input`, and it is *not* a
global instance).

**Scope warning (measured, see `SSGRoute/FRONTIER_MAP_2026-10-03.md`).**  Branch A
(`Work.SSGRoute.stage_global_lifting`) reaches only `PT.e1aBetaCan_le_ker` and
`Work.Sha2Lib.unramifiedDetector` in its proof term, so it does **not** use `ext_sha2_bridge`;
everything here is on `ext_sha2_bridge`'s own route (`tatePoitouEmbedding`), a *parallel* route for
the same content.
-/

namespace Work.SSGRoute.ExtChain

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

/-- **The `p = 2` leaf of `E1a`, axiom-clean**, from the proved `C₂`-lattice Hasse principle
`Work.SSGRoute.E1aFinal.hasseExt1_C2_lattice`. -/
theorem himg_involution_input_two_clean (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (y : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)
      (SSGRoute.PTExt.unitsK k K) 2)
    (hy : SSGRoute.PTExt.extToIdeles (k := k) y = 0) :
    Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y) = 0 :=
  himg_involution_input_two_of_latticeHasse (k := k) (Ω := Ω) (K := K) (N := _) σ hσ hnt
    (fun M _ _ => Work.SSGRoute.E1aFinal.hasseExt1_C2_lattice p k Ω K σ hσ hnt M) y hy

/-- **A drop-in replacement for the sorried `ExtChain.himgIdelesInput_inf`** (same statement),
axiom-clean, with the `p = 2` case supplied by `himg_involution_input_two_clean` and the `p ≠ 2`
case by the proved `ExtChain.himg_involution_input_odd`. -/
theorem himgIdelesInput_inf_clean (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1) :
    Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0 := by
  haveI := hRfin
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  refine resH1_zpowers_e1cMap_eq_zero_of_resH2_e1aChainH_eq_zero (k := k) (Ω := Ω) (K := K)
    (N := Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) σ hσ z ?_
  rcases eq_or_ne p 2 with h2 | h2
  · exact himg_involution_input_two_clean p h2 k Ω K ζ hζ hζK T hT E σ hσ hnt
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) hz
  · exact himg_involution_input_odd p h2 k Ω K ζ hζ hζK T hT E σ hσ hnt
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) hz

/-- **The `p = 2` branch of `himgExtDeltaInput_inf`, axiom-clean**, from the same node (its `sorry`
is the same statement as `himg_involution_input_two`). -/
theorem himgExtDeltaInput_inf_clean (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (x : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (SSGRoute.PTExt.classesK k K) 1)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1) :
    Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
        ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
            (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm
          (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x))) = 0 := by
  haveI := hRfin
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  refine resH1_zpowers_e1cMap_eq_zero_of_resH2_e1aChainH_eq_zero (k := k) (Ω := Ω) (K := K)
    (N := Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) σ hσ _ ?_
  rw [AddEquiv.apply_symm_apply]
  exact himg_involution_input_two_clean p hp k Ω K ζ hζ hζK T hT E σ hσ hnt
    (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x)
    (Work.SSGRoute.ExtChain.extToIdeles_extDelta_eq_zero (k := k) (K := K) x)

/-- The same leaf as `himg_involution_input_two_clean`, stated against the *sorried* sibling
`ExtChain.hasseExt1_C2_lattice_general` — kept so that the reduction is on record independently of
which copy of the `C₂`-lattice Hasse principle is adopted. -/
theorem himg_involution_input_two_of_hasseExt1 (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (y : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)
      (SSGRoute.PTExt.unitsK k K) 2)
    (hy : SSGRoute.PTExt.extToIdeles (k := k) y = 0) :
    Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) y) = 0 :=
  himg_involution_input_two_of_latticeHasse (k := k) (Ω := Ω) (K := K) (N := _) σ hσ hnt
    (fun M _ _ => hasseExt1_C2_lattice_general p k Ω K σ hσ hnt M) y hy

/-- The same `p = 2` branch of `himgExtDeltaInput_inf`, stated against the sorried sibling. -/
theorem himgExtDeltaInput_inf_of_hasseExt1 (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (x : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (SSGRoute.PTExt.classesK k K) 1)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1) :
    Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
        ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
            (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).symm
          (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x))) = 0 := by
  haveI := hRfin
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  refine resH1_zpowers_e1cMap_eq_zero_of_resH2_e1aChainH_eq_zero (k := k) (Ω := Ω) (K := K)
    (N := Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) σ hσ _ ?_
  rw [AddEquiv.apply_symm_apply]
  exact himg_involution_input_two_of_hasseExt1 p hp k Ω K ζ hζ hζK T hT E σ hσ hnt
    (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) x)
    (Work.SSGRoute.ExtChain.extToIdeles_extDelta_eq_zero (k := k) (K := K) x)

end Work.SSGRoute.ExtChain
