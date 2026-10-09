import Mathlib
import Submission.Work.SSGRoute.E7Fin.RedLattice.InvDimFunctional
import Submission.Work.SSGRoute.E7Fin.RedLattice.invDimFunctional_isAddInv
import Submission.Work.SSGRoute.E7Fin.RedLattice.invDimFunctional_regMod
import Submission.Work.SSGRoute.E7Fin.RedLattice.Regular
import Submission.Work.SSGRoute.E7Fin.diagTensorInvariantsEngine
import Submission.Work.SSGRoute.EulerSymm.localArith.LocalKummerMod
import Submission.Work.SSGRoute.EulerSymm.hsSetup
import Submission.Work.SSGRoute.exists_mem_closure_decomp_mul_mem_fixingSubgroup
import Submission.Work.SSGRoute.mup_local_defs
import Submission.Work.SSGRoute.EulerSymm.levelKummerAction
import Submission.Work.SSGRoute.PTCore.invariantsSubmodule
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.LTDRefs.TrivialEulerEps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The vocabulary of the two pieces of obligation (C) (Milne *ADT* I.2.11)

`D = DC k Ω K A Γ` is the decomposition group `decomp k A ⊓ res⁻¹ Γ` of the finite place `A` of `Ω`,
`U = UD k Ω K A = D ∩ Gal(Ω/K)` its kernel of restriction (the *level* group), `Dsub = res(D) = Γ''`
its image in `Gal(K/k)`, and `E = mupLevelField k Ω K A = K ⊔ Ω^{D_A}` the **level field** of the
`μ_p`-Kummer theory at `A`; its `p`-Kummer group `Eˣ⧸(Eˣ)ᵖ` carries the `𝔽_p[↥D]`-structure of
`EulerSymm/levelKummerAction.lean` (`mupLevelKummerFrob`).  Writing `κ = K_𝔮` for the completion of
`K` at the place below `A` (`levelKappa`, `𝔮 = Submission.NeukirchUchida.primeOf A hAK`), this file
supplies

* the local Kummer group `localKummer p k Ω K A hAK = Additive (κˣ ⧸ (κˣ)ᵖ)`, with its canonical
  `𝔽_p`-module structure, its `↥Dsub`-action `localKummerDsubAction` (the local Galois action
  through `Dsub ≤ levelStab`) and its `↥D`-action `localKummerDCAction` (through `res`, hence
  factoring through `Dsub` — `localKummerDCAction_smul` is `rfl`, which is what makes the descent
  `D ↠ Dsub` transparent), together with the `SMulCommClass` instances;
* the `↥Dsub`-structure on the cyclotomic dual `DualMod p T` (`dualModDsubAction`);
* the two Prop-valued predicates in which obligation (C) is stated here:
  * **`IsLevelTransport`** — (C-transport): `Eˣ⧸(Eˣ)ᵖ ≅ κˣ⧸(κˣ)ᵖ` as `𝔽_p[↥D]`-modules;
  * **`IsLocalKummerStructure`** — (C-local): the `ρ`-form of the local structure
    `[κˣ⧸(κˣ)ᵖ] = [𝔽_p] + [DualMod p T] + c·[𝔽_p[Dsub]]` for every additive invariant `ρ` of
    finite `𝔽_p[↥Dsub]`-modules.

The companion file `EulerSymm/kummerGroupUDStructureFresh.lean` proves the gluing of these two
pieces into obligation (C) (`kummerGroupUDStructure`), so a proof of (C) independent of the `sorry`
in `EulerSymm/kummerGroupUDStructure.lean` only has to supply the two predicates.
-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute.EulerSymm

noncomputable section

/-- The prime of the level field `↥K` below the place `A`. -/
abbrev levelPrime (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (A : ValuationSubring Ω) (hAK : SSGRoute.IsFinPlace ↥K A) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
  Submission.NeukirchUchida.primeOf A hAK

/-- The decomposition group of `A` inside `Gal(K/k)` (the local Galois group of the completion). -/
abbrev levelStab (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (A : ValuationSubring Ω) (hAK : SSGRoute.IsFinPlace ↥K A) : Subgroup (K ≃ₐ[k] K) :=
  MulAction.stabilizer (K ≃ₐ[k] K) (NK.GlobalCFT.Place.ofFinite (levelPrime k Ω K A hAK))

/-- The level completion `κ = K_𝔮`. -/
abbrev levelKappa (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (A : ValuationSubring Ω) (hAK : SSGRoute.IsFinPlace ↥K A) : Type :=
  (levelPrime k Ω K A hAK).adicCompletion ↥K

/-- The local `p`-Kummer group `κˣ ⧸ (κˣ)ᵖ` of the level completion, written additively. -/
abbrev localKummer (p : ℕ) (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (A : ValuationSubring Ω) (hAK : SSGRoute.IsFinPlace ↥K A) : Type :=
  Additive ((levelKappa k Ω K A hAK)ˣ ⧸ (powMonoidHom p).range)

/-- `Dsub k Ω K A Γ = res(D_C)` sits inside the local Galois group `levelStab k Ω K A hAK`. -/
lemma Dsub_le_levelStab (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hAK : SSGRoute.IsFinPlace ↥K A) (Γ : Subgroup (K ≃ₐ[k] K))
    (hAq : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K (levelPrime k Ω K A hAK)) :
    Dsub k Ω K A Γ ≤ levelStab k Ω K A hAK :=
  (Subgroup.map_mono (inf_le_left)).trans
    (Work.SSGRoute.decomp_map_le_stabilizer_of_comap_eq k Ω K (levelPrime k Ω K A hAK) A hA hAq)

/-- The `𝔽_p`-module structure on the local Kummer group. -/
instance localKummerModule (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] (A : ValuationSubring Ω) (hAK : SSGRoute.IsFinPlace ↥K A) :
    Module (ZMod p) (localKummer p k Ω K A hAK) :=
  powQuotModule p (A := (levelKappa k Ω K A hAK)ˣ)

/-- The `levelStab`-action on the local Kummer group. -/
instance localKummerGpAction (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] (A : ValuationSubring Ω) (hAK : SSGRoute.IsFinPlace ↥K A) :
    DistribMulAction (levelStab k Ω K A hAK) (localKummer p k Ω K A hAK) :=
  powQuotDistribMulAction (G := levelStab k Ω K A hAK) (A := (levelKappa k Ω K A hAK)ˣ) p

/-- The `𝔽_p`-scalars and the `levelStab`-action on the local Kummer group commute. -/
instance localKummerSMulCommClass (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] (A : ValuationSubring Ω) (hAK : SSGRoute.IsFinPlace ↥K A) :
    SMulCommClass (levelStab k Ω K A hAK) (ZMod p) (localKummer p k Ω K A hAK) :=
  powQuotSMulCommClass (A := (levelKappa k Ω K A hAK)ˣ) p

/-- The `Dsub`-action on the local Kummer group (through the inclusion into the local Galois
group). -/
noncomputable def localKummerDsubAction (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] (A : ValuationSubring Ω)
    (hAK : SSGRoute.IsFinPlace ↥K A) (Γ : Subgroup (K ≃ₐ[k] K))
    (hle : Dsub k Ω K A Γ ≤ levelStab k Ω K A hAK) :
    DistribMulAction ↥(Dsub k Ω K A Γ) (localKummer p k Ω K A hAK) :=
  DistribMulAction.compHom (localKummer p k Ω K A hAK) (Subgroup.inclusion hle)

/-- The `𝔽_p`-scalars and the `Dsub`-action on the local Kummer group commute. -/
noncomputable def localKummerDsubSMulCommClass (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] (A : ValuationSubring Ω)
    (hAK : SSGRoute.IsFinPlace ↥K A) (Γ : Subgroup (K ≃ₐ[k] K))
    (hle : Dsub k Ω K A Γ ≤ levelStab k Ω K A hAK) :
    @SMulCommClass ↥(Dsub k Ω K A Γ) (ZMod p) (localKummer p k Ω K A hAK)
      (localKummerDsubAction p k Ω K A hAK Γ hle).toSMul
      (localKummerModule p k Ω K A hAK).toSMul := by
  letI := localKummerDsubAction p k Ω K A hAK Γ hle
  refine ⟨fun d c x => ?_⟩
  change (Subgroup.inclusion hle d) • (c • x) = c • ((Subgroup.inclusion hle d) • x)
  exact SMulCommClass.smul_comm (Subgroup.inclusion hle d) c x

/-- The canonical homomorphism `D_C →* Dsub k Ω K A Γ` (the restriction `res`). -/
noncomputable def dcToDsub (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [IsGalois k K] (A : ValuationSubring Ω)
    (Γ : Subgroup (K ≃ₐ[k] K)) : ↥(DC k Ω K A Γ) →* ↥(Dsub k Ω K A Γ) where
  toFun δ := ⟨SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω), Subgroup.mem_map.mpr ⟨(δ : Ω ≃ₐ[k] Ω), δ.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

@[simp] lemma dcToDsub_coe (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [IsGalois k K] (A : ValuationSubring Ω)
    (Γ : Subgroup (K ≃ₐ[k] K)) (δ : ↥(DC k Ω K A Γ)) :
    ((dcToDsub k Ω K A Γ δ : ↥(Dsub k Ω K A Γ)) : K ≃ₐ[k] K)
      = SSGRoute.res k K (δ : Ω ≃ₐ[k] Ω) := rfl

/-- The `↥(DC k Ω K A Γ)`-action on the local Kummer group, through `res`. -/
noncomputable def localKummerDCAction (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] (A : ValuationSubring Ω) (hAK : SSGRoute.IsFinPlace ↥K A)
    (Γ : Subgroup (K ≃ₐ[k] K)) (hle : Dsub k Ω K A Γ ≤ levelStab k Ω K A hAK) :
    DistribMulAction ↥(DC k Ω K A Γ) (localKummer p k Ω K A hAK) :=
  DistribMulAction.compHom (localKummer p k Ω K A hAK)
    ((Subgroup.inclusion hle).comp (dcToDsub k Ω K A Γ))

/-- **The `D_C`-action on the local Kummer group factors through `Dsub`**: acting by `δ : D_C` is
acting by its restriction `res δ`. -/
lemma localKummerDCAction_smul (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] (A : ValuationSubring Ω) (hAK : SSGRoute.IsFinPlace ↥K A)
    (Γ : Subgroup (K ≃ₐ[k] K)) (hle : Dsub k Ω K A Γ ≤ levelStab k Ω K A hAK)
    (δ : ↥(DC k Ω K A Γ)) (x : localKummer p k Ω K A hAK) :
    @SMul.smul _ _ (localKummerDCAction p k Ω K A hAK Γ hle).toSMul δ x
      = @SMul.smul _ _ (localKummerDsubAction p k Ω K A hAK Γ hle).toSMul
          (dcToDsub k Ω K A Γ δ) x := rfl

/-- The `𝔽_p`-scalars and the `D_C`-action on the local Kummer group commute. -/
noncomputable def localKummerDCSMulCommClass (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] (A : ValuationSubring Ω)
    (hAK : SSGRoute.IsFinPlace ↥K A) (Γ : Subgroup (K ≃ₐ[k] K))
    (hle : Dsub k Ω K A Γ ≤ levelStab k Ω K A hAK) :
    @SMulCommClass ↥(DC k Ω K A Γ) (ZMod p) (localKummer p k Ω K A hAK)
      (localKummerDCAction p k Ω K A hAK Γ hle).toSMul
      (localKummerModule p k Ω K A hAK).toSMul := by
  letI := localKummerDsubAction p k Ω K A hAK Γ hle
  letI := localKummerDCAction p k Ω K A hAK Γ hle
  letI := localKummerDsubSMulCommClass p k Ω K A hAK Γ hle
  refine ⟨fun δ c x => ?_⟩
  show (dcToDsub k Ω K A Γ δ) • (c • x) = c • ((dcToDsub k Ω K A Γ δ) • x)
  exact SMulCommClass.smul_comm (dcToDsub k Ω K A Γ δ) c x

/-- The canonical inclusion `Dsub k Ω K A Γ ≤ levelStab k Ω K A hAK`. -/
noncomputable def hleStab (k : Type) [Field k] [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [IsSepClosure ↥K Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (hAK : SSGRoute.IsFinPlace ↥K A)
    (Γ : Subgroup (K ≃ₐ[k] K)) : Dsub k Ω K A Γ ≤ levelStab k Ω K A hAK :=
  Dsub_le_levelStab k Ω K A hA hAK Γ (Submission.NeukirchUchida.primeOf_spec A hAK)

/-- The `Dsub`-structure on `DualMod p T` (through the restriction of the `Gal(K/k)`-action). -/
noncomputable def dualModDsubAction (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (A : ValuationSubring Ω)
    (Γ : Subgroup (K ≃ₐ[k] K)) (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] :
    DistribMulAction ↥(Dsub k Ω K A Γ) (Work.SSGRoute.DualMod p T) :=
  letI : DistribMulAction ↥(Dsub k Ω K A Γ) T :=
    DistribMulAction.compHom T (Dsub k Ω K A Γ).subtype
  DistribMulAction.compHom (Work.SSGRoute.DualMod p T) (Dsub k Ω K A Γ).subtype

/-- The `𝔽_p`-scalars and the `Dsub`-action on `DualMod p T` commute. -/
noncomputable def dualModDsubSMulCommClass (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [NumberField k] (Ω : Type) [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (A : ValuationSubring Ω) (Γ : Subgroup (K ≃ₐ[k] K))
    (T : Type) [AddCommGroup T]
    [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] :
    @SMulCommClass ↥(Dsub k Ω K A Γ) (ZMod p) (Work.SSGRoute.DualMod p T)
      (dualModDsubAction p k Ω K A Γ T).toSMul (inferInstance : Module (ZMod p) (Work.SSGRoute.DualMod p T)).toSMul := by
  letI : DistribMulAction ↥(Dsub k Ω K A Γ) T :=
    DistribMulAction.compHom T (Dsub k Ω K A Γ).subtype
  haveI : SMulCommClass ↥(Dsub k Ω K A Γ) (ZMod p) T :=
    ⟨fun d c t => by
      show (d : K ≃ₐ[k] K) • (c • t) = c • ((d : K ≃ₐ[k] K) • t)
      exact SMulCommClass.smul_comm (d : K ≃ₐ[k] K) c t⟩
  letI hd : DistribMulAction ↥(Dsub k Ω K A Γ) (Work.SSGRoute.DualMod p T) :=
    dualModDsubAction p k Ω K A Γ T
  refine ⟨fun d c f => ?_⟩
  change (d : K ≃ₐ[k] K) • (c • f) = c • ((d : K ≃ₐ[k] K) • f)
  exact SMulCommClass.smul_comm (d : K ≃ₐ[k] K) c f

/-- Finiteness of `DualMod p T` for finite `T`. -/
noncomputable def dualModFinite (p : ℕ) [NeZero p] {T : Type} [AddCommGroup T]
    [Module (ZMod p) T] [Finite T] : Finite (Work.SSGRoute.DualMod p T) :=
  Finite.of_injective (fun f : Work.SSGRoute.DualMod p T => (f : T → ZMod p))
    DFunLike.coe_injective

/-- **(C-local)** — the local arithmetic chapter of Milne *ADT* I.2.11 at the level completion
`κ = K_𝔮`, in the form in which the target consumes it: for every additive invariant `ρ` of finite
`𝔽_p[↥(Dsub k Ω K A Γ)]`-modules, the local Kummer group `κˣ ⧸ (κˣ)ᵖ` decomposes as
`[𝔽_p] + [DualMod p T] + c·[Reg]`.

This is the conjunction of the three pieces `localArith/valRho_eq_puRho_add_triv` (VAL),
`LocalArith/puRho_eq_lamRho_add_mup` (LOG) and `LocalArith/lamRho_eq_regular` (LATTICE), applied at
the base field `K^{Dsub k Ω K A Γ}` (so that `Dsub k Ω K A Γ` *is* the full local Galois group), with
the standard folds: the coefficient identification `μ_p(κ) ≅ DualMod p T`, and the constant
identity `d = c` between the LATTICE constant `d·|Dsub| = localDegree K 𝔮` and the target's
`c = ε·Γ.relIndex (res '' decomp k A)`. -/
def IsLocalKummerStructure (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k]
    (Ω : Type) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hAK : SSGRoute.IsFinPlace ↥K A)
    (Γ : Subgroup (K ≃ₐ[k] K)) (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    [Fintype ↥(Dsub k Ω K A Γ)] [Finite (localKummer p k Ω K A hAK)] [Finite T]
    (c : ℕ) : Prop :=
  ∀ (ρ : Work.ArtinInduction.LatticeModp.Inv p ↥(Dsub k Ω K A Γ)),
    Work.ArtinInduction.LatticeModp.IsAddInv ρ →
    @ρ (localKummer p k Ω K A hAK) (inferInstance) (localKummerModule p k Ω K A hAK)
        (localKummerDsubAction p k Ω K A hAK Γ (hleStab k Ω K A hA hAK Γ))
        (localKummerDsubSMulCommClass p k Ω K A hAK Γ (hleStab k Ω K A hA hAK Γ))
        (inferInstance)
      = ρ (Work.SSGRoute.mup.TrivMod p ↥(Dsub k Ω K A Γ))
        + @ρ (Work.SSGRoute.DualMod p T) (inferInstance) (inferInstance)
            (dualModDsubAction p k Ω K A Γ T)
            (dualModDsubSMulCommClass p k Ω K A Γ T) (dualModFinite p)
        + c * @ρ (Work.SSGRoute.E7Fin.RedLattice.RegMod p ↥(Dsub k Ω K A Γ))
            (inferInstance) (inferInstance)
            (Work.SSGRoute.E7Fin.RedLattice.instDistribMulActionRegMod p ↥(Dsub k Ω K A Γ))
            (Work.SSGRoute.E7Fin.RedLattice.instSMulCommClassRegMod p ↥(Dsub k Ω K A Γ))
            (inferInstance)

/-- **(C-transport)** — the level-field bookkeeping: the level Kummer group `Eˣ ⧸ (Eˣ)ᵖ`
(`E = mupLevelField k Ω K A`) and the local Kummer group `κˣ ⧸ (κˣ)ᵖ` of the completion are
isomorphic as `𝔽_p[↥(DC k Ω K A Γ)]`-modules, the action on the latter being the local action
through `res`. -/
def IsLevelTransport (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k] (Ω : Type)
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K] [IsSepClosure ↥K Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (hAK : SSGRoute.IsFinPlace ↥K A)
    (Γ : Subgroup (K ≃ₐ[k] K)) : Prop :=
  ∃ e : Additive (Work.SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A)) ≃ₗ[ZMod p]
      (localKummer p k Ω K A hAK),
    ∀ (δ : ↥(DC k Ω K A Γ))
      (x : Additive (Work.SSGRoute.mup.KummerGroup p ↥(mupLevelField k Ω K A))),
      e (Work.SSGRoute.EulerSymm.mupLevelKummerFrob p k Ω K A Γ δ x)
        = @SMul.smul _ _ (localKummerDCAction p k Ω K A hAK Γ (hleStab k Ω K A hA hAK Γ)).toSMul
            δ (e x)

end

end Work.SSGRoute.EulerSymm
