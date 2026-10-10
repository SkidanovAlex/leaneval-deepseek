import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.CokerPT.IotaAlgebra
import Submission.Work.SSGRoute.E1aClean.localDictionary_natural_family
import Submission.Work.SSGRoute.PT.factorised_isCrossedHom
import Submission.Work.SSGRoute.PT.g1plus_level
import Submission.Work.SSGRoute.PT.g1plus_levelInfl
import Submission.Work.SSGRoute.PT.g1plus_levelTransportIota
import Submission.Work.SSGRoute.PT.levelPair_functoriality
import Submission.Work.SSGRoute.PT.place_glue_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
-- TF-FAST (IsTorsionFree local instance)
/-- Build-speed: `IsAlgClosure k Ω` needs `Module.IsTorsionFree k Ω`, which is otherwise
re-synthesized (about 2 s) at every occurrence. File-local, Prop-valued. -/
private theorem tfFast_isTorsionFree {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] :
    Module.IsTorsionFree k Ω :=
  inferInstance

attribute [local instance] tfFast_isTorsionFree
-- TF-FAST-END

/-!
# `G1⁺`: the level data of the finite-place half `fin` (definitions and level relations)

The finite-place half `PT.finAtLevel` of `Work.SSGRoute.PT.canonical_localPairing_reciprocity_converse`
(`G1⁺`) is `χ L hKL (ι_w z)` with `z = levelPair (finZF) (finZI) (βl a) (finZH)` at a level `L ≥ K`.
This module holds **all** the level-dependent data as *opaque `def`s* plus the level relations
between them, so that

* the unfolded body of `finAtLevel` (in `PT/g1plus_finHalf.lean`) contains only constant
  applications — which keeps it well-typed at the `implicit` transparency level used by
  `rw`/`simp` (see `PT/PING_session42_finAtLevel_welltyped.md`), and
* the level transport of the data can be stated and proved as separate lemmas.

The one remaining obligation of the level independence is `PT.finZZ_eq`
(`PT/finZZ_eq.lean`): `finZZ` at the upper level is the local inflation (`extHMap ρ (finMU)`) of
`finZZ` at the lower level.
-/

open scoped TensorProduct Pointwise
open SSGRoute.PTExt CategoryTheory

noncomputable section

namespace Work.SSGRoute.PT

/-- **The two coefficients of the `gammaHom`–`levelPair` interface agree.**  `ExtH1.gammaHom`
produces its class in `modRep ↥H X` for the action composed along `φ : H →* G'`; `levelPair`
consumes a class in `Rep.res f (Rep.res g (modRep G' X))`, where `g` is the subgroup inclusion of
the decomposition group at the place `w` and `f` is the place-glue map.  When `φ = g ∘ f` the two
`Rep`s are the same (the composite action), so an `Ext` class transports across the equality. -/
lemma modRep_compHom_eq_res_res {H G G' : Type} [Group H] [Group G] [Group G']
    (f : H →* G) (g : G →* G') (X : Type) [AddCommGroup X] [DistribMulAction G' X]
    (φ : H →* G') (hφ : φ = g.comp f) :
    @SSGRoute.PTExt.modRep H X _ _ (DistribMulAction.compHom X φ)
      = Rep.res f (Rep.res g (SSGRoute.PTExt.modRep G' X)) := by
  cases hφ
  rfl

/-- **The local units map as an opaque function.**  `localUnitsMap_exists` produces its map as the
`Classical.choose` of an existential whose *statement* mentions `ι.hom (Additive.ofMul u)`, i.e. it
compares the carriers of `Rep.res f (localUnitsK k w)` and `localUnitsK k w'`; those two `Rep`s are
only *definitionally* equal, so that statement is not type-correct at the `implicit` transparency
level that `rw`/`simp` use for matching.  Whenever the `choose`d map appears inside a goal that is
later rewritten, the whole goal becomes un-rewritable (measured; see
`PT/PING_castfree_hval_breaks_clause_matching.md`).  Bundling the choice in this `def` gives it the
clean type `Rep.res f (localUnitsK k w) ⟶ localUnitsK k w'`, so goals containing it stay well-typed
at `implicit` transparency.  Its value is definitionally the chosen map
(`localUnitsMapAt_spec`). -/
noncomputable def localUnitsMapAt (k K L : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* MulAction.stabilizer (K ≃ₐ[k] K) w)
    (hf : ∀ σ, ((f σ : MulAction.stabilizer (K ≃ₐ[k] K) w) : K ≃ₐ[k] K)
      = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L)) :
    Rep.res f (SSGRoute.PTExt.localUnitsK (k := k) w)
      ⟶ NK.HassePrinciple.localUnitsRep k L w' :=
  (Work.SSGRoute.localUnitsMap_exists k K L w w' hw' f hf).choose

/-- **The characterisation of `localUnitsMapAt`**: on `Additive.ofMul u` it is the canonical local
embedding of unit groups (`NK.GlobalCFT.Place.localAlgebraMapUnits`). -/
theorem localUnitsMapAt_spec (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* MulAction.stabilizer (K ≃ₐ[k] K) w)
    (hf : ∀ σ, ((f σ : MulAction.stabilizer (K ≃ₐ[k] K) w) : K ≃ₐ[k] K)
      = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
    (u : (NK.GlobalCFT.Place.localField K w)ˣ) :
    (localUnitsMapAt k K L w w' hw' f hf).hom (Additive.ofMul u)
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u) :=
  (Work.SSGRoute.localUnitsMap_exists k K L w w' hw' f hf).choose_spec u

/-- **The level class `[b]_L` of the finite half as an opaque function with the right `Rep`.**

`ExtH1.gammaHom` produces its class in `extH (modRep ↥(decompK w) X) 1` (the action pulled back
along the place glue `φ₀ = (decompK q).subtype ∘ f`), while `levelPair` consumes a class in
`extH (Rep.res f (Rep.res (decompK q).subtype (modRep Gal X))) 1`; the two `Rep`s are equal only
*definitionally* (`modRep_compHom_eq_res_res`), so the unfolded body of `finAtLevel` is ill-typed at
the `implicit` transparency level used by `rw`/`simp`, and every rewrite into it fails (measured;
`PT/PING_castfree_hval_breaks_clause_matching.md`).  Bundling the class in this `def` — declared at
the `Rep.res`-spelling `levelPair` expects — makes the second factor of `levelPair` well-typed in
any goal containing it. -/
noncomputable def finLevelClass (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (f : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (hf : ∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      ((f σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :
        ↥K ≃ₐ[k] ↥K) = SSGRoute.PTExt.galRes k (↥K) (↥L) (σ : ↥L ≃ₐ[k] ↥L))
    (b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T))
    (hcrossed : ∀ g h : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀ ((g * h : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))) :
            ↥L ≃ₐ[k] ↥L)
        = b₀ (g : ↥L ≃ₐ[k] ↥L)
          + (SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L))
            • b₀ (h : ↥L ≃ₐ[k] ↥L)) :
    extH (Rep.res f
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (modRep (↥K ≃ₐ[k] ↥K) (DualMod p (M ⊗[ZMod p] T))))) 1 := by
  classical
  let X := DualMod p (M ⊗[ZMod p] T)
  -- the `D_w`-action on `X` is the `Gal(K/k)`-action pulled back along `φ₀ = subtype_q ∘ f`
  let φ₀ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      (↥K ≃ₐ[k] ↥K) :=
    (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp f
  -- the `ℤ`- and `Coeff`-commutation on `X` (not Mathlib instances)
  haveI hCommZ : SMulCommClass (↥K ≃ₐ[k] ↥K) ℤ X :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommC : SMulCommClass (↥K ≃ₐ[k] ↥K) Coeff X :=
    ⟨fun g c m => smul_comm g c.down m⟩
  letI hAct : DistribMulAction ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
      X := DistribMulAction.compHom X φ₀
  haveI hCommZp : SMulCommClass ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
      (ZMod p) X := ⟨fun g c m => smul_comm (φ₀ g) c m⟩
  haveI hCommCp : SMulCommClass ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
      Coeff X := ⟨fun g c m => smul_comm (φ₀ g) c m⟩
  have hcr : Work.GroupCohomology.IsCrossedHom
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
      X (fun σ => b₀ (σ : ↥L ≃ₐ[k] ↥L)) := by
    rw [Work.GroupCohomology.IsCrossedHom]
    intro g h
    rw [hcrossed g h]
    show b₀ (g : ↥L ≃ₐ[k] ↥L)
        + (SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • b₀ (h : ↥L ≃ₐ[k] ↥L)
      = (((f g : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :
            ↥K ≃ₐ[k] ↥K)) • b₀ (h : ↥L ≃ₐ[k] ↥L)
        + b₀ (g : ↥L ≃ₐ[k] ↥L)
    rw [hf g]
    abel
  exact modRep_compHom_eq_res_res f
      (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype X φ₀ rfl ▸
    (Work.SSGRoute.ExtH1.gammaHom
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
      X (Work.SSGRoute.augSES_shortExact _)
      (Work.GroupCohomology.H1π _ _ ⟨fun σ => b₀ ((σ :
        ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))) : ↥L ≃ₐ[k] ↥L), by
          rw [Work.GroupCohomology.mem_Z1_iff]; exact hcr⟩))

/-- **The prime of `𝓞 K` under the finite place `A` of `Ω`** (an opaque form of the choice made
inside `PT.finAtLevel`). -/
noncomputable def finQ {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
  (exists_place_under_isFinPlace k Ω K A hA).choose

theorem finQ_spec {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (x : NumberField.RingOfIntegers ↥K) :
    x ∈ (finQ K A hA).asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1 :=
  (exists_place_under_isFinPlace k Ω K A hA).choose_spec.1 x

theorem finQ_glue {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    (SSGRoute.decomp k A).map (SSGRoute.res k K) =
      decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) :=
  (exists_place_under_isFinPlace k Ω K A hA).choose_spec.2

/-- **The prime of `𝓞 L` under the finite place `A` of `Ω`** (an opaque form of the choice made
inside `PT.finAtLevel`). -/
noncomputable def finQW {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L) :=
  (exists_place_under_isFinPlace k Ω L A hA).choose

theorem finQW_spec {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (y : NumberField.RingOfIntegers ↥L) :
    y ∈ (finQW L A hA).asIdeal ↔ A.valuation (((y : ↥L) : Ω)) < 1 :=
  (exists_place_under_isFinPlace k Ω L A hA).choose_spec.1 y

theorem finQW_glue {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    (SSGRoute.decomp k A).map (SSGRoute.res k L) =
      decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) :=
  (exists_place_under_isFinPlace k Ω L A hA).choose_spec.2

/-- **The place glue `D_w →* D_q`** (`PT.place_glue_level`'s restriction map), in opaque form. -/
noncomputable def finZF {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L) [Algebra ↥K ↥L]
    [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L A hA))) →*
      ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))) :=
  ((place_glue_level k Ω K L hKL A hA (finQ K A hA) (fun x => finQ_spec K A hA x)
      (finQW L A hA) (fun y => finQW_spec L A hA y)).2).choose

theorem finZF_spec {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L) [Algebra ↥K ↥L]
    [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQW L A hA)))) :
    ((finZF hKL A hA σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))) :
        ↥K ≃ₐ[k] ↥K)
      = SSGRoute.PTExt.galRes k (↥K) (↥L) (σ : ↥L ≃ₐ[k] ↥L) :=
  ((place_glue_level k Ω K L hKL A hA (finQ K A hA) (fun x => finQ_spec K A hA x)
      (finQW L A hA) (fun y => finQW_spec L A hA y)).2).choose_spec σ

/-- **The localisation of units `K_wˣ → L_{w'}ˣ`** as a morphism of `D_{w'}`-representations. -/
noncomputable def finZI {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L) [Algebra ↥K ↥L]
    [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    Rep.res (finZF hKL A hA)
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))
      ⟶ SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) :=
  localUnitsMapAt k ↥K ↥L (NK.GlobalCFT.Place.ofFinite (finQ K A hA))
    (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
    (place_glue_level k Ω K L hKL A hA (finQ K A hA) (fun x => finQ_spec K A hA x)
      (finQW L A hA) (fun y => finQW_spec L A hA y)).1
    (finZF hKL A hA) (finZF_spec hKL A hA)

/-- **The global dictionary `βg`** of the natural family `E1aClean.localDictionary_natural_family`
(`H¹(k, E) ≅ Ext¹_G(E^∨(1), Kˣ)`); localising it gives `finZB` at every finite place (see the
`square` clause of `finZB_spec`). -/
noncomputable def finZBg (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    ((Ω ≃ₐ[k] Ω) → M) →
      Abelian.Ext (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (DualMod p (M ⊗[ZMod p] T)))
        (SSGRoute.PTExt.unitsK k K) 1 :=
  Classical.choose (Classical.choose_spec
    (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT)) M

/-- **The local dictionary `βl`**, taken from the *natural* family
`E1aClean.localDictionary_natural_family` (rather than from the `Classical.choose` of
`PT.local_ext_h1_bridge`): the natural family carries, besides the three clauses of
`local_ext_h1_bridge` (additivity on cocycles, kernel the coboundaries, surjectivity), the *square*
with the global dictionary, the *unramified* clause and *naturality* in the coefficient module.
Those extra clauses are what `G1⁺`'s clauses (5), (6) and (7) need
(`PT/PING_finZB_noncanonical_and_NAT_perf.md` measured that they are *not* consequences of
`local_ext_h1_bridge`'s three clauses, because `Classical.choose` has no computation rule).

The *type* is unchanged, so all the level data (`finZZ`, `finZH`, the level relations and
`finAtLevel_eq_of_le`) are unaffected. -/
noncomputable def finZB (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ((Ω ≃ₐ[k] Ω) → M) →
      Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (DualMod p (M ⊗[ZMod p] T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA))) 1 :=
  Classical.choose
      (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT)
    M A (finQ K A hA)

/-- The local clause bundle of the natural family, at the modulus `M` and the place `A`:
additivity on cocycles, kernel the coboundaries, surjectivity, the square with the global dictionary,
the unramified clause, and naturality in the coefficient module. -/
theorem finZB_spec (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] {ζ : Ω} {hζ : IsPrimitiveRoot ζ p} {hζK : ζ ∈ K}
    {T : Type} [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    {hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ}
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    (∀ b b' : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
        finZB p K ζ hζ hζK T hT M A hA (b + b')
          = finZB p K ζ hζ hζK T hT M A hA b + finZB p K ζ hζ hζK T hT M A hA b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (finZB p K ζ hζ hζK T hT M A hA b = 0 ↔
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)) ∧
      (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ finZB p K ζ hζ hζK T hT M A hA b = y) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))
          (SSGRoute.PTExt.extToIdeles (k := k) (finZBg p K ζ hζ hζK T hT M b))
          = finZB p K ζ hζ hζK T hT M A hA b) ∧
      (¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
        ∀ b : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → b σ = 0) →
          SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite (finQ K A hA))
            (finZB p K ζ hζ hζK T hT M A hA b)) ∧
      (∀ (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2] [DistribMulAction (K ≃ₐ[k] K) E2]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
        (f : M →ₗ[ZMod p] E2) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
        (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (DualMod p (E2 ⊗[ZMod p] T)) ⟶
          SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (DualMod p (M ⊗[ZMod p] T)))
        (hF' : ∀ (φ : DualMod p (E2 ⊗[ZMod p] T)) (e : M) (t : T),
          (show DualMod p (M ⊗[ZMod p] T) from F'.hom φ) (TensorProduct.tmul (ZMod p) e t)
            = φ (TensorProduct.tmul (ZMod p) (f e) t))
        (b : (Ω ≃ₐ[k] Ω) → M),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        finZB p K ζ hζ hζK T hT E2 A hA (fun σ => f (b σ)) =
          (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k)
              (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype F')).comp
            (finZB p K ζ hζ hζK T hT M A hA b) (zero_add 1)) :=
  ((Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Work.SSGRoute.E1aClean.localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT)))) M).2.2.2.2 A
    (finQ K A hA) hA (fun x => finQ_spec K A hA x)

/-- Additivity of the local dictionary on locally constant cocycles. -/
theorem finZB_add (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b b' : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b')
    (hl' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b') :
    finZB p K ζ hζ hζK T hT M A hA (b + b')
      = finZB p K ζ hζ hζK T hT M A hA b + finZB p K ζ hζ hζK T hT M A hA b' :=
  (finZB_spec p M A hA).1 b b' hb hl hb' hl'

/-- The kernel of the local dictionary is the coboundaries. -/
theorem finZB_eq_zero_iff (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) :
    finZB p K ζ hζ hζK T hT M A hA b = 0 ↔
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b :=
  (finZB_spec p M A hA).2.1 b hb hl

/-- Surjectivity of the local dictionary onto `Ext¹`. -/
theorem finZB_surjective (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (y : Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (DualMod p (M ⊗[ZMod p] T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA))) 1) :
    ∃ b : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ finZB p K ζ hζ hζK T hT M A hA b = y :=
  (finZB_spec p M A hA).2.2.1 y

/-- The *unramified* clause: a locally constant cocycle vanishing on the inertia at a good place has
unramified dictionary class. -/
theorem finZB_unramified (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hpA : ¬ A.valuation (p : Ω) < 1) (hramA : ¬ SSGRoute.IsRamifiedIn k K A)
    (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → b σ = 0) :
    SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite (finQ K A hA))
      (finZB p K ζ hζ hζK T hT M A hA b) :=
  (finZB_spec p M A hA).2.2.2.2.1 hpA hramA b hb hl hiner

/-- Naturality of the local dictionary in the coefficient module. -/
theorem finZB_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2] [DistribMulAction (K ≃ₐ[k] K) E2]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
    (f : M →ₗ[ZMod p] E2) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (DualMod p (E2 ⊗[ZMod p] T)) ⟶
      SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (DualMod p (M ⊗[ZMod p] T)))
    (hF' : ∀ (φ : DualMod p (E2 ⊗[ZMod p] T)) (e : M) (t : T),
      (show DualMod p (M ⊗[ZMod p] T) from F'.hom φ) (TensorProduct.tmul (ZMod p) e t)
        = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) :
    finZB p K ζ hζ hζK T hT E2 A hA (fun σ => f (b σ)) =
      (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype F')).comp
        (finZB p K ζ hζ hζK T hT M A hA b) (zero_add 1) :=
  (finZB_spec p M A hA).2.2.2.2.2 E2 f hf F' hF' b hb hl

/-- **The level class `[b]_L`** (`PT.finLevelClass` instantiated at the opaque level data). -/
noncomputable def finZH (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    extH (Rep.res (finZF hKL A hA)
      (Rep.res (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (DualMod p (M ⊗[ZMod p] T))))) 1 :=
  finLevelClass p k Ω K T M L (finQ K A hA) (finQW L A hA) (finZF hKL A hA)
    (finZF_spec hKL A hA) b₀
    (factorised_isCrossedHom p k Ω K L hKL A hA (finQ K A hA) (fun x => finQ_spec K A hA x)
      (finQW L A hA) (fun y => finQW_spec L A hA y) (finQW_glue L A hA)
      (DualMod p (M ⊗[ZMod p] T)) b hb b₀ hb₀)

/-- **The local class `levelPair f ι (βl a) [b]_L ∈ H²(D_w, L_wˣ)`** in opaque form. -/
noncomputable def finZZ (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    extH (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite (finQW L A hA))) 2 :=
  levelPair (finZF hKL A hA) (finZI hKL A hA)
    ((finZB p K ζ hζ hζK T hT M A hA) a) (finZH p K T M L hKL A hA b hb b₀ hb₀)

section DataProps

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K L L' : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField L] [FiniteDimensional k L] [IsGalois k L]
  [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
  (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)

/-- **The primes of `𝓞 L` and `𝓞 L'` cut out by the same place `A` of `Ω` lie over each other.** -/
theorem finQW_liesOver (hLL : L ≤ L') [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L']
    [IsScalarTower ↥L ↥L' Ω] :
    (finQW L' A hA).asIdeal.LiesOver (finQW L A hA).asIdeal := by
  simp only [finQW]
  refine asIdeal_liesOver_of_valuation_lt_one L L' A _ ?_ _ ?_
  · exact (exists_place_under_isFinPlace k Ω L A hA).choose_spec.1
  · exact (exists_place_under_isFinPlace k Ω L' A hA).choose_spec.1

end DataProps

section DataProps2

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K L L' : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField L] [FiniteDimensional k L] [IsGalois k L]
  [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
  (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
  [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
  [Algebra ↥K ↥L'] [IsScalarTower k ↥K ↥L'] [IsScalarTower ↥K ↥L' Ω]
  [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω]
  [IsScalarTower ↥K ↥L ↥L']

/-- **The place-glue maps at two levels are related by the restriction of decomposition groups.** -/
theorem finZF_eq (hKL : K ≤ L) (hKL' : K ≤ L') (hLL : L ≤ L') :
    finZF hKL' A hA = (finZF hKL A hA).comp
      (decompKRestrict k (↥L) (↥L')
        (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
        (NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL))) := by
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  rw [finZF_spec hKL' A hA σ, MonoidHom.comp_apply,
    finZF_spec hKL A hA
      (decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
        (NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL)) σ),
    decompKRestrict_coe, galRes_trans]

/-- **The intermediate local-units map** `L_{w'}ˣ → L'_{w''}ˣ` of the level change
`L ≤ L'` (the `μ` of `PT.chi_iota_eq_of_localInflation`). -/
noncomputable def finMU
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K L L' : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hLL : L ≤ L')
    [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω] :
    Rep.res (decompKRestrict k (↥L) (↥L')
        (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
        (NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL)))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite (finQW L A hA)))
    ⟶ SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L')
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) :=
  localUnitsMapAt k ↥L ↥L' (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
    (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
    (NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL))
    (decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
      (NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL)))
    (decompKRestrict_coe k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
      (NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL)))

/-- The value of `finMU` on `Additive.ofMul u`. -/
theorem finMU_spec
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K L L' : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hLL : L ≤ L')
    [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω]
    (u : (NK.GlobalCFT.Place.localField ↥L
        (NK.GlobalCFT.Place.ofFinite (finQW L A hA)))ˣ) :
    (finMU (K := K) A hA hLL).hom (Additive.ofMul u)
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
          (NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL)) u) :=
  localUnitsMapAt_spec k ↥L ↥L' (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
    (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
    (NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL))
    (decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
      (NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL)))
    (decompKRestrict_coe k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
      (NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL))) u

/-- `p` times a vector of a `ZMod p`-module is zero. -/
theorem nsmul_eq_zero_of_zmod' (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] (x : V) :
    p • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self, zero_smul]

end DataProps2


/-- **The level pairing is `nsmul`-compatible in its `Ext` variable** (a local copy of
`PT.levelPair_nsmul_fst`, which lives in a module that imports this one). -/
theorem pt_levelPair_nsmul_fst {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ}
    (n : ℕ) (x : Abelian.Ext.{0} M A r) (h : extH (Rep.res f M) s) :
    n • levelPair f ι x h = levelPair f ι (n • x) h :=
  (AddMonoidHom.map_nsmul
    { toFun := fun x => levelPair f ι x h
      map_zero' := Work.SSGRoute.levelPair_zero f ι h
      map_add' := fun x x' => Work.SSGRoute.levelPair_add f ι x x' h } n x).symm

section FinZZEq

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K L L' : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField L] [FiniteDimensional k L] [IsGalois k L]
  [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
  (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
  [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
  [Algebra ↥K ↥L'] [IsScalarTower k ↥K ↥L'] [IsScalarTower ↥K ↥L' Ω]
  [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω]
  [IsScalarTower ↥K ↥L ↥L']
  (p : ℕ) [Fact p.Prime] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
  (hKL : K ≤ L) (hKL' : K ≤ L') (hLL : L ≤ L')
  (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
  (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
  (b₀ : (↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T))
  (b₀' : (↥L' ≃ₐ[k] ↥L') → DualMod p (M ⊗[ZMod p] T))
  (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
  (hb₀' : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀' (AlgEquiv.restrictNormalHom L' σ))

/-- **Pointwise relation of the local units maps at two levels**: on
`Additive.ofMul u`, `finZI` at the upper level equals `finMU` composed with `finZI` at the lower
level.  This is the transitivity of the canonical local embeddings
(`NK.GlobalCFT.Place.localAlgebraMapUnits_comp` of `SSGRoute/phi1_level_naturality.lean`),
transported through the two `localUnitsMapAt_spec` characterisations. -/
theorem finZI_apply (hKL : K ≤ L) (hKL' : K ≤ L') (hLL : L ≤ L')
    (u : (NK.GlobalCFT.Place.localField ↥K
        (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))ˣ) :
    (finZI hKL' A hA).hom (Additive.ofMul u)
      = (finMU (K := K) A hA hLL).hom ((finZI hKL A hA).hom (Additive.ofMul u)) := by
  have hLies : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) :=
    (place_glue_level k Ω K L hKL A hA (finQ K A hA) (fun x => finQ_spec K A hA x)
      (finQW L A hA) (fun y => finQW_spec L A hA y)).1
  have hLies' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
      (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) :=
    (place_glue_level k Ω K L' hKL' A hA (finQ K A hA) (fun x => finQ_spec K A hA x)
      (finQW L' A hA) (fun y => finQW_spec L' A hA y)).1
  have hw' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) :=
    NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL)
  have h1 : (finZI hKL A hA).hom (Additive.ofMul u)
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) hLies u) := by
    simp only [finZI]
    exact localUnitsMapAt_spec k ↥K ↥L (NK.GlobalCFT.Place.ofFinite (finQ K A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) hLies (finZF hKL A hA)
      (finZF_spec hKL A hA) u
  have h3 : (finZI hKL' A hA).hom (Additive.ofMul u)
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) hLies' u) := by
    simp only [finZI]
    exact localUnitsMapAt_spec k ↥K ↥L' (NK.GlobalCFT.Place.ofFinite (finQ K A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hLies' (finZF hKL' A hA)
      (finZF_spec hKL' A hA) u
  have h2 : (finMU (K := K) A hA hLL).hom
        (Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) hLies u))
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) hw'
          (NK.GlobalCFT.Place.localAlgebraMapUnits
            (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
            (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) hLies u)) := by
    simp only [finMU]
    exact localUnitsMapAt_spec k ↥L ↥L' (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw'
      (decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw')
      (decompKRestrict_coe k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw')
      (NK.GlobalCFT.Place.localAlgebraMapUnits
        (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) hLies u)
  have h2' : (finMU (K := K) A hA hLL).hom ((finZI hKL A hA).hom (Additive.ofMul u))
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) hw'
          (NK.GlobalCFT.Place.localAlgebraMapUnits
            (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
            (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) hLies u)) :=
    (congrArg (fun z => (finMU (K := K) A hA hLL).hom z) h1).trans h2
  have hkey : Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
          (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) hw'
          (NK.GlobalCFT.Place.localAlgebraMapUnits
            (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
            (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) hLies u))
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits
          (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) hLies' u) :=
    congrArg Additive.ofMul (DFunLike.congr_fun (localAlgebraMapUnits_comp hw' hLies hLies') u)
  exact h3.trans (hkey.symm.trans h2'.symm)

end FinZZEq

