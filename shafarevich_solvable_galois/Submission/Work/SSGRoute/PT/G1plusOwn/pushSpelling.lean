import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.vfShared
import Submission.Work.SSGRoute.PT.vf_transverse
import Submission.Work.SSGRoute.local_phi_realization_in
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Rep`-spelling bricks of the level-pairing push (`finZZ = extLoc w Y`)

`PT.finZZ` is spelled with the *opaque* level data `PT.finZF` (the `Classical.choose` of
`PT.place_glue_level`), `PT.finZI` (`PT.localUnitsMapAt` at that glue) and `PT.finZH` (the restricted
level class), while the localisation `extLoc w (levelPair (galRes) (idleRepMap) X h)` of a *global*
class is spelled with the transparent place glue `Work.SSGRoute.decompKRestrict` and the canonical
local-units map `Work.SSGRoute.localUnitsMap`.  The two spellings differ by transportation along the
single equality `finZF = finDKRg` (`PT.finZF_spec`/`decompKRestrict_coe`), dealt with by `eqToHom` of
the corresponding `Rep.res`.

The two bricks recorded here are

* `finZI_eq_localUnitsMap` — `PT.finZI` is `Work.SSGRoute.localUnitsMap`, transported.  Both are
  `Classical.choose`s satisfying the same computation rule on `Additive.ofMul`
  (`PT.localUnitsMapAt_spec`, `Work.SSGRoute.localUnitsMap_spec`);
* `finZH_eq_extHRestrict` — `PT.finZH` is the restriction of the *global* level class
  `PT.levelClassOf` to the decomposition group (group-naturality of `ExtH1.gammaHom`).

(The file is self-contained: the place-glue data are defined here rather than imported from the
sibling lane, whose module does not elaborate in the current memory slot.)
-/

namespace Work.SSGRoute.PT.G1plusOwn

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

/-- The place-glue proof used in the definitions of `PT.finZF` and `PT.finZI`. -/
noncomputable def finHWg {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField L] [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L) [Algebra ↥K ↥L]
    [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    NK.GlobalCFT.Place.LiesOver
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) :=
  (Work.SSGRoute.PT.place_glue_level k Ω K L hKL A hA (Work.SSGRoute.PT.finQ K A hA)
    (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA)
    (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)).1

/-- The canonical place glue `D_{w'} → D_q` of the finite place `A`. -/
noncomputable def finDKRg {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField L] [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L) [Algebra ↥K ↥L]
    [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))) →*
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) :=
  Work.SSGRoute.decompKRestrict k ↥K ↥L
    (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
    (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (finHWg hKL A hA)

/-- **`PT.finZF` is the canonical place glue** `decompKRestrict` at the place-glue proof `finHWg`. -/
theorem finZF_eq_dkrg {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField L] [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L) [Algebra ↥K ↥L]
    [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.PT.finZF hKL A hA = finDKRg hKL A hA := by
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  rw [Work.SSGRoute.PT.finZF_spec hKL A hA σ]
  exact (Work.SSGRoute.decompKRestrict_coe k ↥K ↥L _ _ (finHWg hKL A hA) σ).symm

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k L] [IsGalois k L] (hKL : K ≤ L) [Algebra ↥K ↥L]
  [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω] (A : ValuationSubring Ω)
  (hA : SSGRoute.IsFinPlace k A)

/-- v4.35 port helper: a morphism out of `Rep.res f₁ X` equals `eqToHom h ≫ g` as soon as they agree
pointwise (proved once generically, so the kernel never unfolds the concrete `Rep.res` objects). -/
theorem eq_eqToHom_comp1_of_apply {G H : Type} [Group G] [Group H] (f₁ f₂ : H →* G)
    (X : Rep.{0} SSGRoute.PTExt.Coeff G) (h : Rep.res f₁ X = Rep.res f₂ X)
    {W : Rep.{0} SSGRoute.PTExt.Coeff H} (g : Rep.res f₂ X ⟶ W) (φ : Rep.res f₁ X ⟶ W)
    (hφ : ∀ x : X.V, (Rep.Hom.hom φ) x = (Rep.Hom.hom g) x) :
    φ = CategoryTheory.CategoryStruct.comp (CategoryTheory.eqToHom h) g := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  change (Rep.Hom.hom φ) x = (Rep.Hom.hom g) ((Rep.Hom.hom (CategoryTheory.eqToHom h)) x)
  rw [Work.SSGRoute.PT.eqToHom_res_hom_self]
  exact hφ x

/-- **`PT.finZI` is the canonical local-units map `Work.SSGRoute.localUnitsMap`**, transported along
the `Rep.res`-spelling equality `finZF = finDKRg`.  Both maps send `Additive.ofMul u` to
`Additive.ofMul (localAlgebraMapUnits w' q hw u)` (`PT.localUnitsMapAt_spec`,
`Work.SSGRoute.localUnitsMap_spec`); `PT.finZI` passes the opaque place-glue proof `finHWg`, which
is propositionally equal to the one used by `localUnitsMap`. -/
theorem finZI_eq_localUnitsMap
    (hZF : Work.SSGRoute.PT.finZF hKL A hA = finDKRg hKL A hA) :
    Work.SSGRoute.PT.finZI hKL A hA
      = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.eqToHom (congrArg (fun t => Rep.res t
            (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
              (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)))) hZF))
          (Work.SSGRoute.localUnitsMap k (↥K) (↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (Work.SSGRoute.PT.G1plusOwn.finHWg hKL A hA)) := by
  classical
  refine eq_eqToHom_comp1_of_apply _ _ _ _ _ _ (fun x => ?_)
  rw [show x = Additive.ofMul (Additive.toMul x) from rfl]
  rw [Work.SSGRoute.PT.finZI]
  rw [Work.SSGRoute.PT.localUnitsMapAt_spec]
  rw [Work.SSGRoute.localUnitsMap_spec]

set_option maxHeartbeats 4000000
/-- **The level class `finZH` is the restriction of the global level class to the decomposition
group.**  The content is the group-naturality of `ExtH1.gammaHom`
(`Work.SSGRoute.extHMap_gammaHom_eq`): both sides are the `Ext¹`-class of the `1`-cocycle
`σ ↦ b₀ ↑σ`, the left one directly on `D_{w'}` (with the `D_{w'}`-action
`compHom X ((decompK q).subtype ∘ finZF)`), the right one as the restriction of the class of `b₀` on
`Gal(L/k)` (which uses `(decompK q).subtype ∘ finZF = galRes ∘ (decompK w').subtype`). -/
theorem finZH_eq_extHRestrict (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hbA : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hb₀A : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g)
    (hZF : Work.SSGRoute.PT.finZF hKL A hA = finDKRg hKL A hA) :
    (SSGRoute.PTExt.extHRestrict
        (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)))
        (Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
          (T := T) (M := M) b₀ hψ)
      : SSGRoute.PTExt.extH
          (Rep.res (finDKRg hKL A hA)
            (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
              (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
                (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))) 1)
    = (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hbA b₀ hb₀A).comp
        (CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.eqToHom (congrArg (fun t => Rep.res t
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := ↥K)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))) hZF)))
        (add_zero 1) := by
  classical
  let X := Work.SSGRoute.PT.VFcoef p M T
  let GalL := ↥L ≃ₐ[k] ↥L
  let GalK := ↥K ≃ₐ[k] ↥K
  let q : NK.GlobalCFT.Place ↥K := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)
  let w : NK.GlobalCFT.Place ↥L := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)
  let DW := ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L) w)
  let Dq := ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥K) q)
  let subw : DW →* GalL := (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w).subtype
  let subq : Dq →* GalK := (SSGRoute.PTExt.decompK (k := k) (K := ↥K) q).subtype
  let dkr : DW →* Dq := finDKRg hKL A hA
  let fZF : DW →* Dq := Work.SSGRoute.PT.finZF hKL A hA
  letI hActL : DistribMulAction GalL X :=
    DistribMulAction.compHom X (SSGRoute.PTExt.galRes k (↥K) (↥L))
  haveI hCommZL : SMulCommClass GalL ℤ X :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommCL : SMulCommClass GalL SSGRoute.PTExt.Coeff X :=
    ⟨fun g c m => smul_comm g c.down m⟩
  haveI hCommZK : SMulCommClass GalK ℤ X :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommCK : SMulCommClass GalK SSGRoute.PTExt.Coeff X :=
    ⟨fun g c m => smul_comm g c.down m⟩
  letI act1 : DistribMulAction DW X := DistribMulAction.compHom X (subq.comp dkr)
  haveI hC1 : @SMulCommClass DW SSGRoute.PTExt.Coeff X act1.toSMul _ :=
    Work.SSGRoute.PT.smulCommClass_compHom_aux (X := X) (R := SSGRoute.PTExt.Coeff) (subq.comp dkr)
  letI act2 : DistribMulAction DW X := DistribMulAction.compHom X (subq.comp fZF)
  haveI hC2 : @SMulCommClass DW SSGRoute.PTExt.Coeff X act2.toSMul _ :=
    Work.SSGRoute.PT.smulCommClass_compHom_aux (X := X) (R := SSGRoute.PTExt.Coeff) (subq.comp fZF)
  have hf : dkr = fZF := hZF.symm
  have hres : Rep.res fZF (Rep.res subq (SSGRoute.PTExt.modRep GalK X))
      = Rep.res dkr (Rep.res subq (SSGRoute.PTExt.modRep GalK X)) :=
    (congrArg (fun t => Rep.res t (Rep.res subq (SSGRoute.PTExt.modRep GalK X))) hf).symm
  let hζ1 : @Work.GroupCohomology.Z1 DW X _ _ act1 :=
    ⟨fun σ => b₀ (subw σ), by
      rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
      intro g hh
      show b₀ (subw (g * hh)) = (subq (dkr g)) • b₀ (subw hh) + b₀ (subw g)
      rw [map_mul, hψ (subw g) (subw hh),
        show subq (dkr g) = SSGRoute.PTExt.galRes k (↥K) (↥L) (subw g) from
          Work.SSGRoute.decompKRestrict_coe k ↥K ↥L q w (finHWg hKL A hA) g]⟩
  let hζ2 : @Work.GroupCohomology.Z1 DW X _ _ act2 :=
    ⟨fun σ => b₀ (subw σ), by
      rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
      intro g hh
      show b₀ (subw (g * hh)) = (subq (fZF g)) • b₀ (subw hh) + b₀ (subw g)
      rw [map_mul, hψ (subw g) (subw hh),
        show subq (fZF g) = SSGRoute.PTExt.galRes k (↥K) (↥L) (subw g) from
          Work.SSGRoute.PT.finZF_spec hKL A hA g]⟩
  -- the restriction of `levelClassOf` to `D_w`, in the `gammaZ1` spelling with the `dkr`-action
  have hL : SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w)
        (Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
          (T := T) (M := M) b₀ hψ)
      = (@Work.SSGRoute.ExtH1.gammaZ1 DW _ X _ act1 hC1
          (Work.SSGRoute.augSES_shortExact DW) hζ1) := by
    simp only [SSGRoute.PT.levelClassOf, SSGRoute.PTExt.extHRestrict]
    conv_lhs =>
      change SSGRoute.PTExt.extHMap (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w).subtype
        (𝟙 (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w).subtype
          (SSGRoute.PTExt.modRep GalL X)))
        ((Work.SSGRoute.ExtH1.gammaHom GalL X (Work.SSGRoute.augSES_shortExact GalL)
          ((Work.GroupCohomology.H1π GalL X) ⟨b₀, fun g h => hψ g h⟩)))
    rw [Work.SSGRoute.extHMap_gammaHom_eq
      (r := (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w).subtype)]
    rw [Work.SSGRoute.ExtH1.gammaHom_H1π]
  -- the level class `finZH`, in the `gammaZ1` spelling with the `fZF`-action
  have hR : (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hbA b₀ hb₀A)
      = (@Work.SSGRoute.ExtH1.gammaZ1 DW _ X _ act2 hC2
          (Work.SSGRoute.augSES_shortExact DW) hζ2) := by
    simp only [finZH, finLevelClass, Work.SSGRoute.ExtH1.gammaHom_H1π]
    congr 1
  rw [hL, hR]
  exact @Work.SSGRoute.PT.gammaZ1_levelChange_aux DW GalK Dq _ _ _ X _ _ hCommCK
    subq dkr fZF hf hres hζ1 hζ2 (fun _ => rfl) hC1 hC2

/-! ## The supplies of clause (7)'s assembly which do not involve the push -/

/-- **`p` kills the level pairing of a `p`-torsion `Ext`-variable.**  `levelPair` is linear in its
`Ext` variable (`PT.pt_levelPair_nsmul_fst`), and the pairing of `0` is `0`
(`Work.SSGRoute.levelPair_zero`).  This is the `p`-torsion supply of clause (7)'s class-formation
step (the summands `χ (ι_w (extLoc w Y))` of the reciprocity sum are `p`-torsion because `Y` is
built from the `ZMod p`-module `M' = DualMod p (M ⊗ T)`). -/
theorem nsmul_levelPair_idleRepMap (p : ℕ) [Fact p.Prime] {k K L : Type} [Field k]
    [NumberField k] [Field K] [NumberField K] [Field L] [NumberField L] [Algebra k K]
    [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L]
    {M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)}
    (X : CategoryTheory.Abelian.Ext M (SSGRoute.PTExt.idelesK k K) 1)
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1)
    (hX : p • X = 0) (hh : p • h = 0) :
    p • SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k K L)
        (Work.SSGRoute.idleRepMap k K L) X h = 0 := by
  rw [Work.SSGRoute.PT.pt_levelPair_nsmul_fst, hX, Work.SSGRoute.levelPair_zero]

/-- **The finite places of `S'` cut out distinct places of any finite Galois level `L`.**  For
`S'` a finite set of pairwise non-`G_k`-conjugate finite places of `Ω`, the map
`A ↦ ofFinite (finQW L A)` is injective on `S'` — the reindexing input of clause (7)'s assembly
(`∑_{A ∈ S'} = ∑_{w ∈ W}`).  This is the `σ = 1` case of the proved
`Work.SSGRoute.PT.finQW_smul_injective` (`PT/vf_transverse.lean`). -/
theorem finQW_ofFinite_injective (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
    [IsGalois k L] (S' : Finset (ValuationSubring Ω)) (hS'fin : ∀ A ∈ S', SSGRoute.IsFinPlace k A)
    (hS'disj : ∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace k A B → A = B)
    (A B : ValuationSubring Ω) (hA : A ∈ S') (hB : B ∈ S')
    (h : NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A (hS'fin A hA))
       = NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L B (hS'fin B hB))) :
    A = B := by
  classical
  refine Work.SSGRoute.PT.finQW_smul_injective L (↑S') ?_ ?_ A B hA hB 1 ?_
  · intro v hv; exact hS'fin v (Finset.mem_coe.mp hv)
  · intro v hv w hw hc
    exact hS'disj v (Finset.mem_coe.mp hv) w (Finset.mem_coe.mp hw) hc
  · simpa using h

/-- **The square of the natural family in the `finZB`/`finZBg` spelling**: the localisation of the
global dictionary class is the local dictionary class (the `hsq` supply of clause (7); the
`.2.2.2.1` conjunct of `PT.finZB_spec`). -/
theorem finZB_square (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hl : SSGRoute.IsLocConstOn ⊤ b) :
    SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
        (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M b))
      = Work.SSGRoute.PT.finZB p K ζ hζ hζK T hT M A hA b :=
  (finZB_spec p M A hA).2.2.2.1 b hb hl

/-! ## The push itself, from the two bricks -/

/-- **The level pairing `finZZ` is the localisation of the global level pairing** — the *push* of
clause (7), with the two `Rep`-spelling bricks `hZI` (`PT.finZI` vs `localUnitsMap`) and `hZH`
(`PT.finZH` vs `extHRestrict` of the global level class) taken as hypotheses, together with the
square `hSq` (`PT.finZB_spec`'s `.2.2.2.1`) replacing the local class `finZB a` by the localisation
of the global class `finZBg a`.

The proof is the `finZZ_push` assembly: `PT.Y3Key.levelPair_transport'` moves the three data
(`f = finZF ↦ decompKRestrict`, `ι = finZI ↦ localUnitsMap`, `h = finZH ↦ extHRestrict`) across
`hZF`, and `Work.SSGRoute.levelPair_extLoc_eq_push` computes the localisation of a level pairing.
**Only the two bricks are missing** (`finZI_eq_localUnitsMap` is proved; `finZH_eq_extHRestrict` is
statement-only) — this theorem isolates the remaining gap exactly. -/
theorem finZZ_eq_extLoc_of_bricks (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g)
    (hZF : Work.SSGRoute.PT.finZF hKL A hA = finDKRg hKL A hA)
    (hZI : Work.SSGRoute.PT.finZI hKL A hA
      = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.eqToHom (congrArg (fun t => Rep.res t
            (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
              (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)))) hZF))
          (Work.SSGRoute.localUnitsMap k (↥K) (↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (finHWg hKL A hA)))
    (hZH : (SSGRoute.PTExt.extHRestrict
        (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)))
        (Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
          (T := T) (M := M) b₀ hψ)
      : SSGRoute.PTExt.extH
          (Rep.res (finDKRg hKL A hA)
            (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := ↥K)
                (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
              (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
                (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))) 1)
      = (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀).comp
        (CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.eqToHom (congrArg (fun t => Rep.res t
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := ↥K)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))) hZF)))
        (add_zero 1))
    (hSq : SSGRoute.PTExt.extLoc (k := k)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
        (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
      = Work.SSGRoute.PT.finZB p K ζ hζ hζK T hT M A hA a) :
    Work.SSGRoute.PT.finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀
      = SSGRoute.PTExt.extLoc (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
          (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
            (Work.SSGRoute.idleRepMap k (↥K) (↥L))
            (SSGRoute.PTExt.extToIdeles (k := k)
              (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
            (Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
              (T := T) (M := M) b₀ hψ)) := by
  classical
  let A0 : Rep.{0} Coeff ↥(SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) :=
    SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
  let M0 : Rep.{0} Coeff ↥(SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) :=
    Rep.res (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
  rw [Work.SSGRoute.PT.finZZ]
  rw [← hSq]
  rw [← Work.SSGRoute.levelPair_extLoc_eq_push (k := k) (K := ↥K) (L := ↥L)
    (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
    (Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
      (T := T) (M := M) b₀ hψ)
    (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
    (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (finHWg hKL A hA)]
  refine Work.SSGRoute.Y3Key.levelPair_transport' (f₁ := Work.SSGRoute.PT.finZF hKL A hA)
    (f₂ := finDKRg hKL A hA) (A := A0) (M := M0)
    (B' := SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)))
    (r := 1) (s := 1)
    (x := SSGRoute.PTExt.extLoc (k := k) (K := ↥K)
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
      (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a)))
    (ρA := CategoryTheory.eqToHom (congrArg (fun t => Rep.res t A0) hZF))
    (ρM := CategoryTheory.eqToHom (congrArg (fun t => Rep.res t M0) hZF))
    (σM := CategoryTheory.eqToHom (congrArg (fun t => Rep.res t M0) hZF.symm))
    (ι₁ := Work.SSGRoute.PT.finZI hKL A hA)
    (ι₂ := Work.SSGRoute.localUnitsMap k (↥K) (↥L)
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (finHWg hKL A hA))
    (h₁ := Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀)
    (h₂ := SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)))
      (Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
        (T := T) (M := M) b₀ hψ))
    (hρσM := ?_) (hι := hZI) (hh := hZH) (hx := ?_)
  · rw [CategoryTheory.eqToHom_trans]
    exact CategoryTheory.eqToHom_refl _ _
  · exact Work.SSGRoute.Y3Key.extRes_transport' (A := A0) (M := M0) (r := 1)
      (x := SSGRoute.PTExt.extLoc (k := k) (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
        (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a)))
      hZF.symm

end

end Work.SSGRoute.PT.G1plusOwn
