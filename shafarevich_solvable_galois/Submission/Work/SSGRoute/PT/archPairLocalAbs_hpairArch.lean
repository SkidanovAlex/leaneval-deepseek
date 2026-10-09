import Mathlib
import Submission.Work.SSGRoute.PT.archPairAbstract
import Submission.Work.SSGRoute.PT.archPair_level_independent
import Submission.Work.SSGRoute.PT.extHRestrict_levelClassOf_eq_of_eqOn
import Submission.Work.SSGRoute.PT.archPairLocal_natural
import Submission.Work.SSGRoute.LeadArch2.gammaHom_H1pi_eq_eCoh_or_neg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct
universe v u

attribute [local instance] Fintype.ofFinite
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.PT

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

/-- **The two `shiftFunctorZero'`'s on `CochainComplex C ℤ` agree.**  `CochainComplex.shiftFunctorZero'`
is the componentwise one (`CochainComplex.shiftFunctorZero'_hom_app_f`), the general
`CategoryTheory.shiftFunctorZero'` is `eqToIso _ ≪≫ shiftFunctorZero _ _`, and
`CochainComplex.shiftFunctorZero_eq` identifies the latter with the former. -/
theorem shiftFunctorZero'_cochain_eq {C : Type u} [Category.{v} C] [Preadditive C] :
    (CategoryTheory.shiftFunctorZero' (CochainComplex C ℤ) (0:ℤ) rfl :
      shiftFunctor (CochainComplex C ℤ) (0:ℤ) ≅ 𝟭 (CochainComplex C ℤ)) =
      CochainComplex.shiftFunctorZero' C 0 rfl := by
  simp only [CategoryTheory.shiftFunctorZero', eqToIso_refl, Iso.refl_trans]
  exact CochainComplex.shiftFunctorZero_eq C

/-- **`equivHomShift` of a `0`-cocycle given by a cochain map.**  For `c : K ⟶ L` in
`CochainComplex C ℤ`, the shifted hom `K ⟶ L⟦0⟧` corresponding to the cocycle
`Cocycle.ofHom c` is the "shifted" map `ShiftedHom.mk₀ 0 rfl c`.  Proved componentwise using
`CochainComplex.shiftFunctorZero'_inv_app_f`. -/
theorem equivHomShift_symm_ofHom {C : Type u} [Category.{v} C] [Preadditive C]
    {K L : CochainComplex C ℤ} (c : K ⟶ L) :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm
      (CochainComplex.HomComplex.Cocycle.ofHom c) =
      ShiftedHom.mk₀ (0:ℤ) rfl c := by
  rw [CochainComplex.HomComplex.Cocycle.equivHomShift_symm_apply]
  rw [ShiftedHom.mk₀]
  apply HomologicalComplex.hom_ext
  intro i
  rw [CochainComplex.HomComplex.Cocycle.homOf_f]
  rw [CochainComplex.HomComplex.Cocycle.rightShift_coe]
  rw [CochainComplex.HomComplex.Cocycle.ofHom_coe]
  rw [CochainComplex.HomComplex.Cochain.rightShift_v (CochainComplex.HomComplex.Cochain.ofHom c)
        0 0 (show (0:ℤ) + 0 = 0 by simp) i i (show i + 0 = i by simp) i (show i + 0 = i by simp)]
  rw [CochainComplex.HomComplex.Cochain.ofHom_v]
  rw [HomologicalComplex.comp_f]
  rw [shiftFunctorZero'_cochain_eq]
  rw [CochainComplex.shiftFunctorZero'_inv_app_f]
  rfl

/-- **The augmentation of a projective resolution, in degree-zero `Ext`.**  For a projective
resolution `R` of `X`, a morphism `f : R.complex.X 0 ⟶ Y` of degree `0` with
`R.complex.d 1 0 ≫ f = 0` and a morphism `g : X ⟶ Y` with `f = R.π.f 0 ≫ g`, the class
`R.extMk f 1 rfl hf` is `Ext.mk₀ g`.  This is the degree-zero input of the comparison between the
bar-resolution realisation `eCoh` and the alternating-bar realisation `extMk` of
`Hⁿ(G, -) ≃ Extⁿ_G(ℤ, -)`. -/
theorem extMk_fst_eq_mk₀ {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C] {X Y : C}
    (R : ProjectiveResolution X) (f : R.complex.X 0 ⟶ Y)
    (hf : R.complex.d 1 0 ≫ f = 0) (g : X ⟶ Y) (hfg : f = R.π.f 0 ≫ g) :
    R.extMk f 1 rfl hf = Abelian.Ext.mk₀ g := by
  let := HasDerivedCategory.standard C
  apply Abelian.Ext.ext
  rw [ProjectiveResolution.extMk_hom, Abelian.Ext.mk₀_hom]
  rw [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  have hcoc : CochainComplex.HomComplex.Cocycle.toSingleMk
        ((R.cochainComplexXIso (-↑(0:ℕ)) 0 rfl).hom ≫ f)
        (show (-↑(0:ℕ) : ℤ) + 0 = 0 by simp) (-↑(1:ℕ)) (by lia)
        (by rw [ProjectiveResolution.cochainComplex_d R (-↑(1:ℕ)) (-↑(0:ℕ)) 1 0]
            simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.id_comp]
            rw [hf]
            simp only [Limits.comp_zero, Limits.zero_comp]) =
      CochainComplex.HomComplex.Cocycle.ofHom
        (R.π' ≫ (CochainComplex.singleFunctor C 0).map g) := by
    apply CochainComplex.HomComplex.Cocycle.ext
    rw [CochainComplex.HomComplex.Cocycle.toSingleMk_coe,
      CochainComplex.HomComplex.Cocycle.ofHom_coe]
    apply (CochainComplex.HomComplex.Cochain.toSingleEquiv (C := C) (X := Y)
      (K := R.cochainComplex) (p := 0) (q := 0) (n := 0) (show (0:ℤ) + 0 = 0 by simp)).injective
    rw [CochainComplex.HomComplex.Cochain.toSingleEquiv_toSingleMk]
    show (R.cochainComplexXIso (-↑(0:ℕ)) 0 rfl).hom ≫ f =
      (CochainComplex.HomComplex.Cochain.ofHom
        (R.π' ≫ (CochainComplex.singleFunctor C 0).map g)).v 0 0 (show (0:ℤ)+0 = 0 by simp) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom
    rw [CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f,
      ProjectiveResolution.π'_f_zero]
    simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.id_comp, Category.comp_id]
    rw [hfg]
    rfl
  have hΞ : CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.toSingleMk
          ((R.cochainComplexXIso (-↑(0:ℕ)) 0 rfl).hom ≫ f)
          (show (-↑(0:ℕ) : ℤ) + 0 = 0 by simp) (-↑(1:ℕ)) (by lia)
          (by rw [ProjectiveResolution.cochainComplex_d R (-↑(1:ℕ)) (-↑(0:ℕ)) 1 0]
              simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.id_comp]
              rw [hf]
              simp only [Limits.comp_zero, Limits.zero_comp])) =
      ShiftedHom.mk₀ (0:ℤ) rfl (R.π' ≫ (CochainComplex.singleFunctor C 0).map g) := by
    rw [hcoc]
    exact equivHomShift_symm_ofHom _
  erw [hΞ]
  erw [ShiftedHom.map_mk₀]
  rw [Functor.map_comp]
  simp only [ShiftedHom.mk₀]
  simp only [Category.assoc]
  rw [IsIso.inv_hom_id_assoc]
  rw [← Category.assoc]
  erw [← NatTrans.naturality (DerivedCategory.singleFunctorIsoCompQ C 0).hom g]
  simp only [Category.assoc]
  erw [← NatTrans.naturality (shiftFunctorZero' (DerivedCategory C) (0:ℤ) rfl).inv]
  simp only [Functor.id_map]
  rw [← Iso.app_hom (DerivedCategory.singleFunctorIsoCompQ C 0) Y,
      ← Iso.app_inv (DerivedCategory.singleFunctorIsoCompQ C 0) Y]
  rw [Iso.hom_inv_id_assoc]
  rw [show (rfl : (0:ℤ) = 0) = Abelian.Ext.mk₀._proof_1 from Subsingleton.elim _ _]
  rfl


/-! ## Level independence of `archPairValueZAbs` in the `eCoh` realisation

The two-step level independence used by the value formula: if `L` and `L'` are two levels with a
common upper level `L''`, two `1`-cocycles `z`, `z'` (at `L`, `L'`) whose restrictions to `D_{u''}`
agree with a cocycle `z''` at `L''`, then the two values of `archPairValueZAbs` agree.  Both steps
are `PT.archPair_level_independent_loc`. -/

theorem archPairValueZAbs_level_indep_eCoh
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : Work.SSGRoute.PT.SeamDict p k Ω K ζ hζ hζK T hT)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
      [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (a : (Ω ≃ₐ[k] Ω) → M)
    (L L' : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField ↥L'] [FiniteDimensional k L'] [IsGalois k L']
    (hKL : K ≤ L) (hKL' : K ≤ L')
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    [Algebra ↥K ↥L'] [IsScalarTower k ↥K ↥L'] [IsScalarTower ↥K ↥L' Ω]
    (w : NK.GlobalCFT.Place ↥K) (u : NK.GlobalCFT.Place ↥L)
    (hu : NK.GlobalCFT.Place.LiesOver u w)
    (L'' : IntermediateField k Ω) [NumberField ↥L''] [FiniteDimensional k L''] [IsGalois k L'']
    (hKL'' : K ≤ L'') (hLL'' : L ≤ L'') (hL'L'' : L' ≤ L'')
    [Algebra ↥K ↥L''] [IsScalarTower k ↥K ↥L''] [IsScalarTower ↥K ↥L'' Ω]
    [Algebra ↥L ↥L''] [IsScalarTower k ↥L ↥L''] [IsScalarTower ↥L ↥L'' Ω]
    [IsScalarTower ↥K ↥L ↥L'']
    [Algebra ↥L' ↥L''] [IsScalarTower k ↥L' ↥L''] [IsScalarTower ↥L' ↥L'' Ω]
    [IsScalarTower ↥K ↥L' ↥L'']
    (u' : NK.GlobalCFT.Place ↥L') (hu' : NK.GlobalCFT.Place.LiesOver u' w)
    (u'' : NK.GlobalCFT.Place ↥L'') (hu''w : NK.GlobalCFT.Place.LiesOver u'' w)
    (hu''u : NK.GlobalCFT.Place.LiesOver u'' u)
    (hu''u' : NK.GlobalCFT.Place.LiesOver u'' u')
    (z : groupCohomology.cocycles₁ (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))))
    (z' : groupCohomology.cocycles₁ (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu')
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))))
    (z'' : groupCohomology.cocycles₁ (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L'' w u'' hu''w)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))))
    (hz'' : ∀ g : ↥(SSGRoute.PTExt.decompK (k := k) u''),
      (z'' : ↥(SSGRoute.PTExt.decompK (k := k) u'') → Work.SSGRoute.PT.VFcoef p M T) g =
        (z : ↥(SSGRoute.PTExt.decompK (k := k) u) → Work.SSGRoute.PT.VFcoef p M T)
          (Work.SSGRoute.decompKRestrict k ↥L ↥L'' u u'' hu''u g))
    (hz''' : ∀ g : ↥(SSGRoute.PTExt.decompK (k := k) u''),
      (z'' : ↥(SSGRoute.PTExt.decompK (k := k) u'') → Work.SSGRoute.PT.VFcoef p M T) g =
        (z' : ↥(SSGRoute.PTExt.decompK (k := k) u') → Work.SSGRoute.PT.VFcoef p M T)
          (Work.SSGRoute.decompKRestrict k ↥L' ↥L'' u' u'' hu''u' g)) :
    Work.SSGRoute.PT.archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c w a L hKL u hu
        (SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
          (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
            (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
              (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
          ((groupCohomology.H1π _).hom z)) =
      Work.SSGRoute.PT.archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c w a L' hKL' u' hu'
        (SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u')
          (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L' w u' hu')
            (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
              (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
          ((groupCohomology.H1π _).hom z')) := by
  simp only [Work.SSGRoute.PT.archPairValueZAbs]
  refine (Work.SSGRoute.PT.archPair_level_independent_loc p k Ω K T χ hχadd hχcompat M
    L L'' hKL hKL'' hLL'' w u u'' hu hu''u hu''w (bc M c w a) z z'' hz'').trans ?_
  exact (Work.SSGRoute.PT.archPair_level_independent_loc p k Ω K T χ hχadd hχcompat M
    L' L'' hKL' hKL'' hL'L'' w u' u'' hu' hu''u' hu''w (bc M c w a) z' z'' hz''').symm

/-- **The value formula (`hpairArch`) at the involution, over an abstract seam dictionary.**

The `sorryAx`-free mirror of `Work.SSGRoute.PT.archPairLocal_hpairArch`
(`Submission/Work/SSGRoute/PT/archPairLocal_hpairArch.lean`): same statement with
`PT.archPairLocal ↦ PT.archPairLocalAbs bc`, `PT.archβc ↦ bc`, and the right-hand side written as
`PT.archPairValueZAbs bc … (PT.extHRestrict (decompK u) (PT.levelClassOf ψ))`, which is *verbatim*
the concrete right-hand side (`PT.archPairValueZAbs` unfolds by definition to
`χ L hKL (iota u (levelPair (decompKRestrict …) (localUnitsMap …) (bc M c (archW k Ω K φ) a) z))`).
In particular **no property of `bc` is needed** (both sides use the level-free term
`bc M c (archW k Ω K φ) a`): the content is the independence of the value from the level.

Instantiated at `bc := PT.archβcSeam` (with the `rfl` lemmas `PT.archPairLocalAbs_archβc` /
`PT.archPairValueZAbs_archβc` in `PT/archPairAbstract.lean`) this *is* the concrete value formula,
which is the single input of the hub's clause (7) (`PT.hrecJoint_archFamily`) besides the class
formation; the concrete one is `sorryAx`-tainted through `archβc`'s definition, this one is not.

Route (from the concrete statement's docstring; all inputs are on disk and are `sorry`-free).
Both sides are values of `χ ∘ iota ∘ levelPair` at the *same* coefficient `bc M c (archW k Ω K φ) a`:
the left at the fixed level `L_c := PT.archPairLocalL k Ω K c hc1` with `z = PT.zLocal … b` (the
descent of `b`, pinned by `PT.bDaux_spec` on `D_{u_c} = (⟨c⟩).map (res k L_c)`, and
`PT.archPairLocalL_res` gives `res k L_c c ≠ 1`), the right at `L` with
`z = PTExt.extHRestrict (decompK u) (levelClassOf ψ)`.

1. Go up to `L'' := L_c ⊔ L`: its `NumberField ↥L''`, `FiniteDimensional k L''`, `IsGalois k L''`
   instances, the `≤`-relations `K ≤ L''`, `L_c ≤ L''`, `L ≤ L''`, and the induced
   `Algebra ↥K ↥L''`/`Algebra ↥L_c ↥L''`/`Algebra ↥L ↥L''` with their `IsScalarTower` companions
   (`IntermediateField.inclusion`, `IsScalarTower.of_algebraMap_eq (fun _ => rfl)`).  Take the seam
   place `u'' := NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥L'' Ω)))`;
   `PT.liesOver_linked` gives `u'' | u_c`, `u'' | u`, `u'' | archW k Ω K φ`, and `PT.decompK_linked`
   gives `D_{u''} = (⟨c⟩).map (res k L'')`.  (`PT.archPair_level_independent_loc`'s proof shows the
   necessary trick `cases hinst` making the ambient `Algebra ↥L ↥L''` the canonical one, and that
   the towers force it.)
2. Apply `PT.archPair_level_independent_loc` (proved) from `L_c` to `L''`, with
   `x := bc M c (archW k Ω K φ) a`, `z := ⟨bDaux …, _⟩` (the `D_{u_c}`-cocycle, transported to
   `D_{u''}` by restriction), and from `L` to `L''` with the level-`L''` cocycle `ψ|_{D_{u''}}`.
   Its pointwise-agreement hypothesis on `D_{u''}` follows from `hres` and
   `res_{L''} = res_{L''→L} ∘ res_L` on `⟨c⟩ = {1,c}` (`hc2`); on the `L_c` side from
   `PT.bDaux_spec`.
3. The two resulting `z`-classes agree: the `L_c`-side one is `PT.zLocal … b` by construction
   (`zLocal = eCoh 1 _ _ ((H1π _).hom ⟨bDaux, _⟩)`), the `L`-side one is the restriction of
   `levelClassOf ψ`, identified with the descent of `b` by
   `PT.extHRestrict_levelClassOf_eq_of_eqOn` (proved, input `Work.SSGRoute.extHMap_gammaHom_eq`),
   again using `hres`.

`hus` identifies `u` as the seam place of `L`; `hb` is the guard of `PT.archPairLocalAbs`
(derivable from `hres` + `hψ` via surjectivity of `res k L` on `D_u`).

**Restatement at `p = 2`** (lead design `Submission/_lead_design/ssg_arch2_2320.md`, §(b), §(c)(6)):
the two sides use *different* `H¹ → Ext¹` realisations — the right-hand side uses `levelClassOf`,
i.e. `ExtH1.gammaHom` (augmentation sequence), the left-hand side uses `zLocal`, i.e. `eCoh 1`
(bar resolution) — and the workspace has no lemma relating them.  `B1`
(`gammaHom_H1π_eq_eCoh_or_neg`) supplies the comparison **up to sign**, so the statement is
established at `p = 2`, where the sign is harmless (`±x = x` in `ZMod 2`).  This is the only prime
at which the value formula is consumed (the `p = 2` branch of the hub's clause (7)). -/
-- Provenance.  The steps of this proof follow the lead's reference argument for the same
-- obligation (`Work.SSGRoute.LeadArch2.archPairLocalAbs_hpairArch_two`): the common upper level
-- `L_c ⊔ L` with its tower instances, the two `archPairValueZAbs_level_indep_eCoh` steps, the
-- unfolding of `zLocal`, the pointwise agreement on `D_{u''}` from `bDaux_spec` + `hres`, and the
-- sign handling at `p = 2`.  The single imported input is the shared library lemma B1,
-- `Work.SSGRoute.LeadArch2.gammaHom_H1pi_eq_eCoh_or_neg` (the `H¹ → Ext¹` realisation comparison).
-- The `ShiftedHom`/`toSingleMk` degree-zero bookkeeping above
-- (`shiftFunctorZero'_cochain_eq`, `equivHomShift_symm_ofHom`, `extMk_fst_eq_mk₀`) is this file's own.
theorem archPairLocalAbs_hpairArch_two
    (p : ℕ) [Fact p.Prime] (hp2 : p = 2) (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
      [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (φ : Ω →+* ℂ) (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (hus : u = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
      (φ.comp (algebraMap (↥L) Ω))))
    (ψ : (↥L ≃ₐ[k] ↥L) → VFcoef p M T)
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g)
    (hres : ∀ σ ∈ Subgroup.zpowers c, b σ = ψ (SSGRoute.res k L σ)) :
    archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b =
      archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
          (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ)) := by
  let LC : IntermediateField k Ω := Work.SSGRoute.PT.archPairLocalL k Ω K c hc1
  haveI cfin : FiniteDimensional k LC := Work.SSGRoute.PT.archPairLocalL_fin k Ω K c hc1
  haveI cgal : IsGalois k LC := Work.SSGRoute.PT.archPairLocalL_gal k Ω K c hc1
  haveI cnf : NumberField ↥LC := inferInstance
  have hKLc : K ≤ LC := Work.SSGRoute.PT.archPairLocalL_le k Ω K c hc1
  letI calg : Algebra ↥K ↥LC := (IntermediateField.inclusion hKLc).toAlgebra
  letI ctw1 : IsScalarTower k ↥K ↥LC := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI ctw2 : IsScalarTower ↥K ↥LC Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hres_c : SSGRoute.res k LC c ≠ 1 := Work.SSGRoute.PT.archPairLocalL_res k Ω K c hc1
  let uC : NK.GlobalCFT.Place ↥LC :=
    NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥LC Ω)))
  have huC : NK.GlobalCFT.Place.LiesOver uC (Work.SSGRoute.PT.archW k Ω K φ) :=
    Work.SSGRoute.PT.liesOver_linked k Ω K LC φ
  have hDuC : SSGRoute.PTExt.decompK (k := k) uC = (Subgroup.zpowers c).map (SSGRoute.res k LC) :=
    Work.SSGRoute.PT.decompK_linked k Ω LC c hc2 hc1 φ hφ
  -- the common upper level
  have hKL'' : K ≤ LC ⊔ L := le_trans hKLc le_sup_left
  have hLCL'' : LC ≤ LC ⊔ L := le_sup_left
  have hLL'' : L ≤ LC ⊔ L := le_sup_right
  letI aK : Algebra ↥K ↥(LC ⊔ L) := (IntermediateField.inclusion hKL'').toAlgebra
  letI tK1 : IsScalarTower k ↥K ↥(LC ⊔ L) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI tK2 : IsScalarTower ↥K ↥(LC ⊔ L) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI aC : Algebra ↥LC ↥(LC ⊔ L) := (IntermediateField.inclusion hLCL'').toAlgebra
  letI tC1 : IsScalarTower k ↥LC ↥(LC ⊔ L) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI tC2 : IsScalarTower ↥LC ↥(LC ⊔ L) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI tC3 : IsScalarTower ↥K ↥LC ↥(LC ⊔ L) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI aL : Algebra ↥L ↥(LC ⊔ L) := (IntermediateField.inclusion hLL'').toAlgebra
  letI tL1 : IsScalarTower k ↥L ↥(LC ⊔ L) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI tL2 : IsScalarTower ↥L ↥(LC ⊔ L) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI tL3 : IsScalarTower ↥K ↥L ↥(LC ⊔ L) := IsScalarTower.of_algebraMap_eq (fun x => by
    apply (algebraMap ↥(LC ⊔ L) Ω).injective
    rw [← IsScalarTower.algebraMap_apply ↥L ↥(LC ⊔ L) Ω,
      ← IsScalarTower.algebraMap_apply ↥K ↥L Ω,
      ← IsScalarTower.algebraMap_apply ↥K ↥(LC ⊔ L) Ω])
  haveI fdim'' : FiniteDimensional k ↥(LC ⊔ L) := inferInstance
  haveI gal'' : IsGalois k ↥(LC ⊔ L) := inferInstance
  haveI nf'' : NumberField ↥(LC ⊔ L) := inferInstance
  let u'' : NK.GlobalCFT.Place ↥(LC ⊔ L) :=
    NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥(LC ⊔ L) Ω)))
  have hu''w : NK.GlobalCFT.Place.LiesOver u'' (Work.SSGRoute.PT.archW k Ω K φ) :=
    Work.SSGRoute.PT.liesOver_linked k Ω K (LC ⊔ L) φ
  have hu''C : NK.GlobalCFT.Place.LiesOver u'' uC :=
    Work.SSGRoute.PT.liesOver_linked k Ω LC (LC ⊔ L) φ
  have hu''L : NK.GlobalCFT.Place.LiesOver u'' u := by
    rw [hus]; exact Work.SSGRoute.PT.liesOver_linked k Ω L (LC ⊔ L) φ
  -- unfold the left-hand side
  rw [Work.SSGRoute.PT.archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b hb]
  dsimp only
  -- the cocycles
  let zF : ↥(SSGRoute.PTExt.decompK (k := k) uC) → Work.SSGRoute.PT.VFcoef p M T :=
    Work.SSGRoute.PT.bDaux p k Ω K T M c hc2 LC hKLc hres_c uC hDuC b hb
      (Work.SSGRoute.PT.archW k Ω K φ) huC
  have hzF_mem : zF ∈ groupCohomology.cocycles₁
      (Work.SSGRoute.PT.zRep p k Ω K T M LC uC (Work.SSGRoute.PT.archW k Ω K φ) huC) :=
    Work.SSGRoute.PT.bDaux_mem p k Ω K T M c hc2 LC hKLc hres_c uC hDuC b hb
      (Work.SSGRoute.PT.archW k Ω K φ) huC
  let zF' : ↥(SSGRoute.PTExt.decompK (k := k) u) → Work.SSGRoute.PT.VFcoef p M T :=
    fun d => ψ (d : ↥L ≃ₐ[k] ↥L)
  let zF'' : ↥(SSGRoute.PTExt.decompK (k := k) u'') → Work.SSGRoute.PT.VFcoef p M T :=
    fun g => ψ (Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L g)
  have hzF'_mem : zF' ∈ groupCohomology.cocycles₁
      (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L (Work.SSGRoute.PT.archW k Ω K φ) u hu)
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (Work.SSGRoute.PT.archW k Ω K φ)).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))) := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    simp only [zF', MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul,
      Work.SSGRoute.decompKRestrict_coe]
    exact hψ g h
  have hzF''_mem : zF'' ∈ groupCohomology.cocycles₁
      (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥(LC ⊔ L) (Work.SSGRoute.PT.archW k Ω K φ) u'' hu''w)
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (Work.SSGRoute.PT.archW k Ω K φ)).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))) := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    have hgl : (↑(Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L (g * h)) : ↥L ≃ₐ[k] ↥L)
        = ↑(Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L g)
          * ↑(Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L h) :=
      map_mul _ g h
    have hρ2 : ((Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥(LC ⊔ L)
          (Work.SSGRoute.PT.archW k Ω K φ) u'' hu''w)
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (Work.SSGRoute.PT.archW k Ω K φ)).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))).ρ g)
          (ψ ↑(Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L h))
        = (SSGRoute.PTExt.galRes k (↥K) (↥L))
            ↑(Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L g)
          • ψ ↑(Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L h) := by
      simp only [Rep.res, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Work.SSGRoute.decompKRestrict_coe]
      rw [← SSGRoute.PTExt.galRes_trans (K := ↥K) (L := ↥L) (L' := ↥(LC ⊔ L))
          (g : ↥(LC ⊔ L) ≃ₐ[k] ↥(LC ⊔ L))]
      rfl
    have h1 : zF'' (g * h) = ψ (↑(Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L g)
        * ↑(Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L h)) := by
      show ψ (↑(Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L (g * h))
        : ↥L ≃ₐ[k] ↥L) = _
      rw [hgl]
    rw [h1, hψ, hρ2]
  have hz''' : ∀ g : ↥(SSGRoute.PTExt.decompK (k := k) u''),
      zF'' g = zF' (Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L g) :=
    fun g => rfl
  have hz'' : ∀ d : ↥(SSGRoute.PTExt.decompK (k := k) u''),
      zF'' d = zF (Work.SSGRoute.decompKRestrict k ↥LC ↥(LC ⊔ L) uC u'' hu''C d) := by
    intro d
    have hDu'' : SSGRoute.PTExt.decompK (k := k) u'' =
        (Subgroup.zpowers c).map (SSGRoute.res k (LC ⊔ L)) :=
      Work.SSGRoute.PT.decompK_linked k Ω (LC ⊔ L) c hc2 hc1 φ hφ
    obtain ⟨σ, hσ, hσd⟩ : ∃ σ ∈ Subgroup.zpowers c,
        SSGRoute.res k (LC ⊔ L) σ = (d : ↥(LC ⊔ L) ≃ₐ[k] ↥(LC ⊔ L)) := by
      have hd : (d : ↥(LC ⊔ L) ≃ₐ[k] ↥(LC ⊔ L)) ∈
          (Subgroup.zpowers c).map (SSGRoute.res k (LC ⊔ L)) := by
        rw [← hDu'']
        exact d.2
      exact hd
    have eC : (↑(Work.SSGRoute.decompKRestrict k ↥LC ↥(LC ⊔ L) uC u'' hu''C d)
        : ↥LC ≃ₐ[k] ↥LC) = SSGRoute.res k LC σ := by
      rw [Work.SSGRoute.decompKRestrict_coe, ← hσd]
      exact SSGRoute.PTExt.galRes_trans (K := ↥LC) (L := ↥(LC ⊔ L)) (L' := Ω) σ
    have eL : (↑(Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L d)
        : ↥L ≃ₐ[k] ↥L) = SSGRoute.res k L σ := by
      rw [Work.SSGRoute.decompKRestrict_coe, ← hσd]
      exact SSGRoute.PTExt.galRes_trans (K := ↥L) (L := ↥(LC ⊔ L)) (L' := Ω) σ
    rw [show zF'' d = b σ from by
      show ψ (↑(Work.SSGRoute.decompKRestrict k ↥L ↥(LC ⊔ L) u u'' hu''L d)
        : ↥L ≃ₐ[k] ↥L) = b σ
      rw [eL]
      exact (hres σ hσ).symm,
      show zF (Work.SSGRoute.decompKRestrict k ↥LC ↥(LC ⊔ L) uC u'' hu''C d) = b σ from by
      have hx : Work.SSGRoute.decompKRestrict k ↥LC ↥(LC ⊔ L) uC u'' hu''C d
          = ⟨SSGRoute.res k LC σ, by rw [hDuC]; exact Subgroup.mem_map_of_mem _ hσ⟩ :=
        Subtype.ext eC
      rw [hx]
      exact (Work.SSGRoute.PT.bDaux_spec p k Ω K T M c hc2 LC hKLc hres_c uC hDuC b hb
        (Work.SSGRoute.PT.archW k Ω K φ) huC).2 ⟨σ, hσ⟩]
  have hA := archPairValueZAbs_level_indep_eCoh p k Ω K ζ hζ hζK T hT bc χ hχadd hχcompat M c hc2 hc1
    φ hφ a LC L hKLc hKL (Work.SSGRoute.PT.archW k Ω K φ) uC huC (LC ⊔ L) hKL'' hLCL'' hLL''
    u hu u'' hu''w hu''C hu''L ⟨zF, hzF_mem⟩ ⟨zF', hzF'_mem⟩ ⟨zF'', hzF''_mem⟩ hz'' hz'''
  have hzloc : Work.SSGRoute.PT.zLocal p k Ω K T M c hc2 LC hKLc hres_c uC hDuC b hb
      (Work.SSGRoute.PT.archW k Ω K φ) huC
      = (SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) uC)
          (Work.SSGRoute.PT.zRep p k Ω K T M LC uC (Work.SSGRoute.PT.archW k Ω K φ) huC)
          ((groupCohomology.H1π _).hom ⟨zF, hzF_mem⟩)) := rfl
  -- the H1 -> Ext1 comparison (B1)
  letI hActL : DistribMulAction (↥L ≃ₐ[k] ↥L) (Work.SSGRoute.PT.VFcoef p M T) :=
    DistribMulAction.compHom (Work.SSGRoute.PT.VFcoef p M T) (SSGRoute.PTExt.galRes k (↥K) (↥L))
  haveI hCommZL : SMulCommClass (↥L ≃ₐ[k] ↥L) ℤ (Work.SSGRoute.PT.VFcoef p M T) :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommCL : SMulCommClass (↥L ≃ₐ[k] ↥L) SSGRoute.PTExt.Coeff (Work.SSGRoute.PT.VFcoef p M T) :=
    ⟨fun g c m => smul_comm g c.down m⟩
  letI hActD : DistribMulAction ↥(SSGRoute.PTExt.decompK (k := k) u) (Work.SSGRoute.PT.VFcoef p M T) :=
    DistribMulAction.compHom (Work.SSGRoute.PT.VFcoef p M T)
      ((SSGRoute.PTExt.galRes k (↥K) (↥L)).comp (SSGRoute.PTExt.decompK (k := k) u).subtype)
  haveI hCommZD : SMulCommClass ↥(SSGRoute.PTExt.decompK (k := k) u) ℤ (Work.SSGRoute.PT.VFcoef p M T) :=
    ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
  haveI hCommCD : SMulCommClass ↥(SSGRoute.PTExt.decompK (k := k) u) SSGRoute.PTExt.Coeff
      (Work.SSGRoute.PT.VFcoef p M T) :=
    ⟨fun g c m => smul_comm g c.down m⟩
  have hzp : zF' ∈ Work.GroupCohomology.Z1 ↥(SSGRoute.PTExt.decompK (k := k) u)
      (Work.SSGRoute.PT.VFcoef p M T) :=
    fun g h => hψ (g : ↥L ≃ₐ[k] ↥L) (h : ↥L ≃ₐ[k] ↥L)
  let zp : ↥(Work.GroupCohomology.Z1 ↥(SSGRoute.PTExt.decompK (k := k) u)
      (Work.SSGRoute.PT.VFcoef p M T)) := ⟨zF', hzp⟩
  have hExt : SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ)
      = SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
          (Work.SSGRoute.PT.zRep p k Ω K T M L u (Work.SSGRoute.PT.archW k Ω K φ) hu)
          ((groupCohomology.H1π _).hom ⟨zF', hzF'_mem⟩)
      ∨ SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ)
      = -SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
          (Work.SSGRoute.PT.zRep p k Ω K T M L u (Work.SSGRoute.PT.archW k Ω K φ) hu)
          ((groupCohomology.H1π _).hom ⟨zF', hzF'_mem⟩) := by
    show SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.ExtH1.gammaHom (↥L ≃ₐ[k] ↥L) (Work.SSGRoute.PT.VFcoef p M T)
          (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L))
          (Work.GroupCohomology.H1π (↥L ≃ₐ[k] ↥L) (Work.SSGRoute.PT.VFcoef p M T) ⟨ψ, hψ⟩))
        = SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
            (Work.SSGRoute.PT.zRep p k Ω K T M L u (Work.SSGRoute.PT.archW k Ω K φ) hu)
            ((groupCohomology.H1π _).hom ⟨zF', hzF'_mem⟩)
      ∨ SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.ExtH1.gammaHom (↥L ≃ₐ[k] ↥L) (Work.SSGRoute.PT.VFcoef p M T)
          (Work.SSGRoute.augSES_shortExact (↥L ≃ₐ[k] ↥L))
          (Work.GroupCohomology.H1π (↥L ≃ₐ[k] ↥L) (Work.SSGRoute.PT.VFcoef p M T) ⟨ψ, hψ⟩))
        = -SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
            (Work.SSGRoute.PT.zRep p k Ω K T M L u (Work.SSGRoute.PT.archW k Ω K φ) hu)
            ((groupCohomology.H1π _).hom ⟨zF', hzF'_mem⟩)
    rw [SSGRoute.PTExt.extHRestrict,
      Work.SSGRoute.extHMap_gammaHom_eq (SSGRoute.PTExt.decompK (k := k) u).subtype
        (Work.SSGRoute.PT.VFcoef p M T) ⟨ψ, hψ⟩]
    rw [show (⟨fun h => ψ ((SSGRoute.PTExt.decompK (k := k) u).subtype h), _⟩
          : ↥(Work.GroupCohomology.Z1 ↥(SSGRoute.PTExt.decompK (k := k) u)
              (Work.SSGRoute.PT.VFcoef p M T))) = zp from Subtype.ext rfl]
    rcases Work.SSGRoute.LeadArch2.gammaHom_H1pi_eq_eCoh_or_neg
        (↥(SSGRoute.PTExt.decompK (k := k) u)) (Work.SSGRoute.PT.VFcoef p M T) zp
        hzF'_mem with hB | hB
    · exact Or.inl hB
    · exact Or.inr hB
  have hVzero : Work.SSGRoute.PT.archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c
        (Work.SSGRoute.PT.archW k Ω K φ) a L hKL u hu
        (0 : SSGRoute.PTExt.extH (Work.SSGRoute.PT.zRep p k Ω K T M L u
          (Work.SSGRoute.PT.archW k Ω K φ) hu) 1) = 0 := by
    simp only [Work.SSGRoute.PT.archPairValueZAbs, SSGRoute.PTExt.levelPair,
      Work.SSGRoute.PT.iota_zero, Abelian.Ext.zero_comp]
    have h0 : χ L hKL 0 = χ L hKL 0 + χ L hKL 0 := by
      simpa using hχadd L hKL 0 0 (by simp) (by simp)
    exact add_left_cancel (a := χ L hKL 0) (by simpa using h0.symm)
  have hnegV : Work.SSGRoute.PT.archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c
        (Work.SSGRoute.PT.archW k Ω K φ) a L hKL u hu
        (-(SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
          (Work.SSGRoute.PT.zRep p k Ω K T M L u (Work.SSGRoute.PT.archW k Ω K φ) hu)
          ((groupCohomology.H1π _).hom ⟨zF', hzF'_mem⟩)))
      = -Work.SSGRoute.PT.archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c
        (Work.SSGRoute.PT.archW k Ω K φ) a L hKL u hu
        (SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
          (Work.SSGRoute.PT.zRep p k Ω K T M L u (Work.SSGRoute.PT.archW k Ω K φ) hu)
          ((groupCohomology.H1π _).hom ⟨zF', hzF'_mem⟩)) := by
    have h := Work.SSGRoute.PT.archPairValueZAbs_add_snd p k Ω K ζ hζ hζK T hT bc χ hχadd M c
      hc2 hc1 φ hφ a L hKL u hu
      (-(SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.zRep p k Ω K T M L u (Work.SSGRoute.PT.archW k Ω K φ) hu)
        ((groupCohomology.H1π _).hom ⟨zF', hzF'_mem⟩)))
      (SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
        (Work.SSGRoute.PT.zRep p k Ω K T M L u (Work.SSGRoute.PT.archW k Ω K φ) hu)
        ((groupCohomology.H1π _).hom ⟨zF', hzF'_mem⟩))
    rw [neg_add_cancel, hVzero] at h
    exact eq_neg_iff_add_eq_zero.mpr h.symm
  have hnegself : ∀ x : ZMod p, -x = x := by
    intro x
    have hx : x + x = 0 := by
      have h2 : (2 : ℕ) = p := hp2.symm
      rw [← two_nsmul, h2, ← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self, zero_smul]
    exact neg_eq_iff_add_eq_zero.mpr hx
  have hC : Work.SSGRoute.PT.archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c
        (Work.SSGRoute.PT.archW k Ω K φ) a L hKL u hu
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) u)
          (Work.SSGRoute.PT.levelClassOf p k Ω K T M L ψ hψ))
      = Work.SSGRoute.PT.archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c
        (Work.SSGRoute.PT.archW k Ω K φ) a L hKL u hu
        (SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
          (Work.SSGRoute.PT.zRep p k Ω K T M L u (Work.SSGRoute.PT.archW k Ω K φ) hu)
          ((groupCohomology.H1π _).hom ⟨zF', hzF'_mem⟩)) := by
    rcases hExt with hE | hE
    · rw [hE]
    · rw [hE, hnegV, hnegself]
  rw [hzloc]
  exact hA.trans hC.symm



/-! ## Session state (for continuation) — the `H¹`-realisation bridge `B1`

Everything below records measured facts about the one missing input of the proof of
`archPairLocalAbs_hpairArch_two`, so that the next session does not repeat the search.

**The route** (`Submission/_lead_design/ssg_arch2_2320.md` §(b), §(c)(6)).  `archPairLocalAbs`
unfolds (`archPairLocalAbs_unfold`, PROVED) at the fixed level `L_c = archPairLocalL k Ω K c hc1`
to `archPairValueZAbs … (zLocal …)`, where `zLocal = eCoh 1 _ _ (H1π ⟨bDaux, _⟩)`, while the
right-hand side of the goal has `z = extHRestrict (decompK u) (levelClassOf ψ)`.  By
`Work.SSGRoute.extHMap_gammaHom_eq` (PROVED) the latter is `ExtH1.gammaZ1` of the restricted
cocycle `ζ := ψ ∘ (decompK u).subtype`, i.e. the **augmentation-sequence** realisation
`SS.extClass.comp (mk₀ (cocycleHom ζ))` (`SS := augSES G`, `gammaZ1_apply`), whereas `zLocal` uses
the **bar-resolution** realisation `eCoh 1` (`E0bDefs.lean`).  The workspace contains no lemma
relating the two; `ArchPairLocal_perfect`-style arguments do not avoid it.  Hence B1:

```
gammaHom G M hS (H1π ψ) = eCoh 1 G (modRep G M) (H1π ⟨ψ.1, hψ⟩)   (or its negative)
```

**Measured route for B1** (the `±` is harmless: the target is consumed only at `p = 2`, and the
final comparison is a `ZMod p`-value with `p = 2`):
* the universal cocycle `u := fun g => ExtH1.augDiff G g : G → ↥(ExtH1.augI G)` satisfies
  `IsCrossedHom`, and `cocycleHom G u _ = 𝟙 (augI G)` by `ExtH1.hom_ext_augDiff` +
  `ExtH1.cocycleHom_augDiff`; hence `gammaHom G (augI G) hS (H1π ⟨u,_⟩) = SS.extClass`
  (`gammaHom_H1π`, `gammaZ1_apply`, `phiMap`, `Abelian.Ext.comp_mk₀_id`);
* `Work.SSGRoute.E7cOmega.eCoh_one_comp_mk0` (PROVED) gives, for any `ψ`, that
  `eCoh 1 G (modRep G M) (H1π ⟨ψ.1,hψ⟩) = (eCoh 1 G (augI G) (H1π ⟨u,_⟩)).comp (mk₀ (cocycleHom ψ))`
  (coefficient naturality of `eCoh` along `cocycleHom ψ`, whose composite with `u` is `ψ.1`);
* it therefore remains to compare `E := eCoh 1 G (augI G) (H1π ⟨u,_⟩)` with `SS.extClass`.
  `Work.SSGRoute.eCoh_delta` (PROVED, `±`) at `n = 0` for `SS` plus
  `groupCohomology.δ₀_apply` (Mathlib, `LowDegree.lean`; `x := u`, `y := 1`,
  `z := 1` in `unitRep G.ρ.invariants`) computes `δ 1 = H1π ⟨u,_⟩`, giving
  `E = ± (c.comp SS.extClass)` where `c := eCoh 0 G (unitRep G) y₀` and `y₀ ∈ H⁰(G, unitRep G)`
  is the class of the constant-`1` cocycle.

**The remaining degree-zero obstacle.**  One needs `c.comp SS.extClass = ± SS.extClass`, i.e. that
the degree-zero isomorphism `eCoh 0 G (unitRep G)` is `mk₀ 𝟙` (up to sign).  Equivalently — via
`eCoh_map` (coefficient naturality) with `φ_a : unitRep G ⟶ modRep G A`, `1 ↦ a`:
`eCoh 0 G A a = c.comp (mk₀ φ_a)` — one needs `eCoh 0 G A a = mk₀ φ_a`.  By `eCoh_cocyclesMk`
(`n = 0`, `z` the constant-`a` cocycle, `Rep.freeLift … = R.π.f 0 ≫ φ_a` for `a ∈ A^G`) this is
the **bar-resolution degree-zero identity**

```
(R := Rep.barResolution Coeff G).extMk (R.π.f 0) 1 rfl (R.complex_d_comp_π_f_zero) = Ext.mk₀ 𝟙
```

(this statement *typechecks*, measured).  Mathlib provides for it: `Abelian.Ext.mk₀_bijective`,
`Abelian.Ext.homEquiv₀`, `ProjectiveResolution.extMk_comp_mk₀`, `ProjectiveResolution.mk₀_comp_extMk`
(which together show `mk₀ 𝟙` is a two-sided identity for `Ext.comp`), and
`Work.SSGRoute.extMk_deg_zero_eq_zero` (`R.extMk` *injective* in degree 0), so `R.extMk` is a
bijection `Hom(R.X 0, Y) ≃ Ext X Y 0`; but **no Mathlib lemma computes `extMk` in degree `0`**
(the only available handle is `ProjectiveResolution.extMk_hom`, which requires comparing the two
`ShiftedHom`s in `DerivedCategory`).  That comparison is the isolated remaining gap.

**Session measurement (correction to the `self X` reduction).**  The plan to reduce the
degree-zero identity to `ProjectiveResolution.self X` (whose `complex` is
`(ChainComplex.single₀ C).obj X`, with `π = 𝟙`) does **not** go through as literally stated,
because `((ChainComplex.single₀ C).obj X).X 0` is only *isomorphic*, not definitionally equal,
to `X` (`self`'s own `projective 0` field is closed by `simpa` for exactly this reason).
Measured: `rw [ProjectiveResolution.extMk_hom]` on the goal with `f := h : X ⟶ Y` fails with
"The argument `h` has type `X ⟶ Y` but is expected to have type
`(ProjectiveResolution.self X).complex.X 0 ⟶ Y`".  So the `self` case must carry
`h : (self X).complex.X 0 ⟶ Y` together with the degree-zero iso of `single₀`; the extra
`single₀`-bookkeeping is unavoidable but small.

Further measured API facts for the comparison (full names, since short ones do not resolve):
`CochainComplex.HomComplex.Cocycle.equivHomShift`, `CochainComplex.HomComplex.Cocycle.toSingleMk`
(`Cocycle.toSingleMk` alone is unknown), `HomologicalComplex.single_obj_d`
(`((single V c j).obj A).d k l = 0`), `HomologicalComplex.id_f` (`(𝟙 C).f i = 𝟙 (C.X i)`),
`ShiftedHom.mk₀_comp` / `ShiftedHom.comp_mk₀` / `ShiftedHom.mk₀_comp_mk₀`,
`DerivedCategory.singleFunctorIsoCompQ : singleFunctor C n ≅ singleFunctor C n ⋙ Q`,
`Abelian.Ext.homEquiv : Ext X Y n ≃ ShiftedHom (singleFunctor C 0).obj X (...).obj Y ↑n`.
`Abelian.Ext.ext` needs `[HasDerivedCategory C]` in scope
(`let := HasDerivedCategory.standard C`).

**Session measurement (the exact goal of the cancellation).**  The general sharp form is (no
`single₀` bookkeeping, unlike the `self X` form — the `hf` argument is
`by rw [← Category.assoc, R.complex_d_comp_π_f_zero, zero_comp]`):

```
R.extMk (R.π.f 0 ≫ g) 1 rfl _ = Abelian.Ext.mk₀ g            -- R : ProjectiveResolution X, g : X ⟶ Y
```

and after `let := HasDerivedCategory.standard C`, `apply Abelian.Ext.ext`,
`rw [ProjectiveResolution.extMk_hom, Abelian.Ext.mk₀_hom]` the goal is **exactly**
(measured by `trace_state`; `ι_X = (singleFunctorIsoCompQ C 0).hom.app X`,
`ι_Y = (singleFunctorIsoCompQ C 0).hom.app Y`):

```
(ShiftedHom.mk₀ 0 _ (ι_X ≫ inv (DerivedCategory.Q.map R.π'))).comp
    ((ShiftedHom.map
          (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
            (CochainComplex.HomComplex.Cocycle.toSingleMk
              ((R.cochainComplexXIso 0 0 _).hom ≫ R.π.f 0 ≫ g) _ (-1) _ _))
          DerivedCategory.Q).comp
      (ShiftedHom.mk₀ 0 _ (ι_Y⁻¹)) _) _ =
  ShiftedHom.mk₀ 0 _ ((DerivedCategory.singleFunctor C 0).map g)
```

The cancellation to perform: `ShiftedHom.mk₀_comp` on the outer `mk₀`, `ShiftedHom.comp_mk₀` on
the inner one (which introduces `(shiftFunctor C 0).map (ι_Y⁻¹)` — the `shiftFunctor C 0` versus
`𝟙` bookkeeping still to be absorbed), then identify the middle `ShiftedHom.map … Q` with
`Q ((CochainComplex.singleFunctor C 0).map g)`-precomposed by `Q R.π'` using
`ProjectiveResolution.π'_f_zero`
(`R.π'.f 0 = (R.cochainComplexXIso _ _).hom ≫ R.π.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv`)
and `ProjectiveResolution.Hom.hom'_comp_π'`
(`φ.hom' ≫ R'.π' = R.π' ≫ (CochainComplex.singleFunctor C 0).map f`), and finally cancel
`inv (Q R.π') ≫ Q R.π'` against the naturality square of
`DerivedCategory.singleFunctorIsoCompQ : singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q`.
The scratch file with this exact probe is `MyArchFound.lean` at the workspace root.

**Session measurement (the two `ShiftedHom` rewrites fire).**  In `MyArchFound2.lean` the moves
`rw [ShiftedHom.mk₀_comp]` (outer `mk₀`) and `rw [ShiftedHom.comp_mk₀]` (inner `mk₀`) both fired,
leaving exactly (measured by `trace_state`):

```
(ι_X ≫ inv (Q.map R.π')) ≫
    ShiftedHom.map
      (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.HomComplex.Cocycle.toSingleMk
          ((R.cochainComplexXIso 0 0 _).hom ≫ R.π.f 0 ≫ g) _ (-1) _ _))
      Q ≫
    (shiftFunctor (DerivedCategory C) (0 : ℤ)).map (ι_Y⁻¹)
  = ShiftedHom.mk₀ (0 : ℤ) _ ((DerivedCategory.singleFunctor C 0).map g)
```

So three things are now fixed: the outer/inner `mk₀`s are gone; the middle is a bare
`ShiftedHom.map … Q` (a `ShiftedHom` *in `CochainComplex C ℤ`* from `R.cochainComplex` to the
single complex at `-1`, transported by `Q`), which must be identified with
`Q (R.π' ≫ ((CochainComplex.singleFunctor C 0).map …))` using `π'_f_zero` +
`Hom.hom'_comp_π'` + `singleFunctorIsoCompQ` naturality; and the leftover
`(shiftFunctor (DerivedCategory C) (0 : ℤ)).map (ι_Y⁻¹)` has to be absorbed through
`shiftFunctorZero` before the `inv (Q R.π') ≫ Q R.π'` cancellation can be applied.  `#check`s
measured in the same run: `ShiftedHom.mk₀_comp_mk₀_assoc` exists;
`ShiftedHom.mk₀_comp_assoc`, `ShiftedHom.comp_mk₀_assoc`, `ShiftedHom.comp_hom`,
`CochainComplex.singleFunctor_map_f`, `CochainComplex.singleFunctor_obj_X`,
`DerivedCategory.singleFunctorIsoCompQ_hom_app`, `Cocycle.toSingleMk_cocycle` do **not**;
`HomologicalComplex.singleObjXIsoOfEq (c) (j) (A) (i) (h : i = j) : ((single V c j).obj A).X i ≅ A`
is the degree-`i` iso to use.

**The API that finishes the calculation** (`Mathlib/CategoryTheory/Shift/ShiftedHom.lean`, read):
`ShiftedHom X Y m` is *by definition* `X ⟶ Y⟦m⟧` (`abbrev`), so the printed goal is an equality of
honest morphisms `(singleFunctor C 0).obj X ⟶ ((singleFunctor C 0).obj Y)⟦0⟧` in
`DerivedCategory C`, and the three computation rules are

* `ShiftedHom.mk₀ m₀ hm₀ f = f ≫ (shiftFunctorZero' C m₀ hm₀).inv.app Y`
  — this is what expands the goal's right-hand side `mk₀ (0:ℤ) _ ((singleFunctor C 0).map g)`
  into `((singleFunctor C 0).map g) ≫ (shiftFunctorZero' (DerivedCategory C) 0 _).inv.app _`;
  the residual `(shiftFunctor (DerivedCategory C) (0:ℤ)).map (ι_Y⁻¹) = (ι_Y⁻¹)⟦0⟧'` on the left
  is exactly `(shiftFunctorZero' …).inv`'s role, so `shiftFunctorZero'`'s naturality
  (`shiftFunctorZero'_inv_app_naturality`-style) plus `ι_Y⁻¹ ≫ ι_Y = 𝟙` absorbs it — the
  `singleObjXIsoOfEq` bookkeeping is only needed to move `(single C (-1))` to `(single C 0)` in
  the middle term;
* `ShiftedHom.comp f g h = f ≫ g⟦a⟧' ≫ (shiftFunctorAdd' C b a c h).inv.app _`, which is why the
  two `rw`s in `MyArchFound2.lean` already collapsed the `mk₀`s to bare `≫`;
* `ShiftedHom.homEquiv (m₀) (hm₀) : (X ⟶ Y) ≃ ShiftedHom X Y m₀`, `simp`-normalised as
  `toFun = mk₀ m₀ hm₀`, `invFun g = g ≫ (shiftFunctorZero' C m₀ hm₀).hom.app Y` — the alternative
  finish, by cancelling the `shiftFunctorZero'` pair directly.

So the completion is: expand both `mk₀`s with their defining formula (`mk₀ f = f ≫ sl.inv.app Y`),
identify the middle `ShiftedHom.map … Q` with `Q R.π' ≫ Q ((CochainComplex.singleFunctor C 0).map g)`
via `π'_f_zero` + `Hom.hom'_comp_π'` + `singleFunctorIsoCompQ` naturality, cancel
`inv (Q R.π') ≫ Q R.π'`, and close the resulting square of `shiftFunctorZero'`/`singleFunctorIsoCompQ`
isos on `ι_Y⁻¹ ≫ ι_Y = 𝟙`.

**Session measurement (the `mk₀`-expanded goal, and the reading of the middle).**  In
`MyArchFound3.lean` the additional rewrite `rw [ShiftedHom.mk₀]` (i.e. unfolding
`mk₀ m₀ hm₀ f = f ≫ (shiftFunctorZero' C m₀ hm₀).inv.app Y`) fired, and the goal is now the
equality of honest morphisms in `DerivedCategory C`:

```
(ι_X ≫ inv (Q.map R.π')) ≫
    ShiftedHom.map (Cocycle.equivHomShift.symm …) Q ≫
    (shiftFunctor (DerivedCategory C) (0 : ℤ)).map (ι_Y⁻¹)
  = ((DerivedCategory.singleFunctor C 0).map g) ≫
    (shiftFunctorZero' (DerivedCategory C) (0 : ℤ) _).inv.app ((DerivedCategory.singleFunctor C 0).obj Y)
```

So the recipe's last line is confirmed verbatim: the two sides differ only by
`(shiftFunctorZero' …).inv` on the right against `(ι_Y⁻¹)⟦0⟧'` on the left, and
`shiftFunctorZero'`'s naturality turns `(shiftFunctorZero' …).inv.app (Q L) ≫ (ι_Y⁻¹)⟦0⟧'` into
`ι_Y⁻¹ ≫ (shiftFunctorZero' …).inv.app ((singleFunctor C 0).obj Y)`, after which `ι_Y⁻¹ ≫ ι_Y = 𝟙`
closes it.

Measured signatures (these fix the indexing of the middle):
`CochainComplex.HomComplex.Cocycle.equivHomShift :
  (K ⟶ L⟦n⟧) ≃+ CochainComplex.HomComplex.Cocycle K L n` (an `≃+` between *shifted homs of
cochain complexes* and cocycles), and
`Cocycle.toSingleMk (f : K.X p ⟶ X) {n} (h : p + n = q) (p' : ℤ) (hp' : p' + 1 = p)
  (h' : K.d p' p ≫ f = 0) : Cocycle K ((CochainComplex.singleFunctor C q).obj X) n`.
In the goal `f` is `(R.cochainComplexXIso 0 0 _).hom ≫ R.π.f 0 ≫ g`, `p' = -1` (so `p = 0`), and
the two remaining implicit indices are `n = q = 0` (forced by the type of the composition with
`(shiftFunctor … 0).map (ι_Y⁻¹)` whose source is `(Q ((CochainComplex.singleFunctor C 0).obj Y))`);
hence the middle is the degree-zero shifted hom `R.cochainComplex ⟶ ((CochainComplex.singleFunctor C 0).obj Y)⟦0⟧`
that `equivHomShift` sends to the cocycle `toSingleMk ((cochainComplexXIso _).hom ≫ R.π.f 0 ≫ g)`,
i.e. (via `π'_f_zero` and `CochainComplex.singleFunctor`'s component formula)
`R.π' ≫ ((CochainComplex.singleFunctor C 0).map g)` followed by `(shiftFunctorZero' …).inv`.
Also measured: `ShiftedHom.map_mk₀`, `ShiftedHom.map_comp`, `Cocycle.ofHom` exist;
`shiftFunctorZero'_inv_app`, `shiftFunctorZero'_hom_app`, `shiftFunctorZero'_inv_app_naturality`,
`DerivedCategory.Q_commShift` do **not** resolve under those names (use the `Iso`-projections and
`shiftFunctorZero'`'s naturality lemma as printed by `simp`).

**Session measurement (the two lemmas that perform the middle expansion).**  Both are in
`Mathlib/Algebra/Homology/HomotopyCategory/` and are exactly the expansion step:

* `Cocycle.toSingleMk_postcomp {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) (p' : ℤ)
   (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) {X' : C} (g : X ⟶ X') :
   toSingleMk (f ≫ g) h p' hp' (by simp [reassoc_of% hf]) =
     (toSingleMk f h p' hp' hf).postcomp ((singleFunctor C q).map g)`
  — this pulls `g` out of the cocycle;
* `Cocycle.equivHomShift_symm_postcomp (z : Cocycle K L n) {L'} (g : L ⟶ L') :
   equivHomShift.symm (z.postcomp g) = equivHomShift.symm z ≫ g⟦n⟧'`
  — this turns the `postcomp` into a `≫` on the shifted hom.

Since the goal's cocycle argument is left-associated, it is literally
`toSingleMk (f₁ ≫ g)` with `f₁ := (R.cochainComplexXIso 0 0 _).hom ≫ R.π.f 0`, so the two lemmas
give, verbatim,

```
MID = equivHomShift.symm (toSingleMk f₁ …) ≫ ((CochainComplex.singleFunctor C 0).map g)⟦0⟧'
```

leaving only `equivHomShift.symm (toSingleMk f₁ …)` to identify with `R.π'` (a degree-zero shifted
hom; use `Cocycle.ofHom` together with `π'_f_zero`, which rewrites
`f₁ = R.π'.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom`, then
`toSingleMk_postcomp` again to move that last factor back inside).  After that the goal is the
single cancellation `inv (Q R.π') ≫ Q R.π'` against the `singleFunctorIsoCompQ` naturality square,
with the `shiftFunctorZero'` square on `ι_Y⁻¹ ≫ ι_Y = 𝟙` as the last step.  Also measured:
`Cocycle.equivHomShift_comp_shift (f) (g) : equivHomShift (f ≫ g⟦n⟧') = Cocycle.postcomp (equivHomShift f) g`
(the companion of the second lemma), and `Cocycle.toSingleMk_precomp` for the source side.

**Session measurement (the expansion compiles, and the association correction).**  In
`MyArchFound6.lean` the following general form compiled (`lake env lean`, no error):

```
theorem toSingleMk_mul (C : Type) [Category C] [Preadditive C] [HasZeroObject C]
    {K : CochainComplex C ℤ} {X : C} {p q : ℤ} (f : K.X p ⟶ X) (n : ℤ) (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (Y : C) (g : X ⟶ Y)
    (hf' : K.d p' p ≫ (f ≫ g) = 0) :
    Cocycle.equivHomShift.symm (Cocycle.toSingleMk (f ≫ g) h p' hp' hf')
      = Cocycle.equivHomShift.symm (Cocycle.toSingleMk f h p' hp' hf)
        ≫ ((CochainComplex.singleFunctor C q).map g)⟦n⟧'
```

— proved by `Cocycle.ext` + `rfl` (i.e. `toSingleMk`'s value is independent of its `hf` proof
argument, `Cocycle.toSingleMk_coe`), then `Cocycle.toSingleMk_postcomp`,
`Cocycle.equivHomShift_symm_postcomp`.  **Note this general form is the one to use**: `rw` with the
`by simp [reassoc_of% hf]`-phrased version of the lemma does *not* fire, because the goal carries
its own proof term.

**Association correction (important for all subsequent rewrites).**  Applied to the real goal,
`rw [toSingleMk_mul]` matched with `f := (R.cochainComplexXIso 0 0 _).hom` and
`g := R.π.f 0 ≫ g`, i.e. **the goal's `toSingleMk` argument is right-associated**:
`(cochainComplexXIso 0 0 _).hom ≫ (R.π.f 0 ≫ g)`, *not* `((cochainComplexXIso 0 0 _).hom ≫ R.π.f 0) ≫ g`.
This is why every `rw` on an association pattern (`Category.assoc`/`← Category.assoc`, and
`rw [R.complex_d_comp_π_f_zero, zero_comp]` on `hf`) failed, and why the `MyArchFound*` probes report
*"was not found"* for both associations.  The expansion therefore produces, verbatim,

```
MID = equivHomShift.symm (Cocycle.toSingleMk (R.cochainComplexXIso 0 0 _).hom …)
        ≫ (shiftFunctor (CochainComplex C ℤ) 0).map ((CochainComplex.singleFunctor C 0).map (R.π.f 0 ≫ g))
```

so the next step is `Functor.map_comp` on `(CochainComplex.singleFunctor C 0).map (R.π.f 0 ≫ g)`
to split off the `g`-factor, and then the `R.π'` identification on the remaining factor
(`equivHomShift.symm (toSingleMk (cochainComplexXIso.hom) …) ≫ (singleFunctor C 0).map (R.π.f 0)`
against `Cocycle.ofHom R.π'`), for which the useful measured API is
`Cocycle.rightShift (n a n' : ℤ) (h : n + a = n') : Cocycle K L n → Cocycle K L⟦a⟧ n'`,
`Cocycle.homOf : Cocycle F G 0 → (F ⟶ G)`, and
`Cocycle.equivHomShift_symm_apply (a) : equivHomShift.symm a = (a.rightShift n 0 _).homOf`.
Names that do **not** exist: `Cocycle.homOf_rightShift`, `Cocycle.rightShift_ofHom`,
`Cocycle.rightShift_zero`, `shiftFunctorZero'_inv_app`, `Cocycle.toSingleMk_zero_le`.

**Session measurement (the cochain-level API for the `R.π'` step, and two corrections).**

*New, and the right level to work at* (`Mathlib/Algebra/Homology/HomotopyCategory/HomComplexSingle.lean`):

```
Cochain.toSingleEquiv (h : p + n = q) : Cochain K ((CochainComplex.singleFunctor C q).obj X) n ≃+ (K.X p ⟶ X)
Cochain.toSingleMk_postcomp (f : K.X p ⟶ X) (h : p + n = q) {X'} (g : X ⟶ X') :
    Cochain.toSingleMk (f ≫ g) h = (Cochain.toSingleMk f h).comp (Cochain.ofHom ((CochainComplex.singleFunctor C q).map g)) _
Cochain.ofHom : (F ⟶ G) → Cochain F G 0
```

`Cochain.toSingleEquiv` being an *additive iso* means the equality
`Cocycle.toSingleMk … = Cocycle.ofHom R.π'` (the `R.π'` identification) can be proved at the cochain
level by `Cochain.toSingleEquiv … .injective`, i.e. by comparing the underlying maps
`R.cochainComplex.X 0 ⟶ X` — which is exactly what `Cocycle.toSingleMk_coe`,
`Cocycle.ofHom_coe` and `ProjectiveResolution.π'_f_zero` supply.  This is the cleanest route: the
remaining `singleObjXSelf` bookkeeping is *inside* `toSingleEquiv`'s inverse rather than in the goal.

*Two corrections, measured:*

1. `simp only [Functor.map_comp]` does **not** split
   `(CochainComplex.singleFunctor C 0).map (R.π.f 0 ≫ g)` in the goal; use
   `(CochainComplex.singleFunctor C 0).map_comp` (or `Functor.map_comp` with the functor named
   explicitly) — the goal's occurrence is at `(shiftFunctor (CochainComplex C ℤ) 0).map (…)`, so a
   `rw [Functor.map_comp]`-style rewrite must be pointed at the inner `singleFunctor` application.
2. After `rw [toSingleMk_mul]` a *second* goal appears,
   `case hf : R.cochainComplex.d (-1) 0 ≫ (R.cochainComplexXIso 0 0 _).hom = 0` — the `hf`
   obligation of `toSingleMk`, left as a metavariable by `extMk_hom`'s elaboration (because
   `toSingleMk`'s value does not depend on it).  It is junk: `R.cochainComplex.IsStrictlyLE 0` holds
   (`instance` in `Abelian/Projective/Extend.lean`), so `R.cochainComplex.X (-1)` is a zero object
   and the map is `0` via `CochainComplex.isZero_of_isStrictlyLE R.cochainComplex 0 (-1) _` and
   `IsZero.eq_of_src`.  It must be discharged *before* the remaining rewrites, or the `trace_state`
   output will keep showing the unsolved `case hf` next to the main goal.

**Session correction (the `case hf` residue is NOT junk, and it exposes the wrong split).**  The
goal `R.cochainComplex.d (-1) 0 ≫ (R.cochainComplexXIso 0 0 _).hom = 0` is *not* closable by
`isZero_of_isStrictlyLE`: the cochain complex here is the ℤ-extension of `R.complex`, so
`R.cochainComplex.X (-1) = R.complex.X 1` (the index is negated, **not** truncated), and that
composite is `R.complex.d 1 0 ≠ 0`.  It is unprovable — which means the application of
`toSingleMk_mul` picked the **wrong split**.  Because the goal's `toSingleMk` argument is
right-associated, `(R.cochainComplexXIso 0 0 _).hom ≫ (R.π.f 0 ≫ g)`, the syntactic match forced
`f := (R.cochainComplexXIso 0 0 _).hom` and `g := R.π.f 0 ≫ g`, and `toSingleMk` of *that* `f`
requires the false condition `R.cochainComplex.d (-1) 0 ≫ (R.cochainComplexXIso 0 0 _).hom = 0`.

The correct split is `f₁ := (R.cochainComplexXIso 0 0 _).hom ≫ R.π.f 0`, for which
`R.cochainComplex.d (-1) 0 ≫ ((R.cochainComplexXIso 0 0 _).hom ≫ R.π.f 0) = R.complex.d 1 0 ≫ R.π.f 0 = 0`
*does* hold (`R.complex_d_comp_π_f_zero`) — every index of the ℤ-extension is the negation of the
ℕ-index, so `d (-1) 0` of the cochain complex is `d 1 0` of `R.complex`.  Hence the fix is: first
**reassociate the `toSingleMk` argument** from `a ≫ (b ≫ c)` to `(a ≫ b) ≫ c`
(`rw [← Category.assoc]`, or `conv`/`rw` at that occurrence — note this is a genuine, non-rfl
reassociation in a general category), and *then* apply `toSingleMk_mul`.  With that split the
expansion gives precisely the two factors the cancellation needs:
`equivHomShift.symm (toSingleMk f₁ …)` (the `R.π'`-cocycle, to be identified via
`Cochain.toSingleEquiv.injective` + `Cocycle.ofHom` + `ProjectiveResolution.π'_f_zero`) and
`(CochainComplex.singleFunctor C 0).map g` (which pairs with `inv (Q R.π')`).  `toSingleMk_mul`
itself stays as banked — it is applied to the *correct* `f`, and its `hf` hypothesis is then a
theorem rather than an unprovable obligation.

**Session measurement (association vs. rewriting: the shape the reassociation must take).**  Trying
to discharge the corrected `hf`, `R.cochainComplex.d (-1) 0 ≫ ((R.cochainComplexXIso 0 0 _).hom ≫ R.π.f 0) = 0`,
runs into the same wall as before in a new place: the differential-compatibility lemma
`ProjectiveResolution.cochainComplex_d R i j n m h1 h2` (used inside `delta_toSingleMk_eq`) rewrites
the *left-associated* pattern `R.cochainComplex.d i j ≫ (cochainComplexXIso i n h1).hom`, whereas the
goal's term is right-associated, `d ≫ (a ≫ b)`.  Since `≫` is only *propositionally* associative in
a general category, no `rw` on a `d ≫ iso` pattern fires until the term is reassociated.  So the
reassociation must be performed **twice, at two places**:
* inside the `toSingleMk` argument (to make the split `f₁ ≫ g` visible at all), and
* inside the `hf` obligation (`K.d p' p ≫ (f₁ ≫ g)`, resp. `K.d p' p ≫ f₁`), before
  `ProjectiveResolution.cochainComplex_d` and `R.complex_d_comp_π_f_zero` can fire.

Concretely: `(Category.assoc a b c).symm : a ≫ (b ≫ c) = (a ≫ b) ≫ c` is the equality to `rw` by; for
the `toSingleMk` argument it can be applied with `conv`/`rw` at that occurrence, and the accompanying
`hf` proof then has to be re-elaborated at the reassociated type (which is why the *right-associated*
form of the expansion lemma — an `toSingleMk_mul` variant taking `a b c` with hypotheses
`K.d p' p ≫ (a ≫ b) = 0` and `K.d p' p ≫ (a ≫ (b ≫ c)) = 0` — is the version to state: its proof is
`Cocycle.ext` + `congrArg (fun t => Cochain.toSingleMk t h) (Category.assoc a b c).symm`, and then
`toSingleMk_mul`).  Recommended statement of that variant (proved in one step from the banked
`toSingleMk_mul`):

```
theorem toSingleMk_mul_right (C : Type) [Category C] [Preadditive C] [HasZeroObject C]
    {K : CochainComplex C ℤ} {X X' X'' : C} {p q : ℤ} (a : K.X p ⟶ X) (b : X ⟶ X') (c : X' ⟶ X'')
    (n : ℤ) (h : p + n = q) (p' : ℤ) (hp' : p' + 1 = p)
    (hf : K.d p' p ≫ (a ≫ b) = 0) (hf'' : K.d p' p ≫ (a ≫ (b ≫ c)) = 0) :
    Cocycle.equivHomShift.symm (Cocycle.toSingleMk (a ≫ (b ≫ c)) h p' hp' hf'')
      = Cocycle.equivHomShift.symm (Cocycle.toSingleMk (a ≫ b) h p' hp' hf)
        ≫ ((CochainComplex.singleFunctor C q).map c)⟦n⟧'
```

Applied with `a := (R.cochainComplexXIso 0 0 _).hom`, `b := R.π.f 0`, `c := g`, its `hf`
(a *hypothesis*, so `rw` leaves it as a goal) is then provable — after the second reassociation —
by `ProjectiveResolution.cochainComplex_d` followed by `R.complex_d_comp_π_f_zero`, and its
conclusion has exactly the two factors the cancellation needs.

**Session measurement (`toSingleMk_mul_right` is proved, up to one argument; and the exact `hf`
discharge).**

* The `h1` step of the proposed proof of `toSingleMk_mul_right` **goes through**:
  `Cocycle.ext` + `congrArg (fun t => Cochain.toSingleMk t h) (Category.assoc a b c).symm` closed the
  proof-irrelevance step (measured; the residual error was only in the *call* to the banked lemma:
  its explicit binder order is `(C) (f) (n) (h) (p') (hp') (hf) (Y) (g) (hf')`, so the call must
  read `toSingleMk_mul C (a ≫ b) n h p' hp' hf X'' c (by rw [Category.assoc]; exact hf'')` — the
  intermediate object `Y = X''` is an explicit argument and was missing).
* The `hf` discharge has its exact recipe: measured,
  `ProjectiveResolution.cochainComplex_d R n₁ n₂ k₁ k₂ :
     R.cochainComplex.d n₁ n₂ = (R.cochainComplexXIso n₁ k₁ _).hom ≫ R.complex.d k₁ k₂ ≫ (R.cochainComplexXIso n₂ k₂ _).inv`
  so `R.cochainComplex.d (-1) 0` unfolds to `iso₁.hom ≫ R.complex.d 1 0 ≫ iso₀.inv`, and the goal
  `… ≫ (iso₀.hom ≫ R.π.f 0) = 0` collapses by `Iso.inv_hom_id`
  (`iso₀.inv ≫ iso₀.hom = 𝟙`) and then `R.complex_d_comp_π_f_zero`.  Note the rewrite must be done
  with the *statement* of `cochainComplex_d` oriented at `d n₁ n₂`, i.e. rewriting the differential
  first (`rw [ProjectiveResolution.cochainComplex_d R (-1) 0 1 0]`), not by matching a `d ≫ iso`
  pattern.
* **Residual trap, measured**: even the *statement's* `hf`
  `R.complex.d 1 0 ≫ R.π.f 0 ≫ g = 0` resists both `Category.assoc` orientations **and**
  `rw [R.complex_d_comp_π_f_zero]` and `simp [reassoc_of% R.complex_d_comp_π_f_zero]` (the latter
  reports the simp argument as unused).  The association is therefore neither plainly left nor
  plainly right in the way the patterns expect.  Use
  `by simp only [Category.assoc, R.complex_d_comp_π_f_zero, zero_comp]` (normalise associativity
  first, *then* rewrite) — or take `hf` as an explicit hypothesis of the example and build it that
  way.  This matters for every call site that must supply this proof.

**Session result: `toSingleMk_mul_right` COMPILES, and the `hf` discharge works.**  In
`MyArchFound9.lean` (run under `lake env lean`) both of the following were established:

1. **The right-associated expansion is proved** (no error reported on its declaration):

```
theorem toSingleMk_mul_right (C : Type) [Category C] [Preadditive C] [HasZeroObject C]
    {K : CochainComplex C ℤ} {X X' X'' : C} {p q : ℤ} (a : K.X p ⟶ X) (b : X ⟶ X')
    (c : X' ⟶ X'') (n : ℤ) (h : p + n = q) (p' : ℤ) (hp' : p' + 1 = p)
    (hf : K.d p' p ≫ (a ≫ b) = 0) (hf'' : K.d p' p ≫ (a ≫ (b ≫ c)) = 0) :
    Cocycle.equivHomShift.symm (Cocycle.toSingleMk (a ≫ (b ≫ c)) h p' hp' hf'')
      = Cocycle.equivHomShift.symm (Cocycle.toSingleMk (a ≫ b) h p' hp' hf)
        ≫ ((CochainComplex.singleFunctor C q).map c)⟦n⟧' := by
  have h1 : Cocycle.toSingleMk (a ≫ (b ≫ c)) h p' hp' hf''
      = Cocycle.toSingleMk ((a ≫ b) ≫ c) h p' hp' (by rw [Category.assoc]; exact hf'') := by
    apply Cocycle.ext
    exact congrArg (fun t => Cochain.toSingleMk t h) (Category.assoc a b c).symm
  rw [h1, toSingleMk_mul C (a ≫ b) n h p' hp' hf X'' c (by rw [Category.assoc]; exact hf'')]
```

   (together with the banked `toSingleMk_mul` it depends on).  This is *the* lemma the degree-zero
   identity needs: its syntactic shape is the goal's, and it splits the middle into
   `equivHomShift.symm (toSingleMk ((cochainComplexXIso).hom ≫ R.π.f 0) …)` (the `R.π'`-cocycle) and
   `(CochainComplex.singleFunctor C 0).map g` (the factor pairing with `inv (Q R.π')`), applied with
   `a := (R.cochainComplexXIso 0 0 _).hom`, `b := R.π.f 0`, `c := g`.

2. **The `hf` obligation closes**, with *one* micro-correction: the final step needs
   `Category.comp_zero` (`f ≫ 0 = 0`), **not** `zero_comp` (`0 ≫ f = 0`) — after
   `rw [ProjectiveResolution.cochainComplex_d R (-1) 0 1 0]` the residual goal is
   `(R.cochainComplexXIso (-1) 1 _).hom ≫ 0 = 0`.  Full working proof (measured; the unused-arg
   warnings are harmless):

```
have hf1 : R.cochainComplex.d (-1) 0 ≫ ((R.cochainComplexXIso 0 0 rfl).hom ≫ R.π.f 0) = 0 := by
  rw [ProjectiveResolution.cochainComplex_d R (-1) 0 1 0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.id_comp,
    R.complex_d_comp_π_f_zero, zero_comp, Category.comp_zero]
```

   so `Iso.inv_hom_id_assoc` (`e.inv ≫ e.hom ≫ f = f`) is the lemma that cancels the
   `cochainComplexXIso 0 0`-pair, and the call site should pass `hf := hf1` explicitly
   (`rw [toSingleMk_mul_right (hf := hf1)]`) so no `hf` goal is created.

**Remaining trap at the statement level.**  The obligations of the form
`R.complex.d 1 0 ≫ R.π.f 0 ≫ g = 0` (the `hf` argument of `extMk` in the *statement*) still resist
`simp only [Category.assoc, R.complex_d_comp_π_f_zero, zero_comp]` ("`simp` made no progress"), and
they are only needed to *type* the `extMk` term.  **Recommendation**: state the degree-zero identity
with `hf` as an explicit hypothesis
(`(hf : R.complex.d 1 0 ≫ (R.π.f 0 ≫ g) = 0) : R.extMk (R.π.f 0 ≫ g) 1 rfl hf = Abelian.Ext.mk₀ g`)
and discharge `extMk`'s proof-irrelevance in `hf` (`E0bCore.extMk_congr` /
`ProjectiveResolution.extMk_comp_mk₀`-style) at the call site, rather than trying to build that proof
term inline.
-/
end Work.SSGRoute.PT
