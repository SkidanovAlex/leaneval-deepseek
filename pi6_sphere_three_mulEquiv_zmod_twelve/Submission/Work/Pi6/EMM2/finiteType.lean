import Mathlib
import Submission.Work.Pi6.EMM2.Defs
import Submission.Work.EMFG.emHomologyFG
import Submission.Work.SSS.serreFGThreeForTwo
import Submission.Work.SSS.singularCoeffFG
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Cohomology.kronH_bijective_field
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-!
# Finite type of the cohomology of an Eilenberg–MacLane range model

For `X` a range model of `K(A,m)` through degree `N + 1` with `A` finitely generated, the integral
homology `H_i(X;ℤ)` is finitely generated for `i ≤ N` (`Work.EMFG.emHomologyFG`, proved from
Serre's three-for-two theorem).  This file deduces that the mod-`𝕜` cohomology `Hⁿ(X;𝕜)` is finite
dimensional over any field `𝕜`, for `n ≤ N`.

The two ingredients are

* *finiteness of `H_n(X;𝕜)`*.  If `𝕜` has characteristic zero, `ℤ → 𝕜` is flat and
  `H_n(X;𝕜) ≅ H_n(X;ℤ) ⊗[ℤ] 𝕜` is finitely generated; if `𝕜` has characteristic `p`, then
  `H_n(X;𝔽_p)` is finitely generated as a `ℤ`-module (`Work.SSS.singularCoeffFG`, the universal
  coefficient theorem in finiteness form) and the flat base change `𝔽_p → 𝕜` finishes.
* *duality*: over a field the universal coefficient theorem `Hⁿ(X;𝕜) ≅ Hom_𝕜(H_n(X;𝕜), 𝕜)`
  (`Work.StemsB.fieldDualUCT`, or equivalently the Kronecker pairing
  `Work.Cohomology.kronH_bijective_field`) is an isomorphism, so the `𝕜`-dual of a finitely
  generated module is finitely generated, hence finite dimensional.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Work.Pi6.EMM2

noncomputable section

/-! ## 1. Flat base change for the singular chain complex

For a flat ring homomorphism `f : R →+* S` the singular chain complex with coefficients in `S` is the
extension of scalars of the one with coefficients in `R`, and (the functor being exact) the same
holds for homology.  This is `Work.Serre.OneCell.ratHomologyBaseChange` for an arbitrary flat `f`. -/

/-- **The extension of scalars of the free module of rank one.**  The `R`-module
`(extendScalars f).obj R` is `S ⊗[R] R`, and the multiplication map `s ⊗ r ↦ s * r` is an
`S`-linear isomorphism onto `S`. -/
noncomputable def extendScalarsSelfIso {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{0,0,0} f).obj (ModuleCat.of R R) ≅ ModuleCat.of S S := by
  letI : Algebra R S := f.toAlgebra
  have h : (S ⊗[R] R) ≃ₗ[S] S :=
  { toFun := fun x => TensorProduct.rid R S x
    map_add' := fun x y => map_add (TensorProduct.rid R S) x y
    map_smul' := by
      intro q x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a z =>
          show TensorProduct.rid R S (q • (a ⊗ₜ[R] z)) = q • TensorProduct.rid R S (a ⊗ₜ[R] z)
          rw [TensorProduct.smul_tmul', TensorProduct.rid_tmul, TensorProduct.rid_tmul]
          simp only [Algebra.smul_def]
          ring
      | add x y hx hy => simp only [smul_add, map_add, hx, hy, smul_add]
    invFun := fun q => q ⊗ₜ[R] (1 : R)
    left_inv := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a z =>
          show (TensorProduct.rid R S (a ⊗ₜ[R] z)) ⊗ₜ[R] (1 : R) = a ⊗ₜ[R] z
          rw [TensorProduct.rid_tmul]
          rw [← TensorProduct.smul_tmul' (R := R) (R' := R) z a (1 : R),
            ← TensorProduct.tmul_smul (R := R) (R' := R) z a (1 : R)]
          congr 1
          simp [Algebra.smul_def]
      | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
    right_inv := by
      intro q
      show TensorProduct.rid R S (q ⊗ₜ[R] (1 : R)) = q
      rw [TensorProduct.rid_tmul]
      simp [Algebra.smul_def] }
  exact LinearEquiv.toModuleIso h

/-- **Flat base change for singular homology.**  For a flat ring homomorphism `f : R →+* S` the
singular homology of a space with coefficients in `S` is the extension of scalars of the singular
homology with coefficients in `R`. -/
theorem singularChains_extendScalars_iso {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : f.Flat) (Y : TopCat) (q : ℕ) :
    Nonempty ((Work.Cohomology.singularChains S Y).homology q ≅
      (ModuleCat.extendScalars f).obj ((Work.Cohomology.singularChains R Y).homology q)) := by
  let F : ModuleCat R ⥤ ModuleCat S := ModuleCat.extendScalars f
  haveI hfl : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  haveI hfc : PreservesFiniteColimits F := inferInstance
  haveI hph : F.PreservesHomology := inferInstance
  haveI hcop : ∀ (T : Type), PreservesColimitsOfShape (Discrete T) F := fun _ => inferInstance
  let X : SSet := TopCat.toSSet.obj Y
  let K : ChainComplex (ModuleCat R) ℕ := Work.Cohomology.singularChains R Y
  have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅
      Work.Cohomology.singularChains S Y :=
    Work.StemsB.SphRat.chainComplexBaseChange F X (ModuleCat.of R R) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso X (extendScalarsSelfIso f)
  exact ⟨(HomologicalComplex.homologyMapIso hΦ q).symm ≪≫
    (Work.StemsB.SphRat.homologyMapBaseChange F K q).some⟩

/-- **Finite generation is preserved by extension of scalars.**  If `M` is generated over `R` by
finitely many elements, then `S ⊗[R] M` is generated over `S` by their images `1 ⊗ m`. -/
theorem moduleFinite_extendScalars {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat R) (h : Module.Finite R M) :
    Module.Finite S ((ModuleCat.extendScalars f).obj M) := by
  letI : Algebra R S := f.toAlgebra
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp h.fg_top
  refine Module.Finite.of_fg_top
    (Submodule.fg_def.mpr ⟨(fun m : ↥M => (1 : S) ⊗ₜ[R] m) '' s, hsfin.image _, ?_⟩)
  rw [Submodule.eq_top_iff']
  intro x
  have key : ∀ m : ↥M, m ∈ Submodule.span R s → ∀ a : S, a ⊗ₜ[R] m ∈
      Submodule.span S ((fun m : ↥M => (1 : S) ⊗ₜ[R] m) '' s) := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem z hz =>
        intro a
        have hz' : (1 : S) ⊗ₜ[R] z ∈
            Submodule.span S ((fun m : ↥M => (1 : S) ⊗ₜ[R] m) '' s) :=
          Submodule.subset_span ⟨z, hz, rfl⟩
        have h1 : a ⊗ₜ[R] z = a • ((1 : S) ⊗ₜ[R] z) := by
          rw [TensorProduct.smul_tmul']
          simp
        rw [h1]
        exact Submodule.smul_mem _ a hz'
    | zero => intro a; simp
    | add u v hu hv ihu ihv =>
        intro a
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ (ihu a) (ihv a)
    | smul r z hz ihz =>
        intro a
        have h2 : a ⊗ₜ[R] (r • z) = (algebraMap R S r * a) ⊗ₜ[R] z := by
          rw [← TensorProduct.smul_tmul (R := R) (R' := R) r a z, Algebra.smul_def]
        rw [h2]
        exact ihz _
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a m => exact key m (by rw [hs]; trivial) a
  | add u v ihu ihv => exact Submodule.add_mem _ ihu ihv

/-! ## 2. Restriction of scalars and the `ℤ`-module structure

The singular chain complex with coefficients in `𝔽_p`, viewed as a complex of `ℤ`-modules by
restriction of scalars, is the complex of `ℤ`-modules with coefficients in the abelian group `𝔽_p`. -/

/-- The coefficient object of `ModuleCat.restrictScalars (Int.castRingHom 𝕜)` at `𝕜` is the
canonical `ℤ`-module `𝕜`: every `ℤ`-module structure on a fixed additive group is the canonical
one, so the underlying map of the isomorphism is the identity. -/
noncomputable def restrictScalarsObjIntIso (𝕜 : Type) [Field 𝕜] :
    (ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj (ModuleCat.of 𝕜 𝕜) ≅
      ModuleCat.of ℤ 𝕜 :=
  LinearEquiv.toModuleIso <|
    @AddEquiv.toLinearEquiv _ _ _ _ _ _
      (((ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj (ModuleCat.of 𝕜 𝕜)).isModule) _
      (by rfl) (fun r x => by
        show ((r : 𝕜) • x : 𝕜) = r • x
        exact Int.cast_smul_eq_zsmul 𝕜 r x)

/-- **Restriction of scalars for singular homology.**  The singular chain complex of a simplicial
set with coefficients in `𝕜`, viewed as a complex of `ℤ`-modules by restriction of scalars along
`ℤ → 𝕜`, has the homology of the complex of `ℤ`-modules with coefficients in `𝕜`. -/
theorem hzCoeffRestrictScalarsIso (𝕜 : Type) [Field 𝕜] (X : Type) [TopologicalSpace X] (q : ℕ) :
    Nonempty (Work.SSS.HZCoeff X (ModuleCat.of ℤ 𝕜) q ≅
      (ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj
        ((Work.Cohomology.singularChains 𝕜 (TopCat.of X)).homology q)) := by
  let F : ModuleCat 𝕜 ⥤ ModuleCat ℤ := ModuleCat.restrictScalars (Int.castRingHom 𝕜)
  haveI h1 : ∀ (S : Type), PreservesColimitsOfShape (Discrete S) F := fun _ => inferInstance
  haveI h2 : F.Additive := inferInstance
  haveI h3 : F.PreservesHomology := inferInstance
  let S : SSet := TopCat.toSSet.obj (TopCat.of X)
  let K : ChainComplex (ModuleCat 𝕜) ℕ := S.chainComplex (ModuleCat.of 𝕜 𝕜)
  have cb : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅
      S.chainComplex (F.obj (ModuleCat.of 𝕜 𝕜)) :=
    Work.StemsB.SphRat.chainComplexBaseChange F S (ModuleCat.of 𝕜 𝕜)
  have cc : S.chainComplex (F.obj (ModuleCat.of 𝕜 𝕜)) ≅ S.chainComplex (ModuleCat.of ℤ 𝕜) :=
    Work.StemsB.SphRat.chainComplexCoeffIso S (restrictScalarsObjIntIso 𝕜)
  have hmi : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology q ≅
      F.obj (K.homology q) :=
    (Work.StemsB.SphRat.homologyMapBaseChange F K q).some
  exact ⟨(HomologicalComplex.homologyMapIso (cc.symm ≪≫ cb.symm) q) ≪≫ hmi⟩

/-- **A finitely generated abelian group carrying a `𝕜`-module structure is a finitely generated
`𝕜`-module.**  A generating set over `ℤ` generates over `𝕜`, because every `ℤ`-multiple of an
element is the corresponding `𝕜`-multiple. -/
theorem moduleFinite_of_restrictScalars (𝕜 : Type) [Field 𝕜] (N : ModuleCat 𝕜)
    (h : Module.Finite ℤ ↥((ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj N)) :
    Module.Finite 𝕜 ↥N := by
  have hmod : ((ModuleCat.restrictScalars (Int.castRingHom 𝕜)).obj N).isModule
      = AddCommGroup.toIntModule ↥N := Subsingleton.elim _ _
  rw [hmod] at h
  have hfg : (⊤ : Submodule ℤ ↥N).FG := h.fg_top
  rw [Submodule.fg_def] at hfg
  obtain ⟨s, hsfin, hs⟩ := hfg
  have key : ∀ y : ↥N, y ∈ Submodule.span ℤ s → y ∈ Submodule.span 𝕜 s := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul z a _ ha =>
        show z • a ∈ Submodule.span 𝕜 s
        rw [(Int.cast_smul_eq_zsmul 𝕜 z a).symm]
        exact Submodule.smul_mem _ _ ha
  refine Module.Finite.of_fg_top (Submodule.fg_def.mpr ⟨s, hsfin, ?_⟩)
  apply le_antisymm le_top
  intro x _
  exact key x (by rw [hs]; trivial)

/-! ## 3. Finiteness of `H_*(X;𝕜)` -/

/-- **Finitely generated integral homology in a range gives finite dimensional mod-`𝕜` homology in
that range.** -/
theorem moduleFinite_singularHomology (𝕜 : Type) [Field 𝕜] (X : Type) [TopologicalSpace X]
    (N : ℕ) (h : ∀ i : ℕ, i ≤ N → Module.Finite ℤ (Work.PiS.HZ X i)) :
    ∀ q : ℕ, q ≤ N → Module.Finite 𝕜
      ((Work.Cohomology.singularChains 𝕜 (TopCat.of X)).homology q) := by
  intro q hq
  rcases CharP.exists' 𝕜 with h0 | ⟨p, hpprime, hchar⟩
  · -- characteristic zero
    haveI : CharZero 𝕜 := h0
    have hflat : (Int.castRingHom 𝕜).Flat := by
      have h1 : (Int.castRingHom ℚ).Flat := by rw [RingHom.Flat]; infer_instance
      have h2 : (algebraMap ℚ 𝕜).Flat := by rw [RingHom.Flat]; infer_instance
      have h3 : ((algebraMap ℚ 𝕜).comp (Int.castRingHom ℚ)).Flat := h1.comp h2
      rwa [show (algebraMap ℚ 𝕜).comp (Int.castRingHom ℚ) = Int.castRingHom 𝕜 from
        RingHom.ext (by intro n; simp)] at h3
    obtain ⟨e⟩ := singularChains_extendScalars_iso (Int.castRingHom 𝕜) hflat (TopCat.of X) q
    haveI : Module.Finite ℤ (Work.PiS.HZ X q) := h q hq
    haveI : Module.Finite 𝕜
        ((ModuleCat.extendScalars (Int.castRingHom 𝕜)).obj (Work.PiS.HZ X q)) :=
      moduleFinite_extendScalars (Int.castRingHom 𝕜) (Work.PiS.HZ X q) inferInstance
    exact Module.Finite.equiv (Iso.toLinearEquiv e).symm
  · -- characteristic `p`
    obtain ⟨hpp⟩ := hpprime
    letI : Fact p.Prime := ⟨hpp⟩
    haveI : CharP 𝕜 p := hchar
    have hZ : Module.Finite ℤ (Work.SSS.HZCoeff X (ModuleCat.of ℤ (ZMod p)) q) :=
      Work.SSS.singularCoeffFG (ModuleCat.of ℤ (ZMod p)) q (h q hq) (h (q - 1) (by omega))
        (inferInstance : Module.Finite ℤ (ZMod p))
    obtain ⟨eZ⟩ := hzCoeffRestrictScalarsIso (ZMod p) X q
    have hZ' : Module.Finite ℤ ((ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj
        ((Work.Cohomology.singularChains (ZMod p) (TopCat.of X)).homology q)) :=
      Module.Finite.equiv (Iso.toLinearEquiv eZ)
    haveI : Module.Finite (ZMod p)
        ((Work.Cohomology.singularChains (ZMod p) (TopCat.of X)).homology q) :=
      moduleFinite_of_restrictScalars (ZMod p) _ hZ'
    have hflat : (ZMod.castHom (dvd_refl p) 𝕜).Flat := by
      rw [RingHom.Flat]
      infer_instance
    obtain ⟨e⟩ := singularChains_extendScalars_iso (ZMod.castHom (dvd_refl p) 𝕜) hflat
      (TopCat.of X) q
    haveI : Module.Finite 𝕜 ((ModuleCat.extendScalars (ZMod.castHom (dvd_refl p) 𝕜)).obj
        ((Work.Cohomology.singularChains (ZMod p) (TopCat.of X)).homology q)) :=
      moduleFinite_extendScalars (ZMod.castHom (dvd_refl p) 𝕜) _ inferInstance
    exact Module.Finite.equiv (Iso.toLinearEquiv e).symm

/-! ## 4. The target -/

theorem finiteType (𝕜 : Type) [Field 𝕜] {A : Type} [AddCommGroup A] (hA : Module.Finite ℤ A)
    {m N : ℕ} (hm : 2 ≤ m) {X : Type} [TopologicalSpace X] (x : X)
    (hX : Work.Serre.IsEMSpaceUpTo A m (by omega) (N + 1) X x) :
    ∀ n : ℕ, n ≤ N → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 X n) := by
  haveI : Module.Finite ℤ A := hA
  have hFG : Work.PiS.EMHomologyFG := Work.EMFG.emHomologyFG Work.SSS.serreFGThreeForTwo
  have hfg : ∀ i : ℕ, i ≤ N → Module.Finite ℤ (Work.PiS.HZ X i) := hFG A m hm N X x hX
  intro n hn
  have hfin : Module.Finite 𝕜
      ((Work.Cohomology.singularChains 𝕜 (TopCat.of X)).homology n) :=
    moduleFinite_singularHomology 𝕜 X N hfg n hn
  obtain ⟨e⟩ := Work.StemsB.fieldDualUCT 𝕜
    (Work.Cohomology.singularChains 𝕜 (TopCat.of X)) n
  haveI := hfin
  exact Module.Finite.equiv (Iso.toLinearEquiv e).symm

end

end Work.Pi6.EMM2
