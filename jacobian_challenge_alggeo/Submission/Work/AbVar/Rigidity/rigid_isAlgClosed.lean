import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.Rigidity.range_sectionLeft

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AlgebraicGeometry
open scoped MonObj

namespace Work.AbVar.Rigidity

lemma rigid_aux_subsingleton_point_left {k : Type*} [Field k] :
    Subsingleton ↥(Over.left (𝟙_ (Work.AbVar.Sch k))) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

lemma rigid_aux_range_left_point {k : Type*} [Field k] {Y : Work.AbVar.Sch k}
    (y : Work.AbVar.Point Y) :
    Set.range y.left = {y.left (IsLocalRing.closedPoint k)} := by
  haveI := rigid_aux_subsingleton_point_left (k := k)
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact congrArg y.left (Subsingleton.elim a (IsLocalRing.closedPoint k))
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint k, rfl⟩

/-- the two graph sections agree at a `k`-point -/
lemma rigid_aux_sectionLeft_sectionRight {k : Type*} [Field k] {X Y : Work.AbVar.Sch k}
    (x0 : Work.AbVar.Point X) (y : Work.AbVar.Point Y) :
    x0 ≫ Work.AbVar.sectionLeft X Y y = y ≫ Work.AbVar.sectionRight X Y x0 := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left]
  refine Over.tensorObj_ext _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, ← Over.fst_left,
      ← Over.comp_left, Work.AbVar.sectionLeft_fst, Over.id_left,
      ← Over.comp_left, Work.AbVar.sectionRight_fst, Over.comp_left, Over.toUnit_left,
      ← Category.assoc, Over.w y, Over.tensorUnit_hom]
    simp
  · rw [Category.assoc, Category.assoc, ← Over.snd_left,
      ← Over.comp_left, Work.AbVar.sectionLeft_snd, Over.comp_left, Over.toUnit_left,
      ← Over.comp_left, Work.AbVar.sectionRight_snd, Over.id_left,
      ← Category.assoc, Over.w x0, Over.tensorUnit_hom]
    simp

/-- `sectionRight x₀` lands in the fibre of `snd X Y` over its second argument. -/
lemma rigid_aux_snd_left_sectionRight_apply {k : Type*} [Field k] {X Y : Work.AbVar.Sch k}
    (x0 : Work.AbVar.Point X) (z : Y.left) :
    (SemiCartesianMonoidalCategory.snd X Y).left
      ((Work.AbVar.sectionRight X Y x0).left z) = z := by
  have hs : (Work.AbVar.sectionRight X Y x0).left ≫
      (SemiCartesianMonoidalCategory.snd X Y).left = 𝟙 Y.left := by
    rw [← Over.comp_left, Work.AbVar.sectionRight_snd]
    exact Over.id_left Y
  simpa using congr($hs z)

/-- **Affine-target constancy.** A morphism from an integral scheme `V` which is universally
closed over `Spec τ` and which admits a section `v` of `π` is constant. -/
lemma rigid_aux_const_affine {τ : Type*} [Field τ] {V W : Scheme} [IsAffine W]
    (π : V ⟶ Spec (CommRingCat.of τ)) [IsIntegral V] [UniversallyClosed π]
    (v : Spec (CommRingCat.of τ) ⟶ V) (hv : v ≫ π = 𝟙 _)
    (σ : V ⟶ W) : σ = π ≫ (v ≫ σ) := by
  -- From `v ≫ π = 𝟙` we get `π♯ ≫ v♯ = 𝟙`; since `Γ(V,⊤)` is a field, `v♯` is injective and
  -- hence `v♯ ≫ π♯ = 𝟙` as well.
  have hknown : π.appTop ≫ v.appTop = 𝟙 Γ(Spec (CommRingCat.of τ), ⊤) := by
    have h := congrArg Scheme.Hom.appTop hv
    simpa only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] using h
  have hcomp : v.appTop ≫ π.appTop = 𝟙 Γ(V, ⊤) := by
    have hfield : IsField Γ(V, ⊤) := isField_of_universallyClosed τ π
    have hinj : Function.Injective (v.appTop.hom) := by
      letI := hfield.toField
      exact RingHom.injective v.appTop.hom
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    refine hinj ?_
    have hx := congr($hknown (v.appTop.hom x))
    simpa using hx
  -- Comparing the two morphisms on global sections
  have hkey : Scheme.Hom.appTop (π ≫ (v ≫ σ)) = Scheme.Hom.appTop σ := by
    simp only [Scheme.Hom.comp_appTop]
    rw [Category.assoc, hcomp, Category.comp_id]
  refine (cancel_mono W.toSpecΓ).mp ?_
  rw [Scheme.toSpecΓ_naturality σ, Scheme.toSpecΓ_naturality (π ≫ (v ≫ σ)), hkey]

/-- A morphism into an affine open subscheme of `Z` is constant. -/
lemma rigid_aux_const_of_range_subset_affineOpen {k : Type*} [Field k]
    {X Z : Work.AbVar.Sch k} [AlgebraicGeometry.IsProper X.hom]
    [AlgebraicGeometry.GeometricallyIntegral X.hom]
    (h : X ⟶ Z) (U : Z.left.Opens) [AlgebraicGeometry.IsAffine (U : AlgebraicGeometry.Scheme)]
    (hU : Set.range h.left ⊆ (U : Set Z.left)) (x0 : Work.AbVar.Point X) :
    h = SemiCartesianMonoidalCategory.toUnit X ≫ (x0 ≫ h) := by
  haveI : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_subsingleton X.hom
  haveI : UniversallyClosed X.hom := inferInstance
  have hU' : Set.range h.left ⊆ Set.range (U.ι) := by
    rw [Scheme.Opens.range_ι]
    exact hU
  obtain ⟨h', hh'⟩ : ∃ h' : X.left ⟶ (U : AlgebraicGeometry.Scheme),
      h' ≫ U.ι = h.left :=
    ⟨IsOpenImmersion.lift U.ι h.left hU', IsOpenImmersion.lift_fac U.ι h.left hU'⟩
  have hx0 : x0.left ≫ X.hom = 𝟙 (Spec (.of k)) := Over.w x0
  have hstep : h' = X.hom ≫ (x0.left ≫ h') :=
    rigid_aux_const_affine X.hom x0.left hx0 h'
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, Over.toUnit_left]
  calc h.left = h' ≫ U.ι := hh'.symm
    _ = (X.hom ≫ (x0.left ≫ h')) ≫ U.ι := by
        conv_lhs => rw [hstep]
    _ = X.hom ≫ (x0.left ≫ h' ≫ U.ι) := by simp only [Category.assoc]
    _ = X.hom ≫ (x0.left ≫ h.left) := by rw [hh']

open CategoryTheory in
theorem rigid_isAlgClosed {k : Type*} [Field k] [IsAlgClosed k]
    {X Y Z : Work.AbVar.Sch k} [AlgebraicGeometry.IsProper X.hom]
    [AlgebraicGeometry.GeometricallyIntegral X.hom]
    [AlgebraicGeometry.GeometricallyIntegral Y.hom]
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
    [AlgebraicGeometry.IsSeparated Z.hom] [AlgebraicGeometry.LocallyOfFiniteType Z.hom]
    (y0 : Work.AbVar.Point Y) (f : MonoidalCategoryStruct.tensorObj X Y ⟶ Z)
    (c : Work.AbVar.Point Z)
    (hf : Work.AbVar.sectionLeft X Y y0 ≫ f = SemiCartesianMonoidalCategory.toUnit X ≫ c)
    (x0 : Work.AbVar.Point X) :
    f = SemiCartesianMonoidalCategory.snd X Y ≫ Work.AbVar.sectionRight X Y x0 ≫ f := by
  haveI hYint : IsIntegral Y.left := GeometricallyIntegral.isIntegral_of_subsingleton Y.hom
  haveI hYnoeth : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  haveI hXYlft : LocallyOfFiniteType ((X ⊗ Y).hom) := by rw [Over.tensorObj_hom]; infer_instance
  haveI hXYint : IsIntegral (X ⊗ Y).left :=
    inferInstanceAs (IsIntegral (pullback X.hom Y.hom))
  haveI hXYred : IsReduced (X ⊗ Y).left := inferInstance
  haveI hflft : LocallyOfFiniteType (f.left ≫ Z.hom) := by rw [Over.w f]; exact hXYlft
  haveI hYpre : PreirreducibleSpace ↥Y.left := inferInstance
  haveI hXYpre : PreirreducibleSpace ↥(X ⊗ Y).left :=
    inferInstanceAs (PreirreducibleSpace ↥(pullback X.hom Y.hom))
  -- Step 1: an affine open neighbourhood `U` of the image of the point `c`
  obtain ⟨_, ⟨U, hUaff, rfl⟩, hcU, _⟩ :=
    Z.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (c.left (IsLocalRing.closedPoint k))) isOpen_univ
  haveI : IsAffine (U : AlgebraicGeometry.Scheme) := hUaff
  -- Step 2: the open set of points of `Y` whose fibre maps into `U`
  have hWopen : IsOpen ((f.left ⁻¹ᵁ U : (X ⊗ Y).left.Opens) : Set (X ⊗ Y).left) :=
    (f.left ⁻¹ᵁ U).2
  have hcoerce : ((f.left ⁻¹ᵁ U : (X ⊗ Y).left.Opens) : Set (X ⊗ Y).left)
      = f.left ⁻¹' (U : Set Z.left) := rfl
  have hclosed : IsClosed ((SemiCartesianMonoidalCategory.snd X Y).left ''
      ((f.left ⁻¹ᵁ U : Set (X ⊗ Y).left))ᶜ) := by
    have hmap : IsClosedMap (SemiCartesianMonoidalCategory.snd X Y).left := by
      haveI : IsProper (SemiCartesianMonoidalCategory.snd X Y).left :=
        inferInstanceAs (IsProper (pullback.snd X.hom Y.hom))
      exact (SemiCartesianMonoidalCategory.snd X Y).left.isClosedMap
    exact hmap _ hWopen.isClosed_compl
  let V : Y.left.Opens :=
    ⟨((SemiCartesianMonoidalCategory.snd X Y).left ''
      ((f.left ⁻¹ᵁ U : Set (X ⊗ Y).left))ᶜ)ᶜ, hclosed.isOpen_compl⟩
  have hVfib : ∀ ⦃y : Y.left⦄, y ∈ V → ∀ p : (X ⊗ Y).left,
      (SemiCartesianMonoidalCategory.snd X Y).left p = y → f.left p ∈ U := by
    intro y hy p hp
    by_contra hcon
    have hmem : y ∈ (SemiCartesianMonoidalCategory.snd X Y).left ''
        ((f.left ⁻¹ᵁ U : Set (X ⊗ Y).left))ᶜ :=
      ⟨p, by
        simp only [Set.mem_compl_iff, Set.mem_preimage]
        exact hcon, hp⟩
    exact hy hmem
  -- Step 3: the point of `y0` lies in `V`
  have hqV : (y0.left (IsLocalRing.closedPoint k)) ∈ V := by
    have hnot : (y0.left (IsLocalRing.closedPoint k)) ∉
        (SemiCartesianMonoidalCategory.snd X Y).left ''
          ((f.left ⁻¹ᵁ U : Set (X ⊗ Y).left))ᶜ := by
      rintro ⟨p, hpW, hpq⟩
      -- `p` lies in the fibre over the point of `y0`, hence in the range of `sectionLeft`
      have hpr : p ∈ Set.range (Work.AbVar.sectionLeft X Y y0).left := by
        rw [range_sectionLeft X Y y0]
        exact ⟨IsLocalRing.closedPoint k, hpq.symm⟩
      obtain ⟨x, rfl⟩ := hpr
      haveI := rigid_aux_subsingleton_point_left (k := k)
      have hx : (SemiCartesianMonoidalCategory.toUnit X).left x = IsLocalRing.closedPoint k :=
        Subsingleton.elim _ _
      have hval : f.left ((Work.AbVar.sectionLeft X Y y0).left x)
          = c.left (IsLocalRing.closedPoint k) := by
        have hh := congrArg Over.Hom.left hf
        rw [Over.comp_left, Over.comp_left] at hh
        have hhx := congr($hh x)
        simpa only [Scheme.Hom.comp_apply, hx] using hhx
      exact hpW (by
        rw [hcoerce, Set.mem_preimage]
        exact hval ▸ hcU)
    exact hnot
  -- Step 4: `V` is dense
  have hVdense : Dense (V : Set Y.left) := IsOpen.dense V.2 ⟨_, hqV⟩
  -- Step 5: on the closed points of the preimage of `V`, `f` and `g` agree
  set g : MonoidalCategoryStruct.tensorObj X Y ⟶ Z :=
    SemiCartesianMonoidalCategory.snd X Y ≫ Work.AbVar.sectionRight X Y x0 ≫ f with hg
  have key : ∀ p ∈ ((SemiCartesianMonoidalCategory.snd X Y).left ⁻¹ᵁ V : Set (X ⊗ Y).left),
      IsClosed {p} → f.left p = g.left p := by
    intro p hp hpc
    set y : Y.left := (SemiCartesianMonoidalCategory.snd X Y).left p with hy
    have hyV : y ∈ V := hp
    have hyc : IsClosed {y} := by
      have hmap : IsClosedMap (SemiCartesianMonoidalCategory.snd X Y).left := by
        haveI : IsProper (SemiCartesianMonoidalCategory.snd X Y).left :=
          inferInstanceAs (IsProper (pullback.snd X.hom Y.hom))
        exact (SemiCartesianMonoidalCategory.snd X Y).left.isClosedMap
      have h1 : IsClosed {(SemiCartesianMonoidalCategory.snd X Y).left p} := by
        simpa only [Set.image_singleton] using hmap {p} hpc
      rwa [hy]
    let y' : Work.AbVar.Point Y := Over.homMk (pointOfClosedPoint Y.hom y hyc)
    have hy' : y'.left (IsLocalRing.closedPoint k) = y :=
      pointOfClosedPoint_apply Y.hom y hyc (IsLocalRing.closedPoint k)
    -- the morphism `sectionLeft y' ≫ f` lands in `U`
    have hU' : Set.range ((Work.AbVar.sectionLeft X Y y').left ≫ f.left) ⊆ (U : Set Z.left) := by
      rintro _ ⟨x, rfl⟩
      apply hVfib hyV
      have hsnd := congrArg Over.Hom.left (Work.AbVar.sectionLeft_snd X Y y')
      simp only [Over.comp_left, Over.toUnit_left] at hsnd
      have hsndx := congr($hsnd x)
      simp only [Scheme.Hom.comp_apply] at hsndx
      haveI := rigid_aux_subsingleton_point_left (k := k)
      have hx' : X.hom x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      rw [hx', hy'] at hsndx
      exact hsndx
    -- hence it is constant
    have hconst := rigid_aux_const_of_range_subset_affineOpen (h := Work.AbVar.sectionLeft X Y y' ≫ f)
      U hU' x0
    -- the composite of `sectionLeft y'` with `g` is the same constant morphism
    have hcomp : Work.AbVar.sectionLeft X Y y' ≫ g =
        SemiCartesianMonoidalCategory.toUnit X ≫ (y' ≫ Work.AbVar.sectionRight X Y x0 ≫ f) := by
      rw [hg, ← Category.assoc, Work.AbVar.sectionLeft_snd, Category.assoc]
    have hcompat : x0 ≫ Work.AbVar.sectionLeft X Y y' =
        y' ≫ Work.AbVar.sectionRight X Y x0 := rigid_aux_sectionLeft_sectionRight x0 y'
    have hpt : x0 ≫ (Work.AbVar.sectionLeft X Y y' ≫ f) =
        y' ≫ (Work.AbVar.sectionRight X Y x0 ≫ f) := by
      rw [← Category.assoc, hcompat, Category.assoc]
    have hconst' : Work.AbVar.sectionLeft X Y y' ≫ f = Work.AbVar.sectionLeft X Y y' ≫ g := by
      rw [hcomp, hconst]
      exact congrArg (fun φ : (𝟙_ (Work.AbVar.Sch k)) ⟶ Z =>
        SemiCartesianMonoidalCategory.toUnit X ≫ φ) hpt
    -- `p` lies in the range of `sectionLeft y'`
    have hpr : p ∈ Set.range (Work.AbVar.sectionLeft X Y y').left := by
      rw [range_sectionLeft X Y y', rigid_aux_range_left_point (y := y'), hy']
      exact Set.mem_singleton_iff.mpr hy.symm
    obtain ⟨q, hq⟩ := hpr
    calc f.left p = f.left ((Work.AbVar.sectionLeft X Y y').left q) := by rw [hq]
      _ = ((Work.AbVar.sectionLeft X Y y').left ≫ f.left) q := by rw [Scheme.Hom.comp_apply]
      _ = (Over.Hom.left (Work.AbVar.sectionLeft X Y y' ≫ f)) q := by rw [Over.comp_left]
      _ = (Over.Hom.left (Work.AbVar.sectionLeft X Y y' ≫ g)) q := by rw [hconst']
      _ = ((Work.AbVar.sectionLeft X Y y').left ≫ g.left) q := by rw [Over.comp_left]
      _ = g.left ((Work.AbVar.sectionLeft X Y y').left q) := by rw [Scheme.Hom.comp_apply]
      _ = g.left p := by rw [hq]
  -- Step 6: conclude by density
  have hSne : ((SemiCartesianMonoidalCategory.snd X Y).left ⁻¹ᵁ V :
      Set (X ⊗ Y).left).Nonempty := by
    refine ⟨(Work.AbVar.sectionRight X Y x0).left (y0.left (IsLocalRing.closedPoint k)), ?_⟩
    show (SemiCartesianMonoidalCategory.snd X Y).left
      ((Work.AbVar.sectionRight X Y x0).left (y0.left (IsLocalRing.closedPoint k))) ∈ V
    rw [rigid_aux_snd_left_sectionRight_apply x0]
    exact hqV
  have hmain : f.left = g.left := by
    refine ext_of_apply_eq Z.hom ((SemiCartesianMonoidalCategory.snd X Y).left ⁻¹ᵁ V) ?_ ?_ ?_ ?_
    · exact ((SemiCartesianMonoidalCategory.snd X Y).left ⁻¹ᵁ V).2.isLocallyClosed
    · exact IsOpen.dense ((SemiCartesianMonoidalCategory.snd X Y).left ⁻¹ᵁ V).2 hSne
    · exact key
    · rw [Over.w f, Over.w g]
  exact Over.OverMorphism.ext hmain

end Work.AbVar.Rigidity
