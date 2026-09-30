import Mathlib
import Submission.Work.JacClose.Basic
import Submission.Work.Normality.All
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.Sym.isIntegral_sym
import Submission.Work.SymQuot.Sym.geometricallyIntegral_sym
import Submission.Work.SymQuot.RelQuot.relativeQuotAffinePieceAux
import Submission.Work.SymQuot.Chart.chartRes_isEmbedding
import Submission.Work.SpecLin.Chart.isDomain_tensorProduct_fractionRing
import Submission.Work.JacClose.tensor_fixedPoints_normal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonoidalCategory TensorProduct
open scoped Work.GCBasics

universe u

namespace Work.JacClose

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-! ## 1. General scheme-theoretic lemmas -/

/-- **The range of the tensor of two open immersions.**  For `K`-schemes `f : X₁ ⟶ Y₁` and
`g : X₂ ⟶ Y₂` whose underlying morphisms are open immersions, the range of the underlying morphism
of `f ⊗ₘ g` is the intersection of the preimages of the ranges of `f` and `g` in the fibre product
`Y₁ ⊗ Y₂`. -/
theorem range_tensorHom_left {S : Scheme} {X₁ X₂ Y₁ Y₂ : Over S} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    Set.range (f ⊗ₘ g).left =
      (pullback.fst Y₁.hom Y₂.hom ⁻¹' Set.range f.left) ∩
      (pullback.snd Y₁.hom Y₂.hom ⁻¹' Set.range g.left) := by
  rw [Over.tensorHom_left f g]
  exact Scheme.Pullback.range_map X₁.hom X₂.hom Y₁.hom Y₂.hom f.left g.left (𝟙 S)
    (by simp) (by simp)

/-- Membership form of `range_tensorHom_left`. -/
theorem mem_range_tensorHom_left {S : Scheme} {X₁ X₂ Y₁ Y₂ : Over S} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    [IsOpenImmersion f.left] [IsOpenImmersion g.left] (x : ↥(pullback Y₁.hom Y₂.hom)) :
    (∃ y, (f ⊗ₘ g).left y = x) ↔
      pullback.fst Y₁.hom Y₂.hom x ∈ Set.range f.left ∧
      pullback.snd Y₁.hom Y₂.hom x ∈ Set.range g.left := by
  rw [← Set.mem_range, range_tensorHom_left f g]
  exact Iff.rfl

/-- **The binary product open in a fibre product over an affine base is affine.**  For affine opens
`U ⊆ A` and `W ⊆ B` of schemes over an affine base `S`, the open subscheme
`fst ⁻¹ᵁ U ⊓ snd ⁻¹ᵁ W` of the fibre product `A ×_S B` is affine. -/
theorem isAffineOpen_prodOpens {S A B : Scheme} [IsAffine S] (f : A ⟶ S) (g : B ⟶ S)
    {U : A.Opens} (hU : IsAffineOpen U) {W : B.Opens} (hW : IsAffineOpen W) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ W) := by
  haveI : IsAffine U := hU
  haveI : IsAffine W := hW
  let h : pullback (U.ι ≫ f) (W.ι ≫ g) ⟶ pullback f g :=
    pullback.map (U.ι ≫ f) (W.ι ≫ g) f g U.ι W.ι (𝟙 S) (by simp) (by simp)
  haveI : IsOpenImmersion h :=
    Scheme.pullback_map_isOpenImmersion (U.ι ≫ f) (W.ι ≫ g) f g U.ι W.ι (𝟙 S)
      (by simp) (by simp)
  have hrange : h.opensRange = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ W := by
    ext x
    rw [Scheme.Hom.coe_opensRange]
    change x ∈ Set.range ⇑h ↔
      x ∈ (pullback.fst f g ⁻¹ᵁ U : Set _) ⊓ (pullback.snd f g ⁻¹ᵁ W : Set _)
    rw [Scheme.Pullback.range_map (U.ι ≫ f) (W.ι ≫ g) f g U.ι W.ι (𝟙 S) (by simp) (by simp)]
    simp [Set.mem_inter_iff, Set.mem_preimage, Scheme.Opens.range_ι]
  rw [← hrange]
  exact isAffineOpen_opensRange h

/-- **The sections over the range of an open immersion.**  For an open immersion `f : X ⟶ Y` of
schemes, the ring of sections of `Y` over the image of `f` is the ring of sections of `X`. -/
noncomputable def sections_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    Γ(Y, f.opensRange) ≅ Γ(X, ⊤) :=
  (Scheme.Opens.topIso f.opensRange).symm ≪≫
    Scheme.Γ.mapIso (eqToIso (congrArg Scheme.Opens.toScheme f.image_top_eq_opensRange)).op ≪≫
    Scheme.Γ.mapIso (f.isoImage ⊤).op ≪≫
    Scheme.Opens.topIso ⊤

/-- **Sections of a smooth `K`-scheme over an affine open form a smooth `K`-algebra.** -/
theorem algebraSmooth_sections {X : Work.SpecLin.Sch K} [Smooth X.hom] {U : X.left.Opens}
    (hU : IsAffineOpen U) : Algebra.Smooth K Γ(X.left, U) := by
  have h1 : RingHom.Smooth (X.hom.appLE ⊤ U le_top).hom :=
    X.hom.smooth_appLE (isAffineOpen_top _) hU le_top
  have h2 : RingHom.Smooth ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have h3 : RingHom.Smooth (((X.hom.appLE ⊤ U le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) := RingHom.Smooth.comp h2 h1
  exact RingHom.smooth_algebraMap.mp h3


/-! ## 2. The charts of `Symⁿ C` -/

/-- The chart of `Symⁿ C` attached to an invariant affine open `U ⊆ Cⁿ`: the range of the chart
open immersion `D.chartι U`. -/
noncomputable def symChartOpen (C : CurveBasics.Curve K) (n : ℕ)
    (U : (SymQuot.symData C n).Chart) : (SymQuot.Sym C n).left.Opens :=
  ((SymQuot.symData C n).chartι U).opensRange

theorem isAffineOpen_symChartOpen (C : CurveBasics.Curve K) (n : ℕ)
    (U : (SymQuot.symData C n).Chart) : IsAffineOpen (symChartOpen C n U) :=
  isAffineOpen_opensRange ((SymQuot.symData C n).chartι U)

/-- Every point of `Symⁿ C` lies in the chart of a **nonempty** invariant affine open of `Cⁿ`. -/
theorem exists_nonempty_chart_mem (C : CurveBasics.Curve K) (n : ℕ)
    (y : (SymQuot.Sym C n).left) :
    ∃ U : (SymQuot.symData C n).Chart, Nonempty U.1 ∧ y ∈ symChartOpen C n U := by
  obtain ⟨U, u, hu⟩ := (SymQuot.symData C n).chartι_jointly_surjective y
  refine ⟨U, ?_, Scheme.Hom.mem_opensRange.mpr ⟨u, hu⟩⟩
  obtain ⟨z, -⟩ := SymQuot.Chart.chartMap_surjective (SymQuot.symData C n).action U.2.1 U.2.2 u
  exact ⟨z.1, z.2⟩

/-- **The ring of sections of `Symⁿ C` over the chart of `U` is the invariant ring**
`Γ(Cⁿ, U)^{S_n}`. -/
noncomputable def symChartSections (C : CurveBasics.Curve K) (n : ℕ)
    (U : (SymQuot.symData C n).Chart) :
    Γ((SymQuot.Sym C n).left, symChartOpen C n U) ≃+*
      ↥(FixedPoints.subalgebra K Γ((SymQuot.prod C.toOver n).left, U.1)
        (ULift.{u} (Equiv.Perm (Fin n)))) :=
  ((sections_opensRange ((SymQuot.symData C n).chartι U)) ≪≫
    Scheme.ΓSpecIso ((SymQuot.symData C n).action.chartRing U.1 U.2.2)).commRingCatIsoToRingEquiv

/-! ## 3. The pieces of the product `Symᵐ C ⊗ Symⁿ C` -/

/-- The invariant ring `Γ(Cⁿ, U)^{S_n}` of the chart of an invariant affine open `U ⊆ Cⁿ`. -/
abbrev chartInvariants (C : CurveBasics.Curve K) (n : ℕ) (U : (SymQuot.symData C n).Chart) :
    Type u :=
  ↥(FixedPoints.subalgebra K Γ((SymQuot.prod C.toOver n).left, U.1)
    (ULift.{u} (Equiv.Perm (Fin n))))

/-- **A piece of the product `Symᵐ C ⊗ Symⁿ C`**: the product of the charts of `U` and `W`. -/
noncomputable def pieceOpen (C : CurveBasics.Curve K) (m n : ℕ)
    (U : (SymQuot.symData C m).Chart) (W : (SymQuot.symData C n).Chart) :
    (SymTensor C m n).left.Opens :=
  pullback.fst (SymQuot.Sym C m).hom (SymQuot.Sym C n).hom ⁻¹ᵁ symChartOpen C m U ⊓
    pullback.snd (SymQuot.Sym C m).hom (SymQuot.Sym C n).hom ⁻¹ᵁ symChartOpen C n W

theorem mem_pieceOpen (C : CurveBasics.Curve K) (m n : ℕ)
    (U : (SymQuot.symData C m).Chart) (W : (SymQuot.symData C n).Chart)
    (x : (SymTensor C m n).left) :
    x ∈ pieceOpen C m n U W ↔
      pullback.fst (SymQuot.Sym C m).hom (SymQuot.Sym C n).hom x ∈ symChartOpen C m U ∧
      pullback.snd (SymQuot.Sym C m).hom (SymQuot.Sym C n).hom x ∈ symChartOpen C n W :=
  Iff.rfl

theorem isAffineOpen_pieceOpen (C : CurveBasics.Curve K) (m n : ℕ)
    (U : (SymQuot.symData C m).Chart) (W : (SymQuot.symData C n).Chart) :
    IsAffineOpen (pieceOpen C m n U W) :=
  isAffineOpen_prodOpens (SymQuot.Sym C m).hom (SymQuot.Sym C n).hom
    (isAffineOpen_symChartOpen C m U) (isAffineOpen_symChartOpen C n W)

/-- The **piece map**: the inclusion of the piece `chartU U ⊗ chartU W` into the product. -/
noncomputable def pieceMap (C : CurveBasics.Curve K) (m n : ℕ)
    (U : (SymQuot.symData C m).Chart) (W : (SymQuot.symData C n).Chart) :
    (SymQuot.RelQuot.chartU (SymQuot.symData C m) (SymQuot.sym_hom_invariant C m) U ⊗
      SymQuot.RelQuot.chartU (SymQuot.symData C n) (SymQuot.sym_hom_invariant C n) W) ⟶
      SymTensor C m n :=
  SymQuot.RelQuot.chartιOv (SymQuot.symData C m) (SymQuot.sym_hom_invariant C m) U ⊗ₘ
    SymQuot.RelQuot.chartιOv (SymQuot.symData C n) (SymQuot.sym_hom_invariant C n) W

instance instIsOpenImmersion_pieceMap (C : CurveBasics.Curve K) (m n : ℕ)
    (U : (SymQuot.symData C m).Chart) (W : (SymQuot.symData C n).Chart) :
    IsOpenImmersion (pieceMap C m n U W).left := by
  have hmap : (pieceMap C m n U W).left =
      (SymQuot.RelQuot.chartιOv (SymQuot.symData C m) (SymQuot.sym_hom_invariant C m) U ⊗ₘ
        SymQuot.RelQuot.chartιOv (SymQuot.symData C n) (SymQuot.sym_hom_invariant C n) W).left :=
    rfl
  rw [hmap, Over.tensorHom_left]
  simp only [SymQuot.RelQuot.chartιOv_left]
  exact Scheme.pullback_map_isOpenImmersion _ _ _ _
    ((SymQuot.symData C m).chartι U) ((SymQuot.symData C n).chartι W)
    (𝟙 (Spec (CommRingCat.of K)))
    (by rw [Category.comp_id, SymQuot.RelQuot.chartU_hom])
    (by rw [Category.comp_id, SymQuot.RelQuot.chartU_hom])

theorem mem_range_pieceMap (C : CurveBasics.Curve K) (m n : ℕ)
    (U : (SymQuot.symData C m).Chart) (W : (SymQuot.symData C n).Chart)
    (x : (SymTensor C m n).left) :
    (∃ y, (pieceMap C m n U W).left y = x) ↔
      pullback.fst (SymQuot.Sym C m).hom (SymQuot.Sym C n).hom x ∈ symChartOpen C m U ∧
      pullback.snd (SymQuot.Sym C m).hom (SymQuot.Sym C n).hom x ∈ symChartOpen C n W := by
  haveI hI₁ : IsOpenImmersion (SymQuot.RelQuot.chartιOv (SymQuot.symData C m)
      (SymQuot.sym_hom_invariant C m) U).left := by
    rw [SymQuot.RelQuot.chartιOv_left]; exact inferInstance
  haveI hI₂ : IsOpenImmersion (SymQuot.RelQuot.chartιOv (SymQuot.symData C n)
      (SymQuot.sym_hom_invariant C n) W).left := by
    rw [SymQuot.RelQuot.chartιOv_left]; exact inferInstance
  have h := mem_range_tensorHom_left (SymQuot.RelQuot.chartιOv (SymQuot.symData C m)
      (SymQuot.sym_hom_invariant C m) U)
    (SymQuot.RelQuot.chartιOv (SymQuot.symData C n) (SymQuot.sym_hom_invariant C n) W) x
  exact h

theorem pieceMap_opensRange (C : CurveBasics.Curve K) (m n : ℕ)
    (U : (SymQuot.symData C m).Chart) (W : (SymQuot.symData C n).Chart) :
    (pieceMap C m n U W).left.opensRange = pieceOpen C m n U W := by
  ext x
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_opensRange]
  exact (mem_range_pieceMap C m n U W x).trans (mem_pieceOpen C m n U W x).symm

/-- **The piece is affine**: `chartU U ⊗ chartU W ≅ Spec (A^{S_m} ⊗[K] B^{S_n})`. -/
noncomputable def pieceSchemeIso (C : CurveBasics.Curve K) (m n : ℕ)
    (U : (SymQuot.symData C m).Chart) (W : (SymQuot.symData C n).Chart) :
    (SymQuot.RelQuot.chartU (SymQuot.symData C m) (SymQuot.sym_hom_invariant C m) U ⊗
      SymQuot.RelQuot.chartU (SymQuot.symData C n) (SymQuot.sym_hom_invariant C n) W) ≅
      Work.SpecLin.specOf (K := K) (chartInvariants C m U ⊗[K] chartInvariants C n W) :=
  (SymQuot.RelQuot.chartIsoSpecOf (SymQuot.symData C m) (SymQuot.sym_hom_invariant C m) U ⊗ᵢ
    SymQuot.RelQuot.chartIsoSpecOf (SymQuot.symData C n) (SymQuot.sym_hom_invariant C n) W) ≪≫
    SymQuot.RelQuot.specTensorIso (K := K) (chartInvariants C m U) (chartInvariants C n W)

/-- **The ring of sections of a piece** is the tensor product of the two invariant rings. -/
noncomputable def pieceSections (C : CurveBasics.Curve K) (m n : ℕ)
    (U : (SymQuot.symData C m).Chart) (W : (SymQuot.symData C n).Chart) :
    Γ((SymTensor C m n).left, pieceOpen C m n U W) ≃+*
      (chartInvariants C m U ⊗[K] chartInvariants C n W) :=
  (pieceMap_opensRange C m n U W) ▸
    ((sections_opensRange (pieceMap C m n U W).left) ≪≫
      (Scheme.Γ.mapIso ((Over.forget (Spec (CommRingCat.of K))).mapIso
        (pieceSchemeIso C m n U W)).op).symm ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (chartInvariants C m U ⊗[K] chartInvariants C n W))
      ).commRingCatIsoToRingEquiv

/-! ## 4. The main theorem -/

/-- Sections of a power of a curve over an affine open form a smooth `K`-algebra. -/
theorem algebraSmooth_pow_sections (C : CurveBasics.Curve K) (m : ℕ)
    {U : (SymQuot.prod C.toOver m).left.Opens} (hU : IsAffineOpen U) :
    Algebra.Smooth K Γ((SymQuot.prod C.toOver m).left, U) := by
  haveI : Smooth (SymQuot.prod C.toOver m).hom := SymQuot.smooth_pi_prod C m
  exact algebraSmooth_sections (X := SymQuot.prod C.toOver m) hU

/-- The tensor product of the section rings of two affine opens of powers of a curve is a
domain: `Γ(Cᵐ, U)` is geometrically integral over `K`, so it embeds into
`Γ(Cᵐ, U) ⊗[K] Frac Γ(Cⁿ, W)`, which is a domain. -/
theorem isDomain_tensor_pow_sections (C : CurveBasics.Curve K) (m n : ℕ)
    {U : (SymQuot.prod C.toOver m).left.Opens} (hU : IsAffineOpen U) [Nonempty U]
    {W : (SymQuot.prod C.toOver n).left.Opens} (_hW : IsAffineOpen W) [Nonempty W] :
    IsDomain (TensorProduct K Γ((SymQuot.prod C.toOver m).left, U)
      Γ((SymQuot.prod C.toOver n).left, W)) := by
  haveI : IsIntegral (SymQuot.prod C.toOver n).left := SymQuot.isIntegral_prod C n
  haveI hWdom : IsDomain Γ((SymQuot.prod C.toOver n).left, W) := inferInstance
  exact Work.SpecLin.Chart.isDomain_tensorProduct_fractionRing (K := K)
    (A := Γ((SymQuot.prod C.toOver m).left, U))
    (R := Γ((SymQuot.prod C.toOver n).left, W))
    (SymQuot.Sym.isDomain_sections_tensor C m U hU
      (FractionRing Γ((SymQuot.prod C.toOver n).left, W)))

/-- **Every local ring of a product of two symmetric powers of a smooth curve is integrally
closed.**

The product is covered by the pieces `chartU U ⊗ chartU W` for invariant affine opens
`U ⊆ Cᵐ`, `W ⊆ Cⁿ`; such a piece is affine with ring `Γ(Cᵐ,U)^{S_m} ⊗[K] Γ(Cⁿ,W)^{S_n}`, a
domain and integrally closed by `Work.JacClose.tensor_fixedPoints_normal`. -/
theorem normal_sym_tensor {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (m n : ℕ)
    (x : (Work.JacClose.SymTensor C m n).left) :
    IsIntegrallyClosed ((Work.JacClose.SymTensor C m n).left.presheaf.stalk x) := by
  obtain ⟨U, hUne, hUx⟩ := exists_nonempty_chart_mem C m
    (pullback.fst (SymQuot.Sym C m).hom (SymQuot.Sym C n).hom x)
  obtain ⟨W, hWne, hWx⟩ := exists_nonempty_chart_mem C n
    (pullback.snd (SymQuot.Sym C m).hom (SymQuot.Sym C n).hom x)
  haveI : Nonempty U.1 := hUne
  haveI : Nonempty W.1 := hWne
  haveI : IsIntegral (SymQuot.prod C.toOver m).left := SymQuot.isIntegral_prod C m
  haveI : IsIntegral (SymQuot.prod C.toOver n).left := SymQuot.isIntegral_prod C n
  haveI hdomA : IsDomain Γ((SymQuot.prod C.toOver m).left, U.1) := inferInstance
  haveI hdomB : IsDomain Γ((SymQuot.prod C.toOver n).left, W.1) := inferInstance
  haveI hsmA : Algebra.Smooth K Γ((SymQuot.prod C.toOver m).left, U.1) :=
    algebraSmooth_pow_sections C m U.2.1
  haveI hsmB : Algebra.Smooth K Γ((SymQuot.prod C.toOver n).left, W.1) :=
    algebraSmooth_pow_sections C n W.2.1
  haveI hdomAB : IsDomain (TensorProduct K Γ((SymQuot.prod C.toOver m).left, U.1)
      Γ((SymQuot.prod C.toOver n).left, W.1)) :=
    isDomain_tensor_pow_sections C m n U.2.1 W.2.1
  obtain ⟨hdomT, hicT⟩ := Work.JacClose.tensor_fixedPoints_normal (K := K)
    (A := Γ((SymQuot.prod C.toOver m).left, U.1))
    (B := Γ((SymQuot.prod C.toOver n).left, W.1))
    (G := ULift.{u} (Equiv.Perm (Fin m))) (H := ULift.{u} (Equiv.Perm (Fin n)))
  haveI : IsDomain (chartInvariants C m U ⊗[K] chartInvariants C n W) := hdomT
  haveI : IsIntegrallyClosed (chartInvariants C m U ⊗[K] chartInvariants C n W) := hicT
  haveI hdomPiece : IsDomain Γ((SymTensor C m n).left, pieceOpen C m n U W) :=
    Function.Injective.isDomain (pieceSections C m n U W).toRingHom
      (pieceSections C m n U W).injective
  have hx : x ∈ pieceOpen C m n U W :=
    (mem_pieceOpen C m n U W x).mpr ⟨hUx, hWx⟩
  refine Work.Normality.isIntegrallyClosed_stalk_of_isAffineOpen
    (isAffineOpen_pieceOpen C m n U W) ?_ hx
  exact IsIntegrallyClosed.of_equiv (pieceSections C m n U W).symm

end
end Work.JacClose


