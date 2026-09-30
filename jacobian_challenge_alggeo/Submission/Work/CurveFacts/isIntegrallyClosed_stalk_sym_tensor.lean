import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.CurveInstance
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.QuotientData
import Submission.Work.SymQuot.DivBaseInst
import Submission.Work.SymQuot.Invariants.tensor_fixedPoints_of_flat
import Submission.Work.Normality.Sym
import Submission.Work.Normality.Scheme
import Submission.Work.Normality.isIntegrallyClosed_invariants
import Submission.Work.Normality.isIntegrallyClosed_of_smooth_algebra
import Submission.Work.SymQuot.RelQuot.relativeQuotAffinePieceAux
import Submission.Work.SymQuot.Sym.geometricallyIntegral_sym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveFacts

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonoidalCategory TensorProduct

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-! ## Part 1: the algebra of tensor products of invariant rings -/

section Algebra

variable {K : Type u} [Field K]

/-- A tensor product of two smooth algebras over a field is smooth: the map `K ⟶ A ⊗[K] B` is
the composite of `K ⟶ A` (smooth by hypothesis) and `A ⟶ A ⊗[K] B` (the base change of
`K ⟶ B`, smooth by the stability of smoothness under base change). -/
theorem algebraSmooth_tensorProduct {A B : Type u} [CommRing A] [Algebra K A] [CommRing B]
    [Algebra K B] [Algebra.Smooth K A] [Algebra.Smooth K B] :
    Algebra.Smooth K (A ⊗[K] B) := by
  have h1 : (algebraMap K A).Smooth := RingHom.smooth_algebraMap.mpr ‹Algebra.Smooth K A›
  have h2 : (algebraMap A (A ⊗[K] B)).Smooth :=
    RingHom.smooth_algebraMap.mpr (Algebra.Smooth.baseChange K B A)
  have h3 : ((algebraMap A (A ⊗[K] B)).comp (algebraMap K A)).Smooth :=
    RingHom.Smooth.comp h1 h2
  rw [← IsScalarTower.algebraMap_eq K A (A ⊗[K] B)] at h3
  exact RingHom.smooth_algebraMap.mp h3

/-- **`A^G ⊗[K] B ≅ (A ⊗[K] B)^G`**, where the finite group `G` acts on `A ⊗[K] B` through the
first factor.  This is `Work.SymQuot.Invariants.tensor_fixedPoints_of_flat`, packaged as a ring
equivalence. -/
noncomputable def fixedPointsTensorEquiv {A B : Type u} [CommRing A] [Algebra K A] [CommRing B]
    [Algebra K B] {G : Type u} [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A] :
    ↥(FixedPoints.subalgebra K A G) ⊗[K] B ≃+* ↥(FixedPoints.subring (A ⊗[K] B) G) := by
  classical
  obtain ⟨hinj, hrange⟩ :=
    Work.SymQuot.RelQuot.tensorIncl_range (K := K) (Γ := G) A B
  let φ : ↥(FixedPoints.subalgebra K A G) ⊗[K] B →+* ↥(FixedPoints.subring (A ⊗[K] B) G) :=
    { toFun := fun x => ⟨Work.SymQuot.RelQuot.tensorIncl (K := K) (Γ := G) A B x, by
        have hx : (Work.SymQuot.RelQuot.tensorIncl (K := K) (Γ := G) A B x) ∈
            {y : A ⊗[K] B | ∀ g : G,
              Work.SymQuot.RelQuot.tensorAct (K := K) (Γ := G) A B g y = y} := by
          rw [← hrange]
          exact ⟨x, rfl⟩
        exact hx⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  have hφval : ∀ x : ↥(FixedPoints.subalgebra K A G) ⊗[K] B,
      ((φ x : A ⊗[K] B)) = Work.SymQuot.RelQuot.tensorIncl (K := K) (Γ := G) A B x :=
    fun x => rfl
  have hbij : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      refine hinj ?_
      rw [← hφval x, ← hφval y]
      exact congrArg Subtype.val hxy
    · intro y
      have hy : (y : A ⊗[K] B) ∈ Set.range
          (Work.SymQuot.RelQuot.tensorIncl (K := K) (Γ := G) A B) := by
        rw [hrange]
        exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  exact RingEquiv.ofBijective φ hbij

/-- **The tensor product of the invariant rings of two smooth domains is integrally closed.**
Both `A` and `B` are smooth `K`-algebras which are domains, and `A ⊗[K] B` is a domain.  Then
`A^G ⊗[K] B^H` is integrally closed for finite groups `G`, `H` acting by `K`-algebra
automorphisms. -/
theorem isIntegrallyClosed_fixedPoints_tensorProduct {A B : Type u} [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.Smooth K A] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.Smooth K B] [IsDomain (A ⊗[K] B)] {G H : Type u} [Group G] [Fintype G] [Group H]
    [Fintype H] [MulSemiringAction G A] [SMulCommClass G K A] [MulSemiringAction H B]
    [SMulCommClass H K B] :
    IsIntegrallyClosed (↥(FixedPoints.subalgebra K A G) ⊗[K] ↥(FixedPoints.subalgebra K B H)) := by
  haveI hsm : Algebra.Smooth K (A ⊗[K] B) := algebraSmooth_tensorProduct (K := K) (A := A) (B := B)
  haveI hAB : IsIntegrallyClosed (A ⊗[K] B) :=
    Work.Normality.isIntegrallyClosed_of_smooth_algebra (K := K) (A := A ⊗[K] B)
  -- `B ⊗[K] A` is again a domain, and integrally closed
  haveI hdomBA : IsDomain (B ⊗[K] A) := by
    refine Function.Injective.isDomain (Algebra.TensorProduct.comm K B A).toRingHom ?_
    intro x y hxy
    exact (Algebra.TensorProduct.comm K B A).injective hxy
  haveI hICBA : IsIntegrallyClosed (B ⊗[K] A) :=
    IsIntegrallyClosed.of_equiv (Algebra.TensorProduct.comm K B A).toRingEquiv.symm
  -- `(B ⊗ A)^H` is integrally closed, being the invariants of a finite group on the domain `B ⊗ A`
  haveI h1 : IsIntegrallyClosed ↥(FixedPoints.subring (B ⊗[K] A) H) :=
    Work.Normality.isIntegrallyClosed_invariants H
  -- hence `B^H ⊗ A` is, and it is a domain (as a subring of `B ⊗ A`)
  haveI h2 : IsIntegrallyClosed (↥(FixedPoints.subalgebra K B H) ⊗[K] A) :=
    IsIntegrallyClosed.of_equiv
      (fixedPointsTensorEquiv (K := K) (A := B) (B := A) (G := H)).symm
  haveI hdom2 : IsDomain (↥(FixedPoints.subalgebra K B H) ⊗[K] A) :=
    Function.Injective.isDomain
      (fixedPointsTensorEquiv (K := K) (A := B) (B := A) (G := H)).toRingHom
      (fixedPointsTensorEquiv (K := K) (A := B) (B := A) (G := H)).injective
  -- the same for `A ⊗[K] B^H`
  haveI h3 : IsIntegrallyClosed (A ⊗[K] ↥(FixedPoints.subalgebra K B H)) :=
    IsIntegrallyClosed.of_equiv
      ((Algebra.TensorProduct.comm K A ↥(FixedPoints.subalgebra K B H)).toRingEquiv).symm
  haveI hdom3 : IsDomain (A ⊗[K] ↥(FixedPoints.subalgebra K B H)) := by
    refine Function.Injective.isDomain
      (Algebra.TensorProduct.comm K A ↥(FixedPoints.subalgebra K B H)).toRingHom ?_
    intro x y hxy
    exact (Algebra.TensorProduct.comm K A ↥(FixedPoints.subalgebra K B H)).injective hxy
  -- `(A ⊗ B^H)^G` is integrally closed, and it is `A^G ⊗ B^H`
  haveI h4 : IsIntegrallyClosed
      ↥(FixedPoints.subring (A ⊗[K] ↥(FixedPoints.subalgebra K B H)) G) :=
    Work.Normality.isIntegrallyClosed_invariants G
  exact IsIntegrallyClosed.of_equiv
    (fixedPointsTensorEquiv (K := K) (A := A) (B := ↥(FixedPoints.subalgebra K B H)) (G := G)).symm


/-- **The tensor product of the invariant rings of two smooth domains is a domain.**  Same
hypotheses as `isIntegrallyClosed_fixedPoints_tensorProduct`; the proof is by reduction to the
domain `A ⊗[K] B`. -/
theorem isDomain_fixedPoints_tensorProduct {A B : Type u} [CommRing A] [IsDomain A]
    [Algebra K A] [CommRing B] [IsDomain B] [Algebra K B] [IsDomain (A ⊗[K] B)] {G H : Type u}
    [Group G] [Fintype G] [Group H] [Fintype H] [MulSemiringAction G A] [SMulCommClass G K A]
    [MulSemiringAction H B] [SMulCommClass H K B] :
    IsDomain (↥(FixedPoints.subalgebra K A G) ⊗[K] ↥(FixedPoints.subalgebra K B H)) := by
  haveI hdomBA : IsDomain (B ⊗[K] A) := by
    refine Function.Injective.isDomain (Algebra.TensorProduct.comm K B A).toRingHom ?_
    intro x y hxy
    exact (Algebra.TensorProduct.comm K B A).injective hxy
  haveI h1 : IsDomain ↥(FixedPoints.subring (B ⊗[K] A) H) := inferInstance
  haveI h2 : IsDomain (↥(FixedPoints.subalgebra K B H) ⊗[K] A) :=
    Function.Injective.isDomain
      (fixedPointsTensorEquiv (K := K) (A := B) (B := A) (G := H)).toRingHom
      (fixedPointsTensorEquiv (K := K) (A := B) (B := A) (G := H)).injective
  haveI h3 : IsDomain (A ⊗[K] ↥(FixedPoints.subalgebra K B H)) := by
    refine Function.Injective.isDomain
      (Algebra.TensorProduct.comm K A ↥(FixedPoints.subalgebra K B H)).toRingHom ?_
    intro x y hxy
    exact (Algebra.TensorProduct.comm K A ↥(FixedPoints.subalgebra K B H)).injective hxy
  haveI h4 : IsDomain ↥(FixedPoints.subring (A ⊗[K] ↥(FixedPoints.subalgebra K B H)) G) :=
    inferInstance
  exact Function.Injective.isDomain
    (fixedPointsTensorEquiv (K := K) (A := A) (B := ↥(FixedPoints.subalgebra K B H)) (G := G)).toRingHom
    (fixedPointsTensorEquiv (K := K) (A := A) (B := ↥(FixedPoints.subalgebra K B H)) (G := G)).injective

end Algebra

/-! ## Part 1b: the underlying function of `Algebra.TensorProduct.map` -/

/-- The underlying function of `Algebra.TensorProduct.map f g` is that of
`TensorProduct.map f g`. -/
theorem coe_algebraTensorProduct_map {R : Type u} [CommSemiring R] {A A' B B' : Type u}
    [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B] [CommSemiring A']
    [Algebra R A'] [CommSemiring B'] [Algebra R B'] (f : A →ₐ[R] A') (g : B →ₐ[R] B') :
    ⇑(Algebra.TensorProduct.map f g) = ⇑(TensorProduct.map f.toLinearMap g.toLinearMap) := by
  funext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

/-! ## Part 2: the product of two charts of symmetric powers -/

section SymChart

variable {K : Type u} [Field K]

/-- The ring of invariants `Γ(C^n, U)^{S_n}` of a chart of `Sym^n C`. -/
abbrev chartInv (C : Work.CurveBasics.Curve K) (n : ℕ)
    (U : (Work.SymQuot.symData C n).Chart) : Type u :=
  ↥(FixedPoints.subalgebra K ↥Γ((Work.SymQuot.prod C.toOver n).left, U.1)
    (ULift.{u} (Equiv.Perm (Fin n))))

/-- **The product of the charts of `Sym^m C` and `Sym^n C`**, as a morphism of `K`-schemes
`Spec (Γ(C^m,U)^{S_m}) ⊗ Spec (Γ(C^n,T)^{S_n}) ⟶ Sym^m C ⊗ Sym^n C`. -/
noncomputable def symChartMap (C : Work.CurveBasics.Curve K) (m n : ℕ)
    (U : (Work.SymQuot.symData C m).Chart) (T : (Work.SymQuot.symData C n).Chart) :
    (Work.SymQuot.RelQuot.chartU (Work.SymQuot.symData C m)
        (Work.SymQuot.sym_hom_invariant C m) U ⊗
      Work.SymQuot.RelQuot.chartU (Work.SymQuot.symData C n)
        (Work.SymQuot.sym_hom_invariant C n) T) ⟶
    (Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n) :=
  (Work.SymQuot.RelQuot.chartιOv (Work.SymQuot.symData C m)
      (Work.SymQuot.sym_hom_invariant C m) U) ⊗ₘ
    (Work.SymQuot.RelQuot.chartιOv (Work.SymQuot.symData C n)
      (Work.SymQuot.sym_hom_invariant C n) T)

/-- The product chart map is an open immersion: it is the tensor product of the two chart maps
of the two quotients, i.e. a pullback of open immersions. -/
theorem symChartMap_isOpenImmersion (C : Work.CurveBasics.Curve K) (m n : ℕ)
    (U : (Work.SymQuot.symData C m).Chart) (T : (Work.SymQuot.symData C n).Chart) :
    IsOpenImmersion (symChartMap C m n U T).left := by
  rw [symChartMap, Over.tensorHom_left]
  simp only [Work.SymQuot.RelQuot.chartιOv_left]
  exact Scheme.pullback_map_isOpenImmersion _ _ _ _
    ((Work.SymQuot.symData C m).chartι U) ((Work.SymQuot.symData C n).chartι T)
    (𝟙 (Spec (CommRingCat.of K)))
    (by rw [Category.comp_id, Work.SymQuot.RelQuot.chartU_hom]; rfl)
    (by rw [Category.comp_id, Work.SymQuot.RelQuot.chartU_hom]; rfl)

/-- The image of the product chart map: an affine open subscheme of `Sym^m C ⊗ Sym^n C`. -/
noncomputable def symChartOpen (C : Work.CurveBasics.Curve K) (m n : ℕ)
    (U : (Work.SymQuot.symData C m).Chart) (T : (Work.SymQuot.symData C n).Chart) :
    (Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n).left.Opens := by
  haveI := symChartMap_isOpenImmersion C m n U T
  exact (symChartMap C m n U T).left ''ᵁ ⊤

/-- The identification of the product of the two charts with the spectrum of the tensor product
of the two rings of invariants. -/
noncomputable def symChartIso (C : Work.CurveBasics.Curve K) (m n : ℕ)
    (U : (Work.SymQuot.symData C m).Chart) (T : (Work.SymQuot.symData C n).Chart) :
    (Work.SymQuot.RelQuot.chartU (Work.SymQuot.symData C m)
        (Work.SymQuot.sym_hom_invariant C m) U ⊗
      Work.SymQuot.RelQuot.chartU (Work.SymQuot.symData C n)
        (Work.SymQuot.sym_hom_invariant C n) T) ≅
    Work.SpecLin.specOf (K := K) (chartInv C m U ⊗[K] chartInv C n T) :=
  (Work.SymQuot.RelQuot.chartIsoSpecOf (Work.SymQuot.symData C m)
      (Work.SymQuot.sym_hom_invariant C m) U ⊗ᵢ
    Work.SymQuot.RelQuot.chartIsoSpecOf (Work.SymQuot.symData C n)
      (Work.SymQuot.sym_hom_invariant C n) T) ≪≫
  Work.SymQuot.RelQuot.specTensorIso (K := K) (chartInv C m U) (chartInv C n T)

/-- The source of the product chart map is affine: it is the product of two spectra, hence the
spectrum of the tensor product of the two invariant rings. -/
theorem isAffine_symChartSource (C : Work.CurveBasics.Curve K) (m n : ℕ)
    (U : (Work.SymQuot.symData C m).Chart) (T : (Work.SymQuot.symData C n).Chart) :
    IsAffine (Work.SymQuot.RelQuot.chartU (Work.SymQuot.symData C m)
        (Work.SymQuot.sym_hom_invariant C m) U ⊗
      Work.SymQuot.RelQuot.chartU (Work.SymQuot.symData C n)
        (Work.SymQuot.sym_hom_invariant C n) T).left := by
  haveI : IsAffine (Over.left (Work.SpecLin.specOf (K := K) (chartInv C m U ⊗[K] chartInv C n T))) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (chartInv C m U ⊗[K] chartInv C n T))))
  haveI hIso : IsIso (symChartIso C m n U T).hom.left :=
    (Over.forget _).map_isIso (symChartIso C m n U T).hom
  exact IsAffine.of_isIso (symChartIso C m n U T).hom.left

/-- The product of two charts of symmetric powers is an affine open subscheme. -/
theorem symChartOpen_isAffineOpen (C : Work.CurveBasics.Curve K) (m n : ℕ)
    (U : (Work.SymQuot.symData C m).Chart) (T : (Work.SymQuot.symData C n).Chart) :
    IsAffineOpen (symChartOpen C m n U T) := by
  haveI := symChartMap_isOpenImmersion C m n U T
  haveI := isAffine_symChartSource C m n U T
  exact IsAffineOpen.image_of_isOpenImmersion (isAffineOpen_top _) (symChartMap C m n U T).left

/-- A point of the product lies in the product chart of `U` and `T` precisely when its
coordinates lie in the ranges of the two chart maps. -/
theorem symChartOpen_mem_iff (C : Work.CurveBasics.Curve K) (m n : ℕ)
    (U : (Work.SymQuot.symData C m).Chart) (T : (Work.SymQuot.symData C n).Chart)
    (z : (Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n).left) :
    z ∈ symChartOpen C m n U T ↔
      (∃ u, (Work.SymQuot.symData C m).chartι U u =
        pullback.fst (Work.SymQuot.Sym C m).hom (Work.SymQuot.Sym C n).hom z) ∧
      (∃ t, (Work.SymQuot.symData C n).chartι T t =
        pullback.snd (Work.SymQuot.Sym C m).hom (Work.SymQuot.Sym C n).hom z) := by
  haveI := symChartMap_isOpenImmersion C m n U T
  have hr : Set.range (symChartMap C m n U T).left =
      (pullback.fst (Work.SymQuot.Sym C m).hom (Work.SymQuot.Sym C n).hom ⁻¹'
        Set.range ((Work.SymQuot.symData C m).chartι U)) ∩
      (pullback.snd (Work.SymQuot.Sym C m).hom (Work.SymQuot.Sym C n).hom ⁻¹'
        Set.range ((Work.SymQuot.symData C n).chartι T)) := by
    rw [symChartMap, Over.tensorHom_left]
    simp only [Work.SymQuot.RelQuot.chartιOv_left]
    exact Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _
  have himg : z ∈ symChartOpen C m n U T ↔ z ∈ Set.range (symChartMap C m n U T).left := by
    rw [symChartOpen, Scheme.Hom.image_top_eq_opensRange]
    exact Iff.rfl
  rw [himg, hr, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage, Set.mem_range,
    Set.mem_range]

/-- The ring of sections of a product chart of symmetric powers is the tensor product of the two
invariant rings. -/
theorem symChartOpen_sections (C : Work.CurveBasics.Curve K) (m n : ℕ)
    (U : (Work.SymQuot.symData C m).Chart) (T : (Work.SymQuot.symData C n).Chart) :
    Nonempty (Γ((Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n).left, symChartOpen C m n U T) ≃+*
      (chartInv C m U ⊗[K] chartInv C n T)) := by
  haveI := symChartMap_isOpenImmersion C m n U T
  haveI hIso : IsIso (symChartIso C m n U T).inv.left :=
    (Over.forget _).map_isIso (symChartIso C m n U T).inv
  refine ⟨(Scheme.Hom.appIso (symChartMap C m n U T).left
    (⊤ : (Work.SymQuot.RelQuot.chartU (Work.SymQuot.symData C m)
        (Work.SymQuot.sym_hom_invariant C m) U ⊗
      Work.SymQuot.RelQuot.chartU (Work.SymQuot.symData C n)
        (Work.SymQuot.sym_hom_invariant C n) T).left.Opens) ≪≫
    asIso ((symChartIso C m n U T).inv.left.app
      (⊤ : (Work.SymQuot.RelQuot.chartU (Work.SymQuot.symData C m)
          (Work.SymQuot.sym_hom_invariant C m) U ⊗
        Work.SymQuot.RelQuot.chartU (Work.SymQuot.symData C n)
          (Work.SymQuot.sym_hom_invariant C n) T).left.Opens)) ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (chartInv C m U ⊗[K] chartInv C n T))).commRingCatIsoToRingEquiv⟩

end SymChart

/-! ## Part 3: smoothness and domains for the sections of the curve powers -/

section Sections

variable {K : Type u} [Field K]

/-- **The ring of sections of an affine open of `C^m` is a smooth `K`-algebra**, `C^m` being
smooth over `K`. -/
theorem smooth_sections_pow (C : Work.CurveBasics.Curve K) (m : ℕ)
    (U : (Work.SymQuot.prod C.toOver m).left.Opens) (hU : IsAffineOpen U) :
    Algebra.Smooth K Γ((Work.SymQuot.prod C.toOver m).left, U) := by
  have hSm : Smooth (Work.SymQuot.prod C.toOver m).hom := Work.SymQuot.smooth_pi_prod C m
  have h1 : RingHom.Smooth (((Work.SymQuot.prod C.toOver m).hom).appLE
      (⊤ : (Spec (CommRingCat.of K)).Opens) U le_top).hom :=
    hSm.smooth_appLE (isAffineOpen_top _) hU le_top
  have h2 : RingHom.Smooth ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have h3 : RingHom.Smooth ((((Work.SymQuot.prod C.toOver m).hom).appLE
      (⊤ : (Spec (CommRingCat.of K)).Opens) U le_top).hom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) :=
    RingHom.Smooth.comp h2 h1
  exact (RingHom.smooth_algebraMap).mp h3

/-- **The tensor product of the rings of sections of two affine opens of `C^m` and `C^n` is a
domain.**  It embeds into `Γ(C^m,U) ⊗[K] Frac Γ(C^n,T)`, a domain because `C^m` is geometrically
integral.  (The tensor product of two domains over a field need not be a domain in general.) -/
theorem isDomain_tensor_sections_pow (C : Work.CurveBasics.Curve K) (m n : ℕ)
    (U : (Work.SymQuot.prod C.toOver m).left.Opens)
    (T : (Work.SymQuot.prod C.toOver n).left.Opens)
    (hU : IsAffineOpen U) (hT : IsAffineOpen T) [Nonempty U] [Nonempty T] :
    IsDomain (Γ((Work.SymQuot.prod C.toOver m).left, U) ⊗[K]
      Γ((Work.SymQuot.prod C.toOver n).left, T)) := by
  haveI hint : IsIntegral (Work.SymQuot.prod C.toOver n).left := Work.SymQuot.isIntegral_prod C n
  let L := FractionRing Γ((Work.SymQuot.prod C.toOver n).left, T)
  haveI hL : IsDomain (Γ((Work.SymQuot.prod C.toOver m).left, U) ⊗[K] L) :=
    Work.SymQuot.Sym.isDomain_sections_tensor C m U hU L
  have hinj : Function.Injective
      ⇑(Algebra.TensorProduct.map (AlgHom.id K ↥Γ((Work.SymQuot.prod C.toOver m).left, U))
        (IsScalarTower.toAlgHom K ↥Γ((Work.SymQuot.prod C.toOver n).left, T) L)) := by
    rw [coe_algebraTensorProduct_map]
    exact TensorProduct.map_injective_of_flat_flat _ _ (fun _ _ h => h)
      (IsFractionRing.injective _ L)
  exact Function.Injective.isDomain
    (Algebra.TensorProduct.map (AlgHom.id K ↥Γ((Work.SymQuot.prod C.toOver m).left, U))
      (IsScalarTower.toAlgHom K ↥Γ((Work.SymQuot.prod C.toOver n).left, T) L)).toRingHom
    (by simpa using hinj)

end Sections

end

/-! ## Part 4: the local rings of `Sym^m C ⊗ Sym^n C` -/

section Main

variable {K : Type u} [Field K]

/-- **Item A4 of the closure design, tensor form: the local rings of `Symᵐ C ×_K Symⁿ C` are
integrally closed.**  This is the second half of the normality input `hstalk` (item O8): the chart
construction over `k` needs the local rings of `Sym^g C ⊗ Sym^g C` (a product in `Sch K`, i.e. a
fibre product over `Spec K`) to be integrally closed.

Route.  Take affine opens `V ⊆ (Sym C m).left` and `W ⊆ (Sym C n).left`; their product
`V ×_K W` is an affine open of the product with `Γ(V ×_K W) ≅ Γ(V) ⊗[K] Γ(W)`.  By
`QuotientData.chart` one has `Γ(V) ≅ Γ(C^m, U)^{S_m}` and `Γ(W) ≅ Γ(C^n, U')^{S_n}` for
invariant affine opens of the powers (see the sibling `Work.CurveFacts.isIntegrallyClosed_stalk_sym`
in this directory for the passage from the colimit charts to these `V`, `W`), so that
`Γ(V) ⊗[K] Γ(W) ≅ (Γ(C^m, U) ⊗[K] Γ(C^n, U'))^{S_m × S_n}` by
`Work.SymQuot.Invariants.tensor_fixedPoints_of_flat` (applied twice, or in the two-variable form).

`Γ(C^m, U) ⊗[K] Γ(C^n, U')` is a smooth `K`-algebra (base change of a smooth algebra) and a
domain: it is the ring of sections of the affine open `U ×_K U'` of the smooth, geometrically
integral scheme `C^{m+n}`.  (Note that the tensor product of two domains over a field need *not*
be a domain in general -- e.g. `ℂ ⊗_ℝ ℂ`; here it is a domain for the geometric-integrality
reason just given.)  Hence `Work.Normality.isIntegrallyClosed_invariants_of_smooth` applies to
the finite group `S_m × S_n`.  Conclude with
`Work.Normality.HasIntegrallyClosedStalks.of_isAffineOpen_cover` over the cover by the
`V ×_K W`. -/
theorem isIntegrallyClosed_stalk_sym_tensor {K : Type u} [Field K]
    (C : Work.CurveBasics.Curve K) (m n : ℕ)
    (x : (Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n).left) :
    IsIntegrallyClosed (((Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n).left).presheaf.stalk x) := by
  classical
  -- the algebra input at every pair of nonempty charts
  have hkey : ∀ (U : {U : (Work.SymQuot.symData C m).Chart // Nonempty U.1})
      (T : {T : (Work.SymQuot.symData C n).Chart // Nonempty T.1}),
      IsIntegrallyClosed (chartInv C m U.1 ⊗[K] chartInv C n T.1) ∧
      IsDomain (chartInv C m U.1 ⊗[K] chartInv C n T.1) := by
    rintro ⟨U, hU⟩ ⟨T, hT⟩
    haveI : Nonempty U.1 := hU
    haveI : Nonempty T.1 := hT
    haveI hintm : IsIntegral (Work.SymQuot.prod C.toOver m).left := Work.SymQuot.isIntegral_prod C m
    haveI hintn : IsIntegral (Work.SymQuot.prod C.toOver n).left := Work.SymQuot.isIntegral_prod C n
    haveI hsm₁ : Algebra.Smooth K ↥Γ((Work.SymQuot.prod C.toOver m).left, U.1) :=
      smooth_sections_pow C m U.1 U.2.1
    haveI hsm₂ : Algebra.Smooth K ↥Γ((Work.SymQuot.prod C.toOver n).left, T.1) :=
      smooth_sections_pow C n T.1 T.2.1
    haveI hdom : IsDomain (↥Γ((Work.SymQuot.prod C.toOver m).left, U.1) ⊗[K]
        ↥Γ((Work.SymQuot.prod C.toOver n).left, T.1)) :=
      isDomain_tensor_sections_pow C m n U.1 T.1 U.2.1 T.2.1
    exact ⟨isIntegrallyClosed_fixedPoints_tensorProduct (K := K)
        (A := ↥Γ((Work.SymQuot.prod C.toOver m).left, U.1))
        (B := ↥Γ((Work.SymQuot.prod C.toOver n).left, T.1))
        (G := ULift.{u} (Equiv.Perm (Fin m))) (H := ULift.{u} (Equiv.Perm (Fin n))),
      isDomain_fixedPoints_tensorProduct (K := K)
        (A := ↥Γ((Work.SymQuot.prod C.toOver m).left, U.1))
        (B := ↥Γ((Work.SymQuot.prod C.toOver n).left, T.1))
        (G := ULift.{u} (Equiv.Perm (Fin m))) (H := ULift.{u} (Equiv.Perm (Fin n)))⟩
  -- the cover by the products of the charts
  refine Work.Normality.HasIntegrallyClosedStalks.of_isAffineOpen_cover
    (X := (Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n).left)
    (fun i : {U : (Work.SymQuot.symData C m).Chart // Nonempty U.1} ×
        {T : (Work.SymQuot.symData C n).Chart // Nonempty T.1} =>
      symChartOpen C m n i.1.1 i.2.1) ?_ ?_ ?_ ?_ x
  · rintro ⟨⟨U, _⟩, ⟨T, _⟩⟩
    exact symChartOpen_isAffineOpen C m n U T
  · intro z
    obtain ⟨U, u, hu⟩ := (Work.SymQuot.symData C m).chartι_jointly_surjective
      (pullback.fst (Work.SymQuot.Sym C m).hom (Work.SymQuot.Sym C n).hom z)
    obtain ⟨T, t, ht⟩ := (Work.SymQuot.symData C n).chartι_jointly_surjective
      (pullback.snd (Work.SymQuot.Sym C m).hom (Work.SymQuot.Sym C n).hom z)
    have hUne : Nonempty U.1 := by
      obtain ⟨w, _⟩ := Work.SymQuot.Chart.chartMap_surjective (Work.SymQuot.symData C m).action
        U.2.1 U.2.2 u
      exact ⟨w.1, w.2⟩
    have hTne : Nonempty T.1 := by
      obtain ⟨w, _⟩ := Work.SymQuot.Chart.chartMap_surjective (Work.SymQuot.symData C n).action
        T.2.1 T.2.2 t
      exact ⟨w.1, w.2⟩
    exact ⟨(⟨U, hUne⟩, ⟨T, hTne⟩),
      (symChartOpen_mem_iff C m n U T z).mpr ⟨⟨u, hu⟩, ⟨t, ht⟩⟩⟩
  · rintro ⟨⟨U, hU⟩, ⟨T, hT⟩⟩
    haveI : IsDomain (chartInv C m U ⊗[K] chartInv C n T) := (hkey ⟨U, hU⟩ ⟨T, hT⟩).2
    obtain ⟨e⟩ := symChartOpen_sections C m n U T
    exact Function.Injective.isDomain e.toRingHom e.injective
  · rintro ⟨⟨U, hU⟩, ⟨T, hT⟩⟩
    haveI : IsIntegrallyClosed (chartInv C m U ⊗[K] chartInv C n T) := (hkey ⟨U, hU⟩ ⟨T, hT⟩).1
    obtain ⟨e⟩ := symChartOpen_sections C m n U T
    exact IsIntegrallyClosed.of_equiv e.symm

end Main

end Work.CurveFacts
