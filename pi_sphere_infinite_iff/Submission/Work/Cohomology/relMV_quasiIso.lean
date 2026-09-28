import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.RelMVDefs
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.smallLift_cov
import Submission.Work.Cohomology.smallChains_homology_iso
import Submission.Work.Cohomology.localHomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- `U ∩ A` viewed as a subset of the subspace `A`. -/
abbrev interAU (U A : Set X) : Set A := setOf (fun x : A => (x : X) ∈ U)

/-- The small simplices of the subspace `A` for the cover induced by `(U, V)`. -/
abbrev smallSubcomplexA (U V A : Set X) : (TopCat.toSSet.obj (TopCat.of A)).Subcomplex :=
  smallSubcomplex (X := TopCat.of A) (interAU U A) (interAU V A)

/-- The small simplices of the subspace `A`, as a simplicial set. -/
abbrev smallSSetA (U V A : Set X) : SSet :=
  smallSSet (X := TopCat.of A) (interAU U A) (interAU V A)

/-- The small chains of the subspace `A` for the cover induced by `(U, V)`. -/
abbrev smallChainsA (U V A : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  smallChains (X := TopCat.of A) (interAU U A) (interAU V A)

/-- The inclusion of the singular simplices of `A` is a monomorphism of simplicial sets. -/
instance mono_toSSet_map_subtypeIncl (X : TopCat) (A : Set X) :
    Mono (TopCat.toSSet.map (subtypeIncl X A)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b h
  exact injective_toSSet_map (subtypeIncl X A) (subtypeIncl_injective X A) (Opposite.unop n).len h

/-- Every small-in-`A` simplex lies in the range of the map `Sing(A) ⟶ Sing(X)`. -/
theorem smallInSubcomplex_le_range (U V A : Set X) :
    smallInSubcomplex U V A ≤ Subfunctor.range (TopCat.toSSet.map (subtypeIncl X A)) := by
  intro n σ hσ
  rw [Subfunctor.range_obj]
  obtain ⟨a, ha⟩ := exists_map_inclUX_of_range_subset A n σ hσ.2
  refine ⟨a, ?_⟩
  rw [← ha]
  congr 1

/-- **The lift of a small-in-`A` simplex to a simplex of `A`.**  A small simplex whose image lies
in `A` determines a simplex of `A` (its corestriction), and this assignment is simplicial. -/
def smallInLift (U V A : Set X) :
    smallInSSet U V A ⟶ TopCat.toSSet.obj (TopCat.of A) :=
  Subfunctor.homOfLe (smallInSubcomplex_le_range U V A) ≫
    (asIso (Subfunctor.toRange (TopCat.toSSet.map (subtypeIncl X A)))).inv

/-- `smallInLift` is a section of the map `Sing(A) ⟶ Sing(X)` restricted to the small-in-`A`
simplices. -/
theorem smallInLift_comp (U V A : Set X) :
    smallInLift U V A ≫ TopCat.toSSet.map (subtypeIncl X A) = (smallInSubcomplex U V A).ι := by
  rw [smallInLift, Category.assoc]
  set e := asIso (Subfunctor.toRange (TopCat.toSSet.map (subtypeIncl X A))) with he
  have h2 : e.hom ≫ (Subfunctor.range (TopCat.toSSet.map (subtypeIncl X A))).ι
      = TopCat.toSSet.map (subtypeIncl X A) := by
    rw [he]; exact Subfunctor.toRange_ι _
  have h : e.inv ≫ TopCat.toSSet.map (subtypeIncl X A)
      = (Subfunctor.range (TopCat.toSSet.map (subtypeIncl X A))).ι := by
    calc e.inv ≫ TopCat.toSSet.map (subtypeIncl X A)
        = e.inv ≫ (e.hom ≫ (Subfunctor.range (TopCat.toSSet.map (subtypeIncl X A))).ι) := by
            rw [h2]
      _ = (e.inv ≫ e.hom) ≫ (Subfunctor.range (TopCat.toSSet.map (subtypeIncl X A))).ι := by
            rw [Category.assoc]
      _ = (Subfunctor.range (TopCat.toSSet.map (subtypeIncl X A))).ι := by
            rw [Iso.inv_hom_id, Category.id_comp]
  rw [h]
  exact Subfunctor.homOfLe_ι _

/-- The underlying simplex of `smallInLift` maps to the original simplex of `X`. -/
theorem smallInLift_app_comp (U V A : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (smallInSSet U V A).obj n) :
    (TopCat.toSSet.map (subtypeIncl X A)).app n ((smallInLift U V A).app n σ) = σ.1 := by
  have h := congrArg (fun (g : smallInSSet U V A ⟶ TopCat.toSSet.obj X) => g.app n σ)
    (smallInLift_comp U V A)
  simpa [NatTrans.comp_app] using h

/-- The range of `smallInLift` is the subcomplex of small simplices of the subspace `A`. -/
theorem range_smallInLift_le (U V A : Set X) :
    Subfunctor.range (smallInLift U V A) ≤ smallSubcomplexA U V A := by
  intro n τ hτ
  rw [Subfunctor.range_obj] at hτ
  obtain ⟨σ, rfl⟩ := hτ
  have hcoe : ∀ z : stdSimplex ℝ (Fin (n.unop.len + 1)),
      ((TopCat.toSSetObjEquivT (TopCat.of A) n ((smallInLift U V A).app n σ)) z : X)
        = (TopCat.toSSetObjEquivT X n σ.1) z := by
    intro z
    rw [← smallInLift_app_comp U V A n σ, toSSetObjEquiv_map_apply]
    rfl
  rcases σ.2.1 with hU | hV
  · left
    rintro z ⟨w, rfl⟩
    show ((TopCat.toSSetObjEquivT (TopCat.of A) n ((smallInLift U V A).app n σ)) w : X) ∈ U
    rw [hcoe w]
    exact hU ⟨w, rfl⟩
  · right
    rintro z ⟨w, rfl⟩
    show ((TopCat.toSSetObjEquivT (TopCat.of A) n ((smallInLift U V A).app n σ)) w : X) ∈ V
    rw [hcoe w]
    exact hV ⟨w, rfl⟩

/-- The small simplices of the subspace `A` map into the small-in-`A` simplices of `X`. -/
theorem range_smallSub_le (U V A : Set X) :
    Subfunctor.range ((smallSubcomplexA U V A).ι
        ≫ TopCat.toSSet.map (subtypeIncl X A)) ≤ smallInSubcomplex U V A := by
  intro n σ hσ
  rw [Subfunctor.range_obj] at hσ
  obtain ⟨τ, rfl⟩ := hσ
  have hcoe : ∀ z : stdSimplex ℝ (Fin (n.unop.len + 1)),
      (TopCat.toSSetObjEquivT X n ((TopCat.toSSet.map (subtypeIncl X A)).app n τ.1)) z
        = ((TopCat.toSSetObjEquivT (TopCat.of A) n τ.1) z : X) := by
    intro z
    rw [toSSetObjEquiv_map_apply]
    rfl
  refine ⟨?_, ?_⟩
  · rcases τ.2 with hU | hV
    · left
      rintro z ⟨w, rfl⟩
      show (TopCat.toSSetObjEquivT X n ((TopCat.toSSet.map (subtypeIncl X A)).app n τ.1)) w ∈ U
      rw [hcoe w]
      exact hU ⟨w, rfl⟩
    · right
      rintro z ⟨w, rfl⟩
      show (TopCat.toSSetObjEquivT X n ((TopCat.toSSet.map (subtypeIncl X A)).app n τ.1)) w ∈ V
      rw [hcoe w]
      exact hV ⟨w, rfl⟩
  · rintro z ⟨w, rfl⟩
    show ((TopCat.toSSetObjEquivT (TopCat.of A) n τ.1) w : X) ∈ A
    exact (TopCat.toSSetObjEquivT (TopCat.of A) n τ.1 w).2

/-- The canonical map from the small-in-`A` simplices to the small simplices of the subspace
`A`. -/
def smallInToSmallA (U V A : Set X) :
    smallInSSet U V A ⟶ smallSSetA U V A :=
  Subfunctor.lift (smallInLift U V A) (range_smallInLift_le U V A)

/-- The canonical map from the small simplices of the subspace `A` to the small-in-`A` simplices
of `X`. -/
def smallToSmallInA (U V A : Set X) :
    smallSSetA U V A ⟶ smallInSSet U V A :=
  Subfunctor.lift ((smallSubcomplexA U V A).ι ≫ TopCat.toSSet.map (subtypeIncl X A))
    (range_smallSub_le U V A)

theorem smallInToSmallA_comp (U V A : Set X) :
    smallInToSmallA U V A ≫ (smallSubcomplexA U V A).ι = smallInLift U V A :=
  Subfunctor.lift_ι _ _

theorem smallToSmallInA_comp (U V A : Set X) :
    smallToSmallInA U V A ≫ (smallInSubcomplex U V A).ι
      = (smallSubcomplexA U V A).ι ≫ TopCat.toSSet.map (subtypeIncl X A) :=
  Subfunctor.lift_ι _ _

theorem smallToSmallInA_comp_smallInLift (U V A : Set X) :
    smallToSmallInA U V A ≫ smallInLift U V A = (smallSubcomplexA U V A).ι := by
  apply (cancel_mono (TopCat.toSSet.map (subtypeIncl X A))).1
  rw [Category.assoc, smallInLift_comp, smallToSmallInA_comp]

/-- **The small-in-`A` simplices are the small simplices of the subspace `A`.** -/
theorem isIso_smallInToSmallA (U V A : Set X) : IsIso (smallInToSmallA U V A) := by
  refine IsIso.mk ⟨smallToSmallInA U V A, ?_, ?_⟩
  · apply (cancel_mono (smallInSubcomplex U V A).ι).1
    rw [Category.assoc, smallToSmallInA_comp, ← Category.assoc, smallInToSmallA_comp,
      smallInLift_comp, Category.id_comp]
  · apply (cancel_mono (smallSubcomplexA U V A).ι).1
    rw [Category.assoc, smallInToSmallA_comp, smallToSmallInA_comp_smallInLift, Category.id_comp]

/-- The chain map from the small chains lying in `A` to the singular chains of the subspace `A`. -/
abbrev smallInToSingA (U V A : Set X) :
    smallInChains U V A ⟶ singularChains ℤ (TopCat.of A) :=
  SSet.chainComplexMap (smallInLift U V A) (ModuleCat.of ℤ ℤ)

/-- The map `smallInToSingA` followed by the inclusion `C_*(A) ⟶ C_*(X)` is the inclusion of the
small-in-`A` chains. -/
theorem smallInToSingA_comp (U V A : Set X) :
    smallInToSingA U V A ≫ inclChains X A = smallInToSmall U V A ≫ smallToSing U V := by
  show SSet.chainComplexMap (smallInLift U V A) (ModuleCat.of ℤ ℤ)
      ≫ SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of ℤ ℤ)
    = SSet.chainComplexMap (Subfunctor.homOfLe (smallInSubcomplex_le U V A)) (ModuleCat.of ℤ ℤ)
      ≫ SSet.chainComplexMap (smallSubcomplex U V).ι (ModuleCat.of ℤ ℤ)
  rw [← Functor.map_comp, ← Functor.map_comp, smallInLift_comp, Subfunctor.homOfLe_ι]

/-- The chain-level factorisation of `smallInToSingA` through the small chains of `A`. -/
theorem smallInToSingA_eq (U V A : Set X) :
    smallInToSingA U V A
      = SSet.chainComplexMap (smallInToSmallA U V A) (ModuleCat.of ℤ ℤ)
        ≫ smallToSing (X := TopCat.of A) (interAU U A) (interAU V A) := by
  show SSet.chainComplexMap (smallInLift U V A) (ModuleCat.of ℤ ℤ) = _
  rw [← smallInToSmallA_comp U V A]
  exact Functor.map_comp (self := ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)))
    (smallInToSmallA U V A) (smallSubcomplexA U V A).ι

/-- The small-in-`A` chains are quasi-isomorphic to the singular chains of `A`. -/
theorem isIso_smallInToSingA (U V A : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (smallInToSingA U V A) n) := by
  rw [smallInToSingA_eq U V A, HomologicalComplex.homologyMap_comp]
  haveI : IsIso (smallInToSmallA U V A) := isIso_smallInToSmallA U V A
  haveI h0 : IsIso (SSet.chainComplexMap (smallInToSmallA U V A) (ModuleCat.of ℤ ℤ)) :=
    Functor.map_isIso ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
      (smallInToSmallA U V A)
  haveI h1 : IsIso (HomologicalComplex.homologyMap
      (SSet.chainComplexMap (smallInToSmallA U V A) (ModuleCat.of ℤ ℤ)) n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      (SSet.chainComplexMap (smallInToSmallA U V A) (ModuleCat.of ℤ ℤ))
  have hU' : IsOpen (interAU U A) := hU.preimage continuous_subtype_val
  have hV' : IsOpen (interAU V A) := hV.preimage continuous_subtype_val
  have hcov' : interAU U A ∪ interAU V A = Set.univ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      rcases Set.eq_univ_iff_forall.mp hcov (x : X) with h | h
      · exact Or.inl h
      · exact Or.inr h
  haveI h2 : IsIso (HomologicalComplex.homologyMap
      (smallToSing (X := TopCat.of A) (interAU U A) (interAU V A)) n) :=
    smallChains_homology_iso (X := TopCat.of A) (interAU U A) (interAU V A) hU' hV' hcov' n
  exact inferInstance

/-! ## Injectivity of the inclusion of the small-in-`A` chains -/

/-- The projection of the small chains onto the small-in-`A` chains: a small simplex is sent to
itself if its image lies in `A`, and to `0` otherwise. -/
noncomputable def smallInProj (U V A : Set X) (n : ℕ) :
    (smallChains U V).X n ⟶ (smallInChains U V A).X n := by
  classical
  exact (smallSSet U V).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n |>.desc
    (Cofan.mk _ (fun σ : (smallSSet U V) _⦋n⦌ =>
      if h : IsSmallIn U V A σ.1 then (smallInSSet U V A).ιChainComplex ⟨σ.1, h⟩ else 0))

/-- The inclusion of the small-in-`A` chains is degreewise injective. -/
theorem smallInToSmall_f_injective (U V A : Set X) (n : ℕ) :
    Function.Injective ((smallInToSmall U V A).f n).hom := by
  classical
  have hfac : ∀ σ : (smallSSet U V) _⦋n⦌,
      (smallSSet U V).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ smallInProj U V A n
        = if h : IsSmallIn U V A σ.1 then
            (smallInSSet U V A).ιChainComplex ⟨σ.1, h⟩ else 0 :=
    fun σ => Cofan.IsColimit.fac _ _ _
  have hcomp : (smallInToSmall U V A).f n ≫ smallInProj U V A n
      = 𝟙 ((smallInChains U V A).X n) := by
    apply SSet.chainComplex_hom_ext (X := smallInSSet U V A) (R := ModuleCat.of ℤ ℤ) (n := n)
    intro x
    have h1 : (smallInSSet U V A).ιChainComplex (R := ModuleCat.of ℤ ℤ) x
        ≫ (smallInToSmall U V A).f n
        = (smallSSet U V).ιChainComplex (R := ModuleCat.of ℤ ℤ) ⟨x.1, x.2.1⟩ := by
      have h := SSet.ι_chainComplexMap_f
        (f := Subfunctor.homOfLe (smallInSubcomplex_le U V A)) (R := ModuleCat.of ℤ ℤ)
        (X := smallInSSet U V A) (Y := smallSSet U V) (n := n) x
      simpa [smallInToSmall] using h
    rw [← Category.assoc, h1, Category.comp_id, hfac,
      dif_pos (show IsSmallIn U V A (⟨x.1, x.2.1⟩ : (smallSSet U V) _⦋n⦌).1 from x.2)]
    congr 1
  have h2 : (smallInProj U V A n).hom.comp ((smallInToSmall U V A).f n).hom = LinearMap.id := by
    have hh := congrArg ModuleCat.Hom.hom hcomp
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at hh
    exact hh
  intro x y hxy
  have hgen : ∀ z, (smallInProj U V A n).hom (((smallInToSmall U V A).f n).hom z) = z := by
    intro z
    have hz := LinearMap.congr_fun h2 z
    rwa [LinearMap.comp_apply, LinearMap.id_apply] at hz
  rw [← hgen x, hxy, hgen y]

/-- The inclusion of the small-in-`A` chains into the small chains is a monomorphism. -/
theorem mono_smallInToSmall_aux (U V A : Set X) : Mono (smallInToSmall U V A) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [ModuleCat.mono_iff_injective]
  exact smallInToSmall_f_injective U V A n

/-- **The relative small chains compute relative singular homology.**

For an open cover `U ∪ V = X` of a topological space and an arbitrary subset `A ⊆ X`, the natural
comparison map from the relative *small* chains of the pair `(X, A)` to the relative singular
chains is a quasi-isomorphism, and it is compatible with the two projections. -/
theorem relMV_quasiIso (X : TopCat) (A U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    ∃ (phi : Work.Cohomology.relSmallTop U V A ⟶ Work.Cohomology.relChains X A),
      (∀ n : ℕ, CategoryTheory.IsIso (HomologicalComplex.homologyMap phi n)) ∧
      CategoryTheory.CategoryStruct.comp
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.smallInToSmall U V A)) phi
        = CategoryTheory.CategoryStruct.comp (Work.Cohomology.smallToSing U V)
            (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A)) := by
  let S₁ : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (smallInToSmall U V A) (cokernel.π (smallInToSmall U V A))
      (cokernel.condition (smallInToSmall U V A))
  have hS₁ : S₁.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (smallInToSmall U V A))
      (mono_smallInToSmall_aux U V A) inferInstance
  have hzero : smallInToSmall U V A ≫ (smallToSing U V ≫ cokernel.π (inclChains X A)) = 0 := by
    rw [← Category.assoc, ← smallInToSingA_comp U V A, Category.assoc, cokernel.condition,
      comp_zero]
  let phi : relSmallTop U V A ⟶ relChains X A :=
    cokernel.desc (smallInToSmall U V A) (smallToSing U V ≫ cokernel.π (inclChains X A)) hzero
  have hphi : cokernel.π (smallInToSmall U V A) ≫ phi
      = smallToSing U V ≫ cokernel.π (inclChains X A) :=
    cokernel.π_desc _ _ _
  have hcomm1 : smallInToSingA U V A ≫ (hPairShort X A).f = S₁.f ≫ smallToSing U V := by
    show smallInToSingA U V A ≫ inclChains X A = smallInToSmall U V A ≫ smallToSing U V
    exact smallInToSingA_comp U V A
  have hcomm2 : smallToSing U V ≫ (hPairShort X A).g = S₁.g ≫ phi := by
    show smallToSing U V ≫ cokernel.π (inclChains X A) = cokernel.π (smallInToSmall U V A) ≫ phi
    rw [hphi]
  let ψ : S₁ ⟶ hPairShort X A :=
    ShortComplex.homMk (smallInToSingA U V A) (smallToSing U V) phi hcomm1 hcomm2
  have hq1 : QuasiIso ψ.τ₁ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact isIso_smallInToSingA U V A hU hV hcov i
  have hq2 : QuasiIso ψ.τ₂ := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact smallChains_homology_iso U V hU hV hcov i
  have hq3 : QuasiIso ψ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ hS₁ (hPairShort_shortExact X A) hq1 hq2
  refine ⟨phi, ?_, hphi⟩
  intro n
  have h := hq3.quasiIsoAt n
  rwa [quasiIsoAt_iff_isIso_homologyMap] at h

end

end Work.Cohomology
