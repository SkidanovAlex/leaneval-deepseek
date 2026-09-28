import Mathlib
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.isZero_dualComplex_empty

/-!
# Base-change tools for the per-cell computation

The rational cell step `Work.Serre.csrPerCell` is proved by computing **both** sides of the pair map
over `ℤ` and then base-changing to `ℚ`.  This file collects the generic comparisons:

* `Work.Serre.Csr.relChainsRHomologyIsoRat` — `H_m(X,A;ℚ) ≅ ℚ ⊗[ℤ] H_m(X,A;ℤ)`;
* `Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int` — vanishing transfers along it;
* the same two statements in the absolute case (`Work.StemsB.homologyBaseChangeRat`);
* `Work.Serre.Csr.relChainsR_homology_iso_ratUnit` — an integral identification `H_m ≅ ℤ` produces
  a rational identification `H_m ≅ ℚ`;
* `Work.Serre.Csr.isIso_of_epi_of_ratIso` — a surjective map between one-dimensional `ℚ`-vector
  spaces is an isomorphism (the criterion that upgrades the surjectivity produced by a section of
  `q` over the open half-ball to the sought isomorphism);
* `Work.Serre.Csr.nonempty_of_nonempty_homologyZeroIso` — the nonemptiness of the fibre, extracted
  from the hypothesis of rational `H₀`-connectedness.
-/

set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.Csr

noncomputable section

/-! ## Base change of relative and absolute singular homology -/

/-- **Base change of relative singular homology, `ℤ → ℚ`.** -/
theorem relChainsRHomologyIsoRat (X : TopCat) (A : Set X) (m : ℕ) :
    Nonempty ((Work.StemsB.relChainsR ℚ X A).homology m ≅
      Work.StemsB.IntRatF.obj ((Work.Cohomology.relChains X A).homology m)) := by
  haveI : PreservesFiniteLimits Work.StemsB.IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits Work.StemsB.IntRatF := inferInstance
  haveI : Work.StemsB.IntRatF.PreservesHomology := inferInstance
  obtain ⟨b⟩ := Work.StemsB.relChainsBaseChangeRat X A
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) m).mapIso b.symm
    ≪≫ (Work.StemsB.SphRat.homologyMapBaseChange Work.StemsB.IntRatF
      (Work.Cohomology.relChains X A) m).some⟩

/-- **The vanishing of relative homology transfers from `ℤ` to `ℚ`.** -/
theorem isZero_relChainsR_rat_of_isZero_int (X : TopCat) (A : Set X) (m : ℕ)
    (h : IsZero ((Work.Cohomology.relChains X A).homology m)) :
    IsZero ((Work.StemsB.relChainsR ℚ X A).homology m) := by
  obtain ⟨e⟩ := relChainsRHomologyIsoRat X A m
  exact (CategoryTheory.Functor.map_isZero Work.StemsB.IntRatF h).of_iso e

/-- **An integral identification of a relative homology group with `ℤ` gives one with `ℚ`.** -/
theorem relChainsR_homology_iso_ratUnit (X : TopCat) (A : Set X) (m : ℕ)
    (h : Nonempty ((Work.Cohomology.relChains X A).homology m ≅ ModuleCat.of ℤ ℤ)) :
    Nonempty ((Work.StemsB.relChainsR ℚ X A).homology m ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨e⟩ := h
  obtain ⟨e₂⟩ := relChainsRHomologyIsoRat X A m
  exact ⟨e₂ ≪≫ Work.StemsB.IntRatF.mapIso e ≪≫ Work.StemsB.SphRat.extendScalarsIntRatIso⟩

/-- **Base change of absolute singular homology, `ℤ → ℚ`.** -/
theorem absHomologyIsoRat (X : TopCat) (m : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℚ X).homology m ≅
      Work.StemsB.IntRatF.obj ((Work.Cohomology.singularChains ℤ X).homology m)) := by
  haveI : PreservesFiniteLimits Work.StemsB.IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits Work.StemsB.IntRatF := inferInstance
  haveI : Work.StemsB.IntRatF.PreservesHomology := inferInstance
  have hΦ : (Work.StemsB.IntRatF.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Work.Cohomology.singularChains ℤ X) ≅ Work.Cohomology.singularChains ℚ X :=
    Work.StemsB.SphRat.chainComplexBaseChange Work.StemsB.IntRatF
        (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso (TopCat.toSSet.obj X)
        Work.StemsB.SphRat.extendScalarsIntRatIso
  exact ⟨(HomologicalComplex.homologyMapIso hΦ m).symm ≪≫
    (Work.StemsB.SphRat.homologyMapBaseChange Work.StemsB.IntRatF
      (Work.Cohomology.singularChains ℤ X) m).some⟩

/-- **The vanishing of absolute homology transfers from `ℤ` to `ℚ`.** -/
theorem isZero_absHomology_rat_of_int (X : TopCat) (m : ℕ)
    (h : IsZero ((Work.Cohomology.singularChains ℤ X).homology m)) :
    IsZero ((Work.Cohomology.singularChains ℚ X).homology m) :=
  ((CategoryTheory.Functor.map_isZero Work.StemsB.IntRatF h).of_iso
    (absHomologyIsoRat X m).some)

/-! ## A surjection between one-dimensional `ℚ`-vector spaces is an isomorphism -/

/-- A surjective `ℚ`-linear endomorphism of `ℚ` is bijective. -/
theorem ratLinear_bijective_of_surjective (g : ℚ →ₗ[ℚ] ℚ) (hg : Function.Surjective g) :
    Function.Bijective g := by
  have hformula : ∀ x : ℚ, g x = x * g 1 := by
    intro x
    calc g x = g (x • (1 : ℚ)) := by rw [smul_eq_mul, mul_one]
      _ = x • g 1 := map_smul g x 1
      _ = x * g 1 := by rw [smul_eq_mul]
  refine ⟨fun a b hab => ?_, hg⟩
  obtain ⟨m, hm⟩ := hg 1
  rw [hformula] at hm
  have hg1 : g 1 ≠ 0 := fun h => by
    rw [h, mul_zero] at hm
    exact one_ne_zero hm.symm
  have hsub : (a - b) * g 1 = 0 := by
    rw [sub_mul, ← hformula a, ← hformula b, hab, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right hg1)

/-- **A surjective morphism of `ℚ`-modules between two copies of `ℚ` is an isomorphism.** -/
theorem isIso_of_epi_of_ratIso {M N : ModuleCat ℚ} (eM : M ≅ ModuleCat.of ℚ ℚ)
    (eN : N ≅ ModuleCat.of ℚ ℚ) (f : M ⟶ N) (hf : Epi f) : IsIso f := by
  haveI hfE : Epi f := hf
  set g : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ := eM.inv ≫ f ≫ eN.hom with hg
  haveI hEg : Epi g := by rw [hg]; infer_instance
  have hgs : Function.Surjective (ModuleCat.Hom.hom g) := (ModuleCat.epi_iff_surjective g).mp hEg
  have hbi := ratLinear_bijective_of_surjective (ModuleCat.Hom.hom g) hgs
  haveI : Mono g := (ModuleCat.mono_iff_injective g).mpr hbi.1
  haveI : IsIso g := isIso_of_mono_of_epi g
  have key : eM.hom ≫ g ≫ eN.inv = f := by
    rw [hg, Category.assoc, Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  haveI : IsIso (eM.hom ≫ g ≫ eN.inv) := inferInstance
  rwa [key] at this

/-! ## Nonemptiness from rational `H₀`-connectedness -/

/-- **A space whose rational `H₀` is one-dimensional is nonempty.** -/
theorem nonempty_of_nonempty_homologyZeroIso (X : TopCat)
    (h : Nonempty ((Work.Cohomology.singularChains ℚ X).homology 0 ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty X := by
  by_contra hemp
  haveI : IsEmpty X := not_nonempty_iff.mp hemp
  haveI : IsEmpty (ZerothHomotopy X) :=
    ⟨fun z => hemp (Quotient.inductionOn z (motive := fun _ => Nonempty X) (fun x => ⟨x⟩))⟩
  obtain ⟨e⟩ := h
  have hzero : IsZero (∐ (fun _ : ZerothHomotopy X => ModuleCat.of ℚ ℚ)) :=
    Work.Cohomology.isZero_coproduct_of_isEmpty _
  have hZ : IsZero (ModuleCat.of ℚ ℚ) :=
    hzero.of_iso (e.symm ≪≫ TopCat.singularHomology₀Iso X (ModuleCat.of ℚ ℚ))
  haveI : Subsingleton ℚ := ModuleCat.subsingleton_of_isZero hZ
  exact one_ne_zero (Subsingleton.elim (1 : ℚ) 0)

/-! ## Absolute homology is a homeomorphism invariant -/

/-- **A homeomorphism of spaces induces an isomorphism on singular homology over `ℤ`.** -/
theorem absHomologyIsoOfHomeo {X Y : TopCat} (e : X ≃ₜ Y) (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℤ X).homology n ≅
      (Work.Cohomology.singularChains ℤ Y).homology n) :=
  ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo e))⟩

end

end Work.Serre.Csr
