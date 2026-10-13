import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Setup
import Submission.Work.DSEQ0.eulerCharDefs
import Submission.Work.DSEQ0.cechZ_homology_zero_iso_gamma
import Submission.Work.DSEQ0.phi_injective
import Submission.Work.DSEQ0.homology_extendScalars
import Submission.Work.DSEQ0.eulerChar_eq_homology_finrank
import Submission.Work.DSEQ0.curryComplexZ_homology_isZero
import Submission.Work.DSEQ0.cechZAway_iso_curry_ext
import Submission.Work.DSEQ0.finite_extendScalars_obj
import Submission.Work.DSEQ0.finrank_extendScalars_obj
import Submission.Work.DSEQ0.isZero_extendScalars_away
import Submission.Work.DSEQ0.finite_homology
import Submission.Work.DSEQ0.nontrivial_extendScalars_fractionRing

/-!
# The Euler characteristic of a bounded finite free model of the Čech complex is nonzero

This file proves `Work.DSEQ0.eulerChar_ne_zero`:

for a Noetherian domain `A`, a proper, surjective, generically finite morphism
`f : X ⟶ Spec A`, a finite affine cover `U` of `X`, and a bounded complex `F` of finite free
`A`-modules quasi-isomorphic to the Čech complex `DSMap.cechZ A X f U`, the Euler characteristic
`Σ_{i ∈ [lo,hi]} (-1)^i rk (F^i)` is nonzero.

## Proof outline

Let `g ≠ 0` be an element such that `f` is finite over `D(g) ∈ Spec A` (it exists because `f` is
generically finite), and let `W = f⁻¹D(g) ⊆ X`, an affine open.

1. **The Čech complex localised at `g` is a resolution** (`cechZAway_homology_isZero`): the base
   change `Č(U;𝒪_X) ⊗_A A_g` is the Čech complex of the affine scheme `W` along the cover
   `{W ⊓ U i}`, hence has no homology outside degree `0`.  This uses
   `Work.DSEQ0.cechZAway_iso_curry_ext` (the identification of the localised complex with the
   Čech complex of `W`) and `Work.DSEQ0.curryComplexZ_homology_isZero` (the affine resolution).
2. **Euler–Poincaré over the field `K = Frac A`** (`Work.DSEQ0.eulerChar_eq_homology_finrank`).
   Base change along `A → K` (flat) computes the homology
   (`Work.DSEQ0.homology_extendScalars`), and by step 1 only `H⁰` survives.
3. **The surviving term is `K ⊗_A Γ(X,⊤) ≠ 0`**: `H⁰(Č) ≅ Γ(X,⊤)`
   (`Work.DSEQ0.cechZ_homology_zero_iso_gamma`) and `A → Γ(X,⊤)` is injective because `f` is
   surjective (`Work.DSEQ0.phi_injective`).
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct ChangeOfRings

namespace Work.DSEQ0

universe a u

/-! ## Elementary helpers -/

section Helpers

/-- A module over a ring is zero (as an object) if and only if it is a subsingleton type. -/
theorem isZero_moduleCat_iff_subsingleton {R : Type u} [Ring R] (M : ModuleCat.{u} R) :
    IsZero M ↔ Subsingleton M := by
  rw [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    refine ⟨fun x y => ?_⟩
    have h2 : ∀ z : M, ((𝟙 M : M ⟶ M)).hom z = z := fun z => rfl
    have h3 : ∀ z : M, ((0 : M ⟶ M)).hom z = 0 := fun z => rfl
    have h1 := congrArg (fun (f : M ⟶ M) => f.hom x) h
    rw [h2 x, h3 x] at h1
    have h4 : y = 0 := by
      have hh := congrArg (fun (f : M ⟶ M) => f.hom y) h
      rw [h2 y, h3 y] at hh
      exact hh
    rw [h1, h4]
  · intro h
    ext x
    exact h.elim _ _

variable {A : Type a} [CommRing A] {X : AlgebraicGeometry.Scheme.{a}}
  {f : X ⟶ AlgebraicGeometry.Spec (.of A)}

/-- The open `f ⁻¹ᵁ D(g)` is affine when `f` is finite over `D(g)`. -/
theorem isAffineOpen_awayOpen {g : A}
    (h : IsFinite (f ∣_ (PrimeSpectrum.basicOpen g : (AlgebraicGeometry.Spec (.of A)).Opens))) :
    IsAffineOpen (awayOpen A X f g) := by
  have hgoal : awayOpen A X f g
      = f ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (AlgebraicGeometry.Spec (.of A)).Opens) := rfl
  rw [hgoal]
  set U₀ : (AlgebraicGeometry.Spec (.of A)).Opens := PrimeSpectrum.basicOpen g with hU₀
  have hfin : IsFinite (f ∣_ U₀) := h
  haveI : IsFinite (f ∣_ U₀) := hfin
  haveI : IsAffineHom (f ∣_ U₀) := ⟨hfin.isAffine_preimage⟩
  have hU : IsAffineOpen U₀ := hU₀ ▸ IsAffineOpen.Spec_basicOpen (R := CommRingCat.of A) g
  haveI : IsAffine U₀ := hU
  exact isAffine_of_isAffineHom (f ∣_ U₀)

/-- The scheme `X` is separated over `Spec ℤ` when it is separated over an affine base. -/
theorem isSeparated_scheme [IsSeparated f] : Scheme.IsSeparated X := ⟨by
  rw [← terminal.comp_from f]
  exact (IsSeparated.comp_iff (f := f)
    (g := terminal.from (AlgebraicGeometry.Spec (CommRingCat.of A)))).mpr inferInstance⟩

/-- Finite intersections of affine opens of a scheme separated over an affine base are affine. -/
theorem isAffineOpen_iInf_cover [IsSeparated f] {ι : Type a} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ) (y : Fin (n + 1) → ι) :
    IsAffineOpen (⨅ a, U (y a)) := by
  haveI := isSeparated_scheme (X := X) (f := f)
  exact IsAffineOpen.iInf (fun a => hU (y a))

end Helpers

/-! ## The crux: the Čech complex localised at `g` is a resolution -/

/-- **The Čech complex of `X` localised at `g` has no homology outside degree `0`.**

For `g ≠ 0` such that `f` is finite over `D(g)`, the base change of the Čech complex along
`A → A_g = Localization.Away g` is the Čech complex of the affine open scheme `W = f⁻¹D(g)`
along the cover `{W ⊓ U i}`, and an affine scheme has no higher cohomology: the complex is a
resolution of its ring of global sections. -/
theorem cechZAway_homology_isZero {A : Type a} [CommRing A] [IsDomain A]
    (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (.of A)) [IsProper f]
    (hs : Function.Surjective f) {ι : Type a} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (g : A) (hg0 : g ≠ 0)
    (hgf : IsFinite (f ∣_ (PrimeSpectrum.basicOpen g : (AlgebraicGeometry.Spec (.of A)).Opens))) :
    ∀ i : ℤ, i ≠ 0 → IsZero ((cechZAway A X f U g).homology i) := by
  haveI hsep : IsSeparated f := inferInstance
  set W : X.Opens := awayOpen A X f g with hW
  have hWaff : IsAffineOpen W := hW ▸ isAffineOpen_awayOpen (X := X) (f := f) hgf
  have hint : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (⨅ a, U (y a)) :=
    fun n y => isAffineOpen_iInf_cover (X := X) (f := f) U hU n y
  haveI := isSeparated_scheme (X := X) (f := f)
  have hinf : ∀ (n : ℕ) (y : Fin (n + 1) → ι), IsAffineOpen (W ⊓ ⨅ a, U (y a)) :=
    fun n y => IsAffineOpen.inf hWaff (hint n y)
  have hle : W ≤ ⨆ i, U i := by rw [hcov]; exact le_top
  obtain ⟨e⟩ := cechZAway_iso_curry_ext A X f U g hW hint
  intro i hi
  have hcur : IsZero ((curryComplexZ A X f W U).homology i) := by
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · exact ShortComplex.isZero_homology_of_isZero_X₂
        (S := (curryComplexZ A X f W U).sc i)
        (HomologicalComplex.isZero_extend_X
          ((CategoryTheory.cechComplexFunctor U).obj (curryPresheaf A X f W))
          ComplexShape.embeddingUpNat i (fun j => by
            rw [ComplexShape.embeddingUpNat_f]
            omega))
    · exact curryComplexZ_homology_isZero A X f hWaff U hinf hle i hgt
  have h2 : IsZero ((HomologicalComplex.homology
      ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away g)))
        (ComplexShape.up ℤ)).obj (curryComplexZ A X f W U)) i)) := by
    obtain ⟨iso⟩ := homology_extendScalars A (Localization.Away g) (curryComplexZ A X f W U) i
    exact IsZero.of_iso (Functor.map_isZero _ hcur) iso
  exact IsZero.of_iso h2 (HomologicalComplex.homologyMapIso e i)

/-! ## The main theorem -/

/-- **The Euler characteristic of a bounded finite free model of the Čech complex is nonzero.**

Over a Noetherian domain `A`, for `f : X ⟶ Spec A` proper, surjective and generically finite, any
bounded complex `F` of finite free `A`-modules quasi-isomorphic to the Čech complex of a finite
affine cover of `X` has nonzero Euler characteristic: it is the *generic degree*. -/
theorem eulerChar_ne_zero (A : Type a) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (X : AlgebraicGeometry.Scheme.{a}) (f : X ⟶ AlgebraicGeometry.Spec (.of A))
    [AlgebraicGeometry.IsProper f] (hs : Function.Surjective f) (hg : DSMap.IsGenFinite A f)
    {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i))
    (hcov : ⨆ i, U i = ⊤)
    (F : CochainComplex (ModuleCat.{a} A) ℤ) (lo hi : ℤ)
    (hbdd : ∀ i : ℤ, i < lo ∨ hi < i → CategoryTheory.Limits.IsZero (F.X i))
    (hfin : ∀ i : ℤ, Module.Finite A ↥(F.X i)) (hfree : ∀ i : ℤ, Module.Free A ↥(F.X i))
    (q : F ⟶ DSMap.cechZ A X f U) (hq : QuasiIso q) :
    (∑ i ∈ Finset.Icc lo hi, (-1 : ℤ) ^ i.natAbs * (Module.finrank A ↥(F.X i) : ℤ)) ≠ 0 := by
  classical
  obtain ⟨g, hg0, hgf⟩ := hg
  haveI hfinA : ∀ i : ℤ, Module.Finite A ↥(F.X i) := hfin
  have hcruxAg := cechZAway_homology_isZero X f hs U hU hcov g hg0 hgf
  let K := FractionRing A
  let EK : ModuleCat.{a} A ⥤ ModuleCat.{a} K := ModuleCat.extendScalars (algebraMap A K)
  let FK : CochainComplex (ModuleCat.{a} K) ℤ :=
    (Functor.mapHomologicalComplex EK (ComplexShape.up ℤ)).obj F
  let ČK : CochainComplex (ModuleCat.{a} K) ℤ :=
    (Functor.mapHomologicalComplex EK (ComplexShape.up ℤ)).obj (DSMap.cechZ A X f U)
  haveI hfinK : ∀ i : ℤ, Module.Finite K ↥(FK.X i) :=
    fun i => finite_extendScalars_obj (algebraMap A K) (F.X i)
  -- (1) the base changed Čech complex has no homology outside degree 0
  have hČK : ∀ i : ℤ, i ≠ 0 → IsZero (ČK.homology i) := by
    intro i hi
    have h0 : IsZero (EK.obj ((DSMap.cechZ A X f U).homology i)) := by
      refine isZero_extendScalars_away A g hg0 ((DSMap.cechZ A X f U).homology i) ?_
      exact IsZero.of_iso (hcruxAg i hi)
        (homology_extendScalars A (Localization.Away g) (DSMap.cechZ A X f U) i).some.symm
    exact IsZero.of_iso h0 (homology_extendScalars A K (DSMap.cechZ A X f U) i).some
  -- (2) hence the homology of `K ⊗ F` vanishes outside degree 0 as well
  have hFKzero : ∀ i : ℤ, i ≠ 0 → IsZero (FK.homology i) := by
    intro i hi
    have hqi : F.homology i ≅ (DSMap.cechZ A X f U).homology i := isoOfQuasiIsoAt q i
    have h2 : IsZero (EK.obj (F.homology i)) :=
      IsZero.of_iso
        (IsZero.of_iso (hČK i hi)
          (homology_extendScalars A K (DSMap.cechZ A X f U) i).some.symm)
        (Functor.mapIso EK hqi)
    exact IsZero.of_iso h2 (homology_extendScalars A K F i).some
  -- (3) Euler–Poincaré over the field `K`
  have hbddK : ∀ i : ℤ, i < lo ∨ hi < i → IsZero (FK.X i) :=
    fun i h => Functor.map_isZero EK (hbdd i h)
  have hEP := eulerChar_eq_homology_finrank K FK lo hi hbddK
  have hS : (∑ i ∈ Finset.Icc lo hi, (-1 : ℤ) ^ i.natAbs * (Module.finrank A ↥(F.X i) : ℤ))
      = ∑ i ∈ Finset.Icc lo hi,
          (-1 : ℤ) ^ i.natAbs * (Module.finrank K ↥(FK.homology i) : ℤ) := by
    rw [← hEP]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (-1 : ℤ) ^ i.natAbs * (Module.finrank A ↥(F.X i) : ℤ)
      = (-1 : ℤ) ^ i.natAbs
        * (Module.finrank K ↥((ModuleCat.extendScalars (algebraMap A K)).obj (F.X i)) : ℤ)
    rw [finrank_extendScalars_obj (M := F.X i)]
  have hterm : ∀ i ∈ Finset.Icc lo hi, i ≠ 0 →
      (-1 : ℤ) ^ i.natAbs * (Module.finrank K ↥(FK.homology i) : ℤ) = 0 := by
    intro i _ hi0
    haveI : Subsingleton ↥(FK.homology i) :=
      (isZero_moduleCat_iff_subsingleton _).1 (hFKzero i hi0)
    rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]
  -- the ring of global sections, as an `A`-algebra
  letI : Algebra A (GammaTop X) := (DSMap.phi A X f).toAlgebra
  have hφ : ∀ a : A, algebraMap A (GammaTop X) a = DSMap.phi A X f a := fun a => rfl
  have hinjalg : Function.Injective (Algebra.linearMap A (GammaTop X)) := phi_injective A X f hs
  by_cases h0mem : (0 : ℤ) ∈ Finset.Icc lo hi
  · have hsum : (∑ i ∈ Finset.Icc lo hi,
        (-1 : ℤ) ^ i.natAbs * (Module.finrank K ↥(FK.homology i) : ℤ))
        = (Module.finrank K ↥(FK.homology 0) : ℤ) := by
      have h := Finset.sum_eq_single (s := Finset.Icc lo hi)
        (f := fun i => (-1 : ℤ) ^ i.natAbs * (Module.finrank K ↥(FK.homology i) : ℤ)) 0
        (fun b hb hb0 => hterm b hb hb0) (fun h => absurd h0mem h)
      simpa using h
    have hNT : Nontrivial ↥(EK.obj (ModuleCat.of A (GammaTop X))) :=
      nontrivial_extendScalars_fractionRing (A := A) (GammaTop X) hinjalg
    haveI : Module.Finite K ↥(FK.homology 0) := finite_homology FK 0
    have hpos : (Module.finrank K ↥(FK.homology 0) : ℤ) ≠ 0 := by
      obtain ⟨eΓ⟩ := cechZ_homology_zero_iso_gamma A X f U hcov hφ
      have e1 : FK.homology 0 ≅ EK.obj (F.homology 0) := (homology_extendScalars A K F 0).some
      have e2 : EK.obj (F.homology 0) ≅ EK.obj ((DSMap.cechZ A X f U).homology 0) :=
        Functor.mapIso EK (isoOfQuasiIsoAt q 0)
      have e3 : EK.obj ((DSMap.cechZ A X f U).homology 0)
          ≅ EK.obj (ModuleCat.of A (GammaTop X)) :=
        Functor.mapIso EK (LinearEquiv.toModuleIso eΓ)
      have efinal := e1.trans (e2.trans e3)
      have hright : ∀ x : ↥(EK.obj (ModuleCat.of A (GammaTop X))), efinal.hom (efinal.inv x) = x := by
        intro x
        have h := congrArg (fun (g : EK.obj (ModuleCat.of A (GammaTop X)) ⟶
            EK.obj (ModuleCat.of A (GammaTop X))) => g x) efinal.inv_hom_id
        simpa using h
      have hinj : Function.Injective (fun x => efinal.inv x) := by
        intro x y hxy
        have h1 : efinal.hom (efinal.inv x) = efinal.hom (efinal.inv y) := congrArg _ hxy
        rwa [hright x, hright y] at h1
      haveI : Nontrivial ↥(FK.homology 0) := Function.Injective.nontrivial hinj
      have h : 0 < Module.finrank K ↥(FK.homology 0) := Module.finrank_pos
      omega
    intro hcon
    exact hpos (by rw [← hsum, ← hS]; exact hcon)
  · exfalso
    have hX0 : IsZero (F.X 0) := by
      have hsplit : lo > 0 ∨ hi < 0 := by
        by_contra hcon
        push_neg at hcon
        exact h0mem (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rcases hsplit with h | h
      · exact hbdd 0 (Or.inl h)
      · exact hbdd 0 (Or.inr h)
    have hH0 : IsZero (F.homology 0) :=
      ShortComplex.isZero_homology_of_isZero_X₂ (S := F.sc 0) hX0
    have hČ0 : IsZero ((DSMap.cechZ A X f U).homology 0) :=
      IsZero.of_iso hH0 (isoOfQuasiIsoAt q 0).symm
    obtain ⟨e⟩ := cechZ_homology_zero_iso_gamma A X f U hcov hφ
    have hsub : Subsingleton (GammaTop X) := by
      refine ⟨fun x y => ?_⟩
      have h1 : Subsingleton ↥((DSMap.cechZ A X f U).homology 0) :=
        (isZero_moduleCat_iff_subsingleton _).1 hČ0
      exact e.symm.injective (Subsingleton.elim (e.symm x) (e.symm y))
    have hsubA : Subsingleton A := ⟨fun x y => hinjalg (Subsingleton.elim _ _)⟩
    exact one_ne_zero (Subsingleton.elim (1 : A) 0)

end Work.DSEQ0
