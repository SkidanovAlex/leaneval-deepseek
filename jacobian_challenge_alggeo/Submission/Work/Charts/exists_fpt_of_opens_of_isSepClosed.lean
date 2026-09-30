import Mathlib
import Submission.Work.Charts.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Charts

universe u

noncomputable section

/- A separably closed field is infinite: a finite field is perfect, and a perfect separably
closed field is algebraically closed, hence infinite. -/
open Work.GCBasics in
open CategoryTheory Limits MonoidalCategory AlgebraicGeometry in
open scoped Classical MonoidalCategory in
theorem isSepClosed_infinite (K : Type u) [Field K] [IsSepClosed K] : Infinite K := by
  by_contra h
  haveI : Finite K := not_infinite_iff_finite.mp h
  haveI : PerfectField K := PerfectField.ofFinite
  haveI : IsAlgClosed K := inferInstance
  exact h inferInstance

/- A nonzero polynomial over an infinite field does not vanish everywhere. -/
open Work.GCBasics in
open CategoryTheory Limits MonoidalCategory AlgebraicGeometry in
open scoped Classical MonoidalCategory in
theorem exists_eval_ne_zero {K : Type u} [Field K] [Infinite K] {n : ℕ}
    {g : MvPolynomial (Fin n) K} (hg : g ≠ 0) :
    ∃ a : Fin n → K, MvPolynomial.eval a g ≠ 0 := by
  by_contra h
  push Not at h
  exact hg (MvPolynomial.funext fun x => by simpa using h x)

/- Every nonempty open subset of the affine space `Spec K[X₁,…,Xₙ]` over an infinite field `K`
contains a `K`-rational point, i.e. a point of the form
`PrimeSpectrum.comap (MvPolynomial.eval a) ⊥`. -/
open Work.GCBasics in
open CategoryTheory Limits MonoidalCategory AlgebraicGeometry in
open scoped Classical MonoidalCategory in
theorem exists_comap_bot_mem_of_isOpen {K : Type u} [Field K] [Infinite K] {n : ℕ}
    {W : Set (PrimeSpectrum (MvPolynomial (Fin n) K))} (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ a : Fin n → K, PrimeSpectrum.comap (MvPolynomial.eval a) (⊥ : PrimeSpectrum K) ∈ W := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨s₀, hs₀, hxs₀, hs₀W⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hW
  obtain ⟨g₀, rfl⟩ := hs₀
  have hg₀ : g₀ ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hxs₀ (Ideal.zero_mem _)
  obtain ⟨a, ha⟩ := exists_eval_ne_zero hg₀
  refine ⟨a, hs₀W ?_⟩
  change PrimeSpectrum.comap (MvPolynomial.eval a) (⊥ : PrimeSpectrum K)
    ∈ PrimeSpectrum.basicOpen g₀
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal]
  intro h
  have hmem : MvPolynomial.eval a g₀ ∈ (⊥ : PrimeSpectrum K).asIdeal := Ideal.mem_comap.mp h
  rw [PrimeSpectrum.asIdeal_bot] at hmem
  exact ha (Ideal.mem_bot.mp hmem)

/- A nonempty smooth `K`-scheme which is locally of finite type over a separably closed field
`K` has a `K`-point.

The proof is the standard one: choose an affine open `Spec A ⊆ Y` and, by
`Algebra.IsStandardSmooth.exists_etale_mvPolynomial`, an étale morphism
`Spec A ⟶ Spec K[X₁,…,Xₙ]`, whose image is a nonempty open subscheme of the affine space (étale
morphisms are open).  Any nonempty open of the affine space over the infinite field `K` contains
a `K`-rational point, and an étale morphism over a separably closed field lifts points along
separable residue field extensions (`AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed`);
this yields a `K`-point of `Y`. -/
open Work.GCBasics in
open CategoryTheory Limits MonoidalCategory AlgebraicGeometry in
open scoped Classical MonoidalCategory in
theorem exists_fpt_of_smooth_of_nonempty {K : Type u} [Field K] [IsSepClosed K]
    (Y : Sch K) [Smooth Y.hom] [LocallyOfFiniteType Y.hom]
    (hY : Nonempty Y.left) : Nonempty (FPt Y K) := by
  classical
  haveI : Infinite K := isSepClosed_infinite K
  obtain ⟨x0⟩ := hY
  obtain ⟨U, hUaff, V, hVaff, hx0V, e, hstd⟩ :=
    (Smooth.iff_forall_exists_isStandardSmooth Y.hom).mp ‹Smooth Y.hom› x0
  have hUmem : Y.hom x0 ∈ U := e hx0V
  have hUtop : U = ⊤ := by
    refine le_antisymm le_top fun p _ => ?_
    rw [Subsingleton.elim p (Y.hom x0)]
    exact hUmem
  have eT : V ≤ Y.hom ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of K)).Opens) := fun _ _ => trivial
  have hstd' : (Y.hom.appLE ⊤ V eT).hom.IsStandardSmooth :=
    (Scheme.Hom.appLE_congr Y.hom e hUtop rfl
      (fun {R S} (φ : R ⟶ S) => φ.hom.IsStandardSmooth)).mp hstd
  let A : CommRingCat := Y.left.presheaf.obj (Opposite.op V)
  let iota : CommRingCat.of K ⟶ (Spec (CommRingCat.of K)).presheaf.obj
      (Opposite.op (⊤ : (Spec (CommRingCat.of K)).Opens)) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv
  let f' : K →+* ↥A := (Y.hom.appLE ⊤ V eT).hom.comp iota.hom
  have hf' : f'.IsStandardSmooth :=
    (RingHom.RespectsIso.cancel_left_isIso (P := @RingHom.IsStandardSmooth)
      RingHom.isStandardSmooth_respectsIso iota (Y.hom.appLE ⊤ V eT)).mpr hstd'
  obtain ⟨n, g, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hf'
  let φ : Spec A ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) K)) :=
    Spec.map (CommRingCat.ofHom g)
  have hφEtale : Etale φ := by
    rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @Etale) (Q := RingHom.Etale)]
    exact hg
  haveI : Etale φ := hφEtale
  have hφopen : IsOpen (Set.range ⇑φ) := (Scheme.Hom.isOpenMap φ).isOpen_range
  have hy0 : Nonempty (Spec A) := ⟨hVaff.isoSpec.hom ⟨x0, hx0V⟩⟩
  obtain ⟨y0⟩ := hy0
  have hWne : (Set.range (fun y : ↥(Spec A) => PrimeSpectrum.comap g y)).Nonempty :=
    ⟨PrimeSpectrum.comap g y0, y0, rfl⟩
  obtain ⟨a, ha⟩ := exists_comap_bot_mem_of_isOpen
    (W := Set.range (fun y : ↥(Spec A) => PrimeSpectrum.comap g y)) hφopen hWne
  obtain ⟨y, hy⟩ := ha
  let ev : MvPolynomial (Fin n) K →+* K := MvPolynomial.eval a
  let s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) K)) :=
    Spec.map (CommRingCat.ofHom ev)
  have hd : (default : ↥(Spec (CommRingCat.of K))) = (⊥ : PrimeSpectrum K) :=
    Subsingleton.elim _ _
  have hs_def : s (default : ↥(Spec (CommRingCat.of K)))
      = (PrimeSpectrum.comap ev (⊥ : PrimeSpectrum K)
          : ↥(Spec (CommRingCat.of (MvPolynomial (Fin n) K)))) := by
    show (Spec.map (CommRingCat.ofHom ev)) (default : ↥(Spec (CommRingCat.of K))) = _
    rw [show (Spec.map (CommRingCat.ofHom ev)) (default : ↥(Spec (CommRingCat.of K)))
        = (PrimeSpectrum.comap ev (default : ↥(Spec (CommRingCat.of K)))
            : ↥(Spec (CommRingCat.of (MvPolynomial (Fin n) K)))) from rfl]
    rw [hd]
  have hxy : φ y = s (default : ↥(Spec (CommRingCat.of K))) := by
    rw [hs_def,
      show φ y = (PrimeSpectrum.comap g y
        : ↥(Spec (CommRingCat.of (MvPolynomial (Fin n) K)))) from rfl,
      show PrimeSpectrum.comap g y = PrimeSpectrum.comap ev (⊥ : PrimeSpectrum K) from hy]
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed φ s y hxy
  letI : Algebra K ↥A := f'.toAlgebra
  let gAlg : MvPolynomial (Fin n) K →ₐ[K] ↥A :=
    { toRingHom := g
      commutes' := fun k => by
        show g (algebraMap K (MvPolynomial (Fin n) K) k) = algebraMap K ↥A k
        rw [MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra f']
        exact congrArg (fun (φ : K →+* ↥A) => φ k) hgC }
  let evAlg : MvPolynomial (Fin n) K →ₐ[K] K := MvPolynomial.aeval a
  have hφ_over : (specOfMap (K := K) gAlg).left = φ := by rw [specOfMap_left]
  have hw_φ : φ ≫ (specOf K (MvPolynomial (Fin n) K)).hom = (specOf K ↥A).hom := by
    rw [← hφ_over]; exact Over.w _
  have hs_over : (specOfMap (K := K) evAlg).left = s := by
    rw [specOfMap_left]
    rfl
  have hw_s : s ≫ (specOf K (MvPolynomial (Fin n) K)).hom = (specOf K K).hom := by
    rw [← hs_over]; exact Over.w _
  have hring : iota ≫ (Y.hom.appLE ⊤ V eT) = CommRingCat.ofHom (algebraMap K ↥A) := by
    apply CommRingCat.hom_ext
    show (Y.hom.appLE ⊤ V eT).hom.comp iota.hom = algebraMap K ↥A
    exact (RingHom.algebraMap_toAlgebra f').symm
  have hstruct : hVaff.fromSpec ≫ Y.hom = (specOf K ↥A).hom := by
    rw [← AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec Y.hom
        (hU := isAffineOpen_top _) (hV := hVaff) eT, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv, specOf_hom, ← Spec.map_comp, hring]
  refine ⟨Over.homMk (l ≫ hVaff.fromSpec) ?_⟩
  calc (l ≫ hVaff.fromSpec) ≫ Y.hom
      = l ≫ (specOf K ↥A).hom := by rw [Category.assoc, hstruct]
    _ = l ≫ φ ≫ (specOf K (MvPolynomial (Fin n) K)).hom := by rw [hw_φ]
    _ = s ≫ (specOf K (MvPolynomial (Fin n) K)).hom := by rw [← Category.assoc, hl]
    _ = (specOf K K).hom := hw_s

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry in
open scoped Classical MonoidalCategory in
theorem exists_fpt_of_opens_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    (X : Work.GCBasics.Sch K) [Smooth X.hom] [GeometricallyIrreducible X.hom]
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) (hU : U ≠ ⊥) :
    ∃ p : Work.GCBasics.FPt X K, Work.GCBasics.RPt.LandsIn p U := by
  haveI : Smooth (Work.GCBasics.Opens.toOver U).hom :=
    inferInstanceAs (Smooth (U.ι ≫ X.hom))
  haveI : LocallyOfFiniteType (Work.GCBasics.Opens.toOver U).hom :=
    inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  have hUne : Nonempty (Work.GCBasics.Opens.toOver U).left := by
    have h : (U : Set X.left).Nonempty := by
      by_contra hne
      have h2 : (U : Set X.left) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      exact hU (SetLike.coe_injective (by rw [h2, TopologicalSpace.Opens.coe_bot]))
    obtain ⟨x, hx⟩ := h
    exact ⟨show ↥U from ⟨x, hx⟩⟩
  obtain ⟨q⟩ := Work.Charts.exists_fpt_of_smooth_of_nonempty
    (Work.GCBasics.Opens.toOver U) hUne
  refine ⟨q ≫ Work.GCBasics.Opens.ιOver U, ?_⟩
  show (Over.Hom.left (Work.GCBasics.Opens.ιOver U))
    ((Over.Hom.left q) (IsLocalRing.closedPoint K)) ∈ (U : Set X.left)
  exact (Scheme.Opens.range_ι U).le (Set.mem_range_self _)

end

end Work.Charts
