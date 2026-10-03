/-
Copyright (c) 2026 The contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coherence of semirings is invariant under ring isomorphisms

`Ring.Coherent R` says that every finitely generated left ideal of `R` is a finitely
presented `R`-module.  This file shows that the property is transported along any ring
equivalence `e : R ≃+* S`.

The mathematical content is that a ring isomorphism lets us rewrite every `S`-presentation
as an `R`-presentation (and conversely).  Formally this is done by transporting
`Module.FinitePresentation` first along the isomorphism `R ≃+* S` (which changes the scalar
ring of a fixed module) and then along a linear equivalence (which changes the module).

## Main results

* `Work.ORReductions.Coherent.finitePresentation_of_ringEquiv`
* `Work.ORReductions.Coherent.finitePresentation_of_linearEquiv`
* `Work.ORReductions.Coherent.coherent_of_ringEquiv`
-/
import Mathlib
import Submission.Work.ORReductions.Basic

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.ORReductions.Coherent

open Finsupp

/-! ### Semilinear transport along a ring equivalence -/

/-- A ring equivalence, regarded as a semilinear map. -/
abbrev ringEquivLinear {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) :
    R →ₛₗ[(e : R →+* S)] S :=
  { toFun := e, map_add' := map_add e, map_smul' := by intro c x; simp [map_mul] }

@[simp] theorem ringEquivLinear_apply {R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) (x : R) : ringEquivLinear e x = e x := rfl

/-- `Finsupp.mapRange` along a ring equivalence, packaged as a semilinear map. -/
noncomputable abbrev finsuppMapRangeLinear {R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) (α : Type*) : (α →₀ R) →ₛₗ[(e : R →+* S)] (α →₀ S) :=
  Finsupp.mapRange.linearMap (ringEquivLinear e)

@[simp] theorem finsuppMapRangeLinear_apply {R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) (α : Type*) (l : α →₀ R) :
    finsuppMapRangeLinear e α l = mapRange (e : R → S) (map_zero e) l := rfl

/-- Coefficients of a `linearCombination` over `S` can be pushed to coefficients over `R`.
Here the `S`-module structure on `M` is the one pulled back from the `R`-structure along `e`. -/
theorem linearCombination_compHom {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R M] (e : R ≃+* S) {α : Type*} (v : α → M) (l : α →₀ S) :
    letI : Module S M := Module.compHom M e.symm.toRingHom
    linearCombination S v l =
      linearCombination R v (mapRange (e.symm : S → R) (map_zero e.symm) l) := by
  letI : Module S M := Module.compHom M e.symm.toRingHom
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (fun _ => by simp)]
  rfl

/-- The span of a set of elements does not depend on whether the scalars are taken in `R` or
in `S`, when the `S`-module structure is pulled back from the `R`-structure along `e`. -/
theorem span_compHom {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
    (e : R ≃+* S) (T : Set M) :
    letI : Module S M := Module.compHom M e.symm.toRingHom
    (Submodule.span S T : Set M) = (Submodule.span R T : Set M) := by
  letI : Module S M := Module.compHom M e.symm.toRingHom
  apply Set.ext
  intro x
  change x ∈ Submodule.span S T ↔ x ∈ Submodule.span R T
  rw [Finsupp.mem_span_iff_linearCombination S T x,
      Finsupp.mem_span_iff_linearCombination R T x]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨mapRange (e.symm : S → R) (map_zero e.symm) l, (linearCombination_compHom e _ l).symm⟩
  · rintro ⟨l, rfl⟩
    refine ⟨mapRange (e : R → S) (map_zero e) l, ?_⟩
    rw [linearCombination_compHom e]
    congr 1
    ext i
    simp

/-- `Module.FinitePresentation` is invariant under a ring equivalence: a finitely presented
module over `R` is finitely presented over `S`, for the `S`-structure pulled back along `e`. -/
theorem finitePresentation_of_ringEquiv {R S M : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module R M] (e : R ≃+* S) (h : Module.FinitePresentation R M) :
    letI : Module S M := Module.compHom M e.symm.toRingHom
    Module.FinitePresentation S M := by
  letI : Module S M := Module.compHom M e.symm.toRingHom
  obtain ⟨s, hs, hk⟩ := h
  refine ⟨s, ?_, ?_⟩
  · rw [Submodule.eq_top_iff']
    intro x
    have hx : x ∈ (Submodule.span R (↑s : Set M) : Set M) := by rw [hs]; trivial
    rwa [← span_compHom e (↑s : Set M)] at hx
  · have hker : LinearMap.ker (linearCombination S ((↑) : s → M))
        = Submodule.map (finsuppMapRangeLinear e s)
            (LinearMap.ker (linearCombination R ((↑) : s → M))) := by
      apply le_antisymm
      · intro x hx
        rw [Submodule.mem_map]
        refine ⟨mapRange (e.symm : S → R) (map_zero e.symm) x, ?_, ?_⟩
        · rw [LinearMap.mem_ker, ← linearCombination_compHom e ((↑) : s → M) x]
          exact hx
        · ext i; simp
      · rw [Submodule.map_le_iff_le_comap]
        intro y hy
        rw [Submodule.mem_comap, LinearMap.mem_ker]
        have h1 : linearCombination S ((↑) : s → M) (finsuppMapRangeLinear e s y)
            = linearCombination R ((↑) : s → M) y := by
          rw [linearCombination_compHom e]
          congr 1
          ext i; simp
        rw [h1]
        exact LinearMap.mem_ker.mp hy
    rw [hker]
    exact hk.map (finsuppMapRangeLinear e s)

/-- `Module.FinitePresentation` is invariant under a linear equivalence. -/
theorem finitePresentation_of_linearEquiv {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (φ : M ≃ₗ[R] N) :
    Module.FinitePresentation R M → Module.FinitePresentation R N := by
  intro h
  classical
  obtain ⟨s, hs, hk⟩ := h
  set f : s → s.image (⇑φ) := fun i => ⟨φ i, Finset.mem_image_of_mem _ i.2⟩ with hf
  have hf_surj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hy
    exact ⟨⟨i, hi⟩, by ext; exact hiy⟩
  refine ⟨s.image (⇑φ), ?_, ?_⟩
  · rw [Finset.coe_image, show (⇑φ : M → N) = ⇑(φ : M →ₗ[R] N) from rfl,
        ← Submodule.map_span (φ : M →ₗ[R] N) (↑s : Set M), hs, Submodule.map_top,
        LinearMap.range_eq_top.mpr φ.surjective]
  · have hkey : ∀ l : s →₀ R,
        Finsupp.linearCombination R ((↑) : s.image (⇑φ) → N) (Finsupp.mapDomain f l)
          = ⇑(φ : M →ₗ[R] N) (Finsupp.linearCombination R ((↑) : s → M) l) := by
      intro l
      rw [Finsupp.linearCombination_mapDomain,
          Finsupp.apply_linearCombination R (φ : M →ₗ[R] N) ((↑) : s → M) l]
      congr 1
    have hker : LinearMap.ker (Finsupp.linearCombination R ((↑) : s.image (⇑φ) → N))
        = Submodule.map (Finsupp.lmapDomain R R f)
            (LinearMap.ker (Finsupp.linearCombination R ((↑) : s → M))) := by
      ext x
      rw [Submodule.mem_map]
      constructor
      · intro hx
        obtain ⟨l, hl⟩ := Finsupp.mapDomain_surjective hf_surj x
        have h0 : ⇑(φ : M →ₗ[R] N) (Finsupp.linearCombination R ((↑) : s → M) l) = 0 := by
          rw [← hkey l, hl]
          exact LinearMap.mem_ker.mp hx
        refine ⟨l, ?_, ?_⟩
        · rw [LinearMap.mem_ker]
          exact φ.injective (by simpa using h0)
        · change Finsupp.mapDomain f l = x
          exact hl
      · rintro ⟨l, hl, hxl⟩
        rw [← hxl, LinearMap.mem_ker]
        change Finsupp.linearCombination R ((↑) : s.image (⇑φ) → N) (Finsupp.mapDomain f l) = 0
        rw [hkey l, LinearMap.mem_ker.mp hl]
        simp
    rw [hker]
    exact hk.map (Finsupp.lmapDomain R R f)

/-- A semiring is (left) coherent if all of its finitely generated (left) ideals are
finitely presented.  This property is invariant under ring isomorphisms. -/
theorem coherent_of_ringEquiv {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) :
    Ring.Coherent R → Ring.Coherent S := by
  intro hR J hJ
  let I : Ideal R := Ideal.comap e.toRingHom J
  have hI : I.FG := by
    have hm : Submodule.map (ringEquivLinear e.symm) J = I := by
      ext x
      show x ∈ Submodule.map (ringEquivLinear e.symm) J ↔ x ∈ Ideal.comap e.toRingHom J
      rw [Submodule.mem_map, Ideal.mem_comap]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rw [← hyx]
        simpa [ringEquivLinear_apply] using hy
      · intro hx
        exact ⟨e x, hx, by simp [ringEquivLinear_apply]⟩
    rw [← hm]
    exact Submodule.FG.map (ringEquivLinear e.symm) hJ
  have hfp : Module.FinitePresentation R I := hR I hI
  letI : Module S I := Module.compHom I e.symm.toRingHom
  have hfpS : Module.FinitePresentation S I := finitePresentation_of_ringEquiv e hfp
  have e_lin : I ≃ₗ[S] J :=
    { toFun := fun x => ⟨e x, by simpa using Ideal.mem_comap.mp x.2⟩
      invFun := fun y => ⟨e.symm y, by
        show e.symm (y : S) ∈ Ideal.comap e.toRingHom J
        rw [Ideal.mem_comap]
        simp⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro y; ext; simp
      map_add' := by intro x y; ext; simp
      map_smul' := by
        intro s x
        ext
        rw [show (s • x : I) = e.symm s • x from rfl]
        simp }
  exact finitePresentation_of_linearEquiv e_lin hfpS

end Work.ORReductions.Coherent
