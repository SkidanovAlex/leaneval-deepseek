import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.exists_toCycles_eq_of_homologypi_eq_zero
import Submission.Work.Compact.Noncompact.cokernel_pi_eq_zero_iff

/-!
# A relative cycle whose class in `H_{k+1}(X, X∖S)` vanishes is a boundary modulo `S`

For a topological space `X`, a subset `S ⊆ X` and a chain `z ∈ C_{k+1}(X)` whose boundary is
supported in `S`, the class of `z` in `H_{k+1}(X, X∖S) = H_{k+1}(C_*(X)/C_*(S))` is
`Work.Compact.Noncompact.hatClass S k z hz`.  This file proves that when that class vanishes,
`z` differs from a boundary by a chain supported in `S`:

`exists_sub_bdry_of_hatClass_eq_zero`:
`∃ w : C_{k+2}(X), z - ∂w ∈ suppS X S (k+1)`.

The proof is elementary homological algebra.  The vanishing of `hatClass` says that the cycle
`hatCycHom S k z hz ∈ C_{k+1}(X)/C_{k+1}(S)` is a boundary, so there is
`y ∈ C_{k+2}(X)/C_{k+2}(S)` with `∂y = hatQ S k z`, the image of `z` in the quotient.  Lifting `y`
to a chain `w ∈ C_{k+2}(X)` and using the compatibility of `∂` with the quotient projection gives
`hatQ S k (z - ∂w) = 0`; the auxiliary fact `hatQ_eq_zero_iff_mem_suppS` (the image of a chain in
the quotient vanishes exactly when the chain is supported in `S`) then yields the conclusion.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Compact.Noncompact

set_option maxHeartbeats 800000

noncomputable section

/-- The span of a single element, evaluated at `1`. -/
lemma toSpanSingleton_one' {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M] (x : M) :
    (LinearMap.toSpanSingleton R M x) (1 : R) = x := by
  rw [LinearMap.toSpanSingleton_apply, one_smul]

/-- The `ℤ`-linear map `1 ↦ x` as a morphism of `ModuleCat`, evaluated at `1`. -/
lemma ofHom_toSpanSingleton_one' {R : Type*} [Ring R] {M : ModuleCat R} (x : M) :
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)).hom (1 : R) = x := by
  rw [ModuleCat.hom_ofHom, toSpanSingleton_one']

/-- **The image of a chain in `C_*(X)/C_*(S)` vanishes exactly when the chain is supported in
`S`.**  The projection `(cokernel.π (inclChains X S)).f (k+1)` is the cokernel of the degree-`(k+1)`
component `(inclChains X S).f (k+1)` of the inclusion of chain complexes (cokernels of chain
complexes are computed degreewise, i.e. the evaluation functor preserves them), so its kernel in
the category of `ℤ`-modules is the range of that component, which is `suppS X S (k+1)`. -/
lemma hatQ_eq_zero_iff_mem_suppS {X : TopCat} (S : Set X) (k : ℕ) (x : Ch X (k+1)) :
    x ∈ suppS X S (k+1) ↔ hatQ S k x = 0 := by
  constructor
  · intro hx
    exact hatQ_eq_zero_of_mem_suppS hx
  · intro hx
    -- the degree-`(k+1)` projection is a cokernel of the degree-`(k+1)` inclusion
    have hc := isColimitCoforkMapOfIsColimit'
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) (k+1))
      (cokernel.condition (Work.Cohomology.inclChains X S))
      (cokernelIsCokernel (Work.Cohomology.inclChains X S))
    have hc' : (Work.Cohomology.inclChains X S).f (k+1) ≫
        (cokernel.π (Work.Cohomology.inclChains X S)).f (k+1) = 0 := by
      rw [← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f]
    exact (cokernelπ_eq_zero_iff_range hc' hc x).mp hx

theorem exists_sub_bdry_of_hatClass_eq_zero {X : TopCat} (S : Set X) (k : ℕ)
    (z : Work.Compact.Noncompact.Ch X (k + 1))
    (hz : Work.Compact.Noncompact.bdry X k z ∈ Work.Compact.Noncompact.suppS X S k)
    (h : Work.Compact.Noncompact.hatClass S k z hz = 0) :
    ∃ w : Work.Compact.Noncompact.Ch X (k + 2),
      z - Work.Compact.Noncompact.bdry X (k + 1) w ∈ Work.Compact.Noncompact.suppS X S (k + 1) := by
  -- the class of the cycle `hatCycHom S k z hz` in homology vanishes
  have hπ : (RC X S).homologyπ (k+1) ((hatCycHom S k z hz).hom 1) = 0 := by
    rw [hatClass, hatClassHom, ModuleCat.comp_apply] at h
    exact h
  -- hence the cycle is a boundary `toCycles y`
  obtain ⟨y, hy⟩ := exists_toCycles_eq_of_homologypi_eq_zero (C := RC X S) k
    ((hatCycHom S k z hz).hom 1) hπ
  -- the image of that cycle under `iCycles` is the image of `z` in the quotient
  have hA : (RC X S).iCycles (k+1) ((hatCycHom S k z hz).hom 1) = hatQ S k z := by
    have h := iCycles_hatCycHom S k z hz
    have h2 := congrArg (fun (f : ModuleCat.of ℤ ℤ ⟶ (RC X S).X (k+1)) => f.hom 1) h
    rw [ModuleCat.comp_apply] at h2
    rw [h2]
    exact ofHom_toSpanSingleton_one' (hatQ S k z)
  -- so `∂y = hatQ S k z`
  have hdy : (RC X S).d (k+2) (k+1) y = hatQ S k z := by
    have hL : (RC X S).iCycles (k+1) ((RC X S).toCycles (k+2) (k+1) y)
        = (RC X S).d (k+2) (k+1) y := by
      rw [← ModuleCat.comp_apply, HomologicalComplex.toCycles_i]
    rw [← hL, hy, hA]
  -- lift `y` to a chain `w` of `X`
  obtain ⟨w, hw⟩ : ∃ w : Ch X (k+2),
      (cokernel.π (Work.Cohomology.inclChains X S)).f (k+2) w = y := by
    have hsurj : Function.Surjective
        (ModuleCat.Hom.hom ((cokernel.π (Work.Cohomology.inclChains X S)).f (k+2))) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨w, hw⟩ := hsurj y
    exact ⟨w, hw⟩
  refine ⟨w, ?_⟩
  -- it suffices that `z - ∂w` has vanishing image in the quotient
  rw [hatQ_eq_zero_iff_mem_suppS]
  have h3 : (RC X S).d (k+2) (k+1) y
      = ((cokernel.π (Work.Cohomology.inclChains X S)).f (k+1)) (bdry X (k+1) w) := by
    rw [← hw]
    have hcomm := HomologicalComplex.Hom.comm (cokernel.π (Work.Cohomology.inclChains X S))
      (k+2) (k+1)
    have hh := congrArg (fun (φ : Ch X (k+2) ⟶ (RC X S).X (k+1)) => φ.hom w) hcomm
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hh
    exact hh
  rw [hatQ, map_sub, ← h3, hdy, sub_self]

end

end Work.Compact.Noncompact
