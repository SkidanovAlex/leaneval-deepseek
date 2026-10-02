import Mathlib
import Submission.Work.Cohomology.isZeroRelCohomologyZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The zeroth relative cohomology with rational coefficients

For a topological space `X`, a subset `A ⊆ X` and coefficients in a ring `R`, the relative
cohomology `H⁰(X,A;R)` is the kernel of the restriction `H⁰(X;R) ⟶ H⁰(A;R)`.  A degree zero
cohomology class is a locally constant function on `X`; restricting to the nonempty subset `A` of a
path-connected space `X`, such a function is determined by its value at any point of `A`.  Hence the
restriction is injective and

`H⁰(X,A; R) = 0`   for `A` nonempty and `X` path-connected,

for *any* coefficient ring `R`.  The integral case `R = ℤ` is
`Work.Cohomology.isZeroRelCohomologyZero`; here we reproduce the argument over a general
commutative ring and specialise it to `R = ℚ`, which is the statement requested.

The argument is carried out directly on the cochain complex: the relative cochain complex
`C^*(X,A)` (`relComplex`) is the subcomplex of `C^*(X)` of the cochains vanishing on chains lying in
`A` (`relKern`), so in degree `0` there is no incoming differential and

`H⁰(X,A; R) ≅ ker (d⁰ : C⁰(X,A) ⟶ C¹(X,A))`.

Thus it suffices to prove that `relDiffLM R X A 0` is injective, and for that we show that a linear
functional `φ` on the `0`-chains of `X` which vanishes on the `0`-chains of `A` and kills the
boundary `d₁ : C₁(X) ⟶ C₀(X)` is zero:

* killing `d₁` makes `φ` constant on the `0`-simplices representing the same path component
  (`Work.Cohomology.eval_constancy`), hence constant because `X` is path-connected;
* vanishing on `A` and `A ≠ ∅` makes `φ` vanish at one `0`-simplex (the image of a `0`-simplex of
  `A`), so `φ` vanishes on every `0`-simplex;
* the `0`-simplices generate `C₀(X)` (`SSet.chainComplex_hom_ext`), so `φ = 0`.

The transfer of `ker = ⊥` to the vanishing of `H⁰(X,A;R)` is the standard `IsZero ↔ Subsingleton`
for modules, together with the isomorphism `H⁰ ≅ ker d⁰` described above.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre

noncomputable section

open Work.Cohomology

/-! ## Two elementary lemmas about the singular chains, with arbitrary coefficients -/

/-- **The chain map induced by the inclusion `A ⊆ X` on the generators of `C₀`**, with coefficients
in any commutative ring `R`. -/
lemma chainMap_subtypeIncl_sgen_R (R : Type) [CommRing R] (X : TopCat) (A : Set X)
    (σ : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op ⦋0⦌)) :
    (chainMap R (TopCat.of A) X (subtypeIncl X A)).f 0 (sgen R (TopCat.of A) σ)
      = sgen R X ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋0⦌) σ) := by
  simp only [chainMap_f_eq, sgen]
  exact congrArg (fun (g : ModuleCat.of R R ⟶ (singularChains R X).X 0) => ModuleCat.Hom.hom g 1)
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of A)) (TopCat.toSSet.obj X)
      (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of R R) σ)

/-- A morphism of `R`-modules whose underlying linear map has trivial kernel has zero kernel. -/
lemma isZero_kernel_of_ker_eq_bot_R {R : Type} [CommRing R] {M N : ModuleCat R} (f : M ⟶ N)
    (h : LinearMap.ker (ModuleCat.Hom.hom f) = ⊥) : IsZero (kernel f) := by
  have hsub : Subsingleton ↥(LinearMap.ker (ModuleCat.Hom.hom f)) := by
    refine ⟨fun a b => ?_⟩
    exact Subtype.ext (by
      have ha : (a : M) = 0 := (Submodule.mem_bot R).mp (h ▸ a.2)
      have hb : (b : M) = 0 := (Submodule.mem_bot R).mp (h ▸ b.2)
      rw [ha, hb])
  have : Subsingleton (ModuleCat.of R ↥(LinearMap.ker (ModuleCat.Hom.hom f))) := hsub
  exact (Iso.isZero_iff (ModuleCat.kernelIsoKer f)).2 (ModuleCat.isZero_of_subsingleton _)

/-! ## The differential `C⁰(X,A) ⟶ C¹(X,A)` is injective -/

/-- **A relative `0`-cocycle is zero** when `X` is path-connected and `A` is nonempty; equivalently
the differential `d⁰ : C⁰(X,A) ⟶ C¹(X,A)` of the relative cochain complex is injective.  With
coefficients in an arbitrary commutative ring `R`. -/
theorem ker_relDiffLM_zero_eq_bot_R (R : Type) [CommRing R] (X : TopCat) (A : Set X)
    [PathConnectedSpace X] (hA : A.Nonempty) : LinearMap.ker (relDiffLM R X A 0) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨a, ha⟩ := hA
  -- `x` is a linear functional on the `0`-chains of `X` which kills the boundary `d₁`.
  have hf : (show ↥((singularChains R X).X 0) →ₗ[R] R from x.1).comp
      ((singularChains R X).d 1 0).hom = 0 := by
    have hdiff : cochainDiff R (TopCat.toSSet.obj X)
        (show ↥((singularChains R X).X 0) →ₗ[R] R from x.1) = 0 := by
      rw [← singularCochain_d_apply R X (show ↥((singularChains R X).X 0) →ₗ[R] R from x.1)]
      simpa only [relDiffLM_coe, Submodule.coe_zero] using congrArg Subtype.val hx
    simp only [cochainDiff] at hdiff
    exact hdiff
  -- a `0`-simplex of `A`
  let σ : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op ⦋0⦌) :=
    (TopCat.toSSetObj₀Equiv (X := TopCat.of A)).symm ⟨a, ha⟩
  -- the functional vanishes on the image in `X` of that simplex, since it vanishes on `A`
  have hval : (show ↥((singularChains R X).X 0) →ₗ[R] R from x.1)
      (sgen R X ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋0⦌) σ)) = 0 := by
    have h0 : ((chainMap R (TopCat.of A) X (subtypeIncl X A)).f 0).hom.dualMap x.1 = 0 := x.2
    have h2 := congrArg (fun g : ↥((singularChains R (TopCat.of A)).X 0) →ₗ[R] R =>
      g (sgen R (TopCat.of A) σ)) h0
    simp only [LinearMap.zero_apply] at h2
    rw [LinearMap.dualMap_apply, chainMap_subtypeIncl_sgen_R] at h2
    exact h2
  -- hence it vanishes on *every* `0`-simplex, by constancy along the path components
  have hall : ∀ s, (show ↥((singularChains R X).X 0) →ₗ[R] R from x.1) (sgen R X s) = 0 := by
    intro s
    exact (eval_constancy R X (show ↥((singularChains R X).X 0) →ₗ[R] R from x.1) hf s).trans
      ((eval_constancy R X (show ↥((singularChains R X).X 0) →ₗ[R] R from x.1) hf
        ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋0⦌) σ)).symm.trans hval)
  -- and the `0`-simplices generate `C₀(X)`
  have hφzero : (show ↥((singularChains R X).X 0) →ₗ[R] R from x.1) = 0 := by
    have key : (ModuleCat.ofHom (show ↥((singularChains R X).X 0) →ₗ[R] R from x.1)
        : (singularChains R X).X 0 ⟶ ModuleCat.of R R) = 0 := by
      apply SSet.chainComplex_hom_ext (n := 0) (T := ModuleCat.of R R)
      intro s
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
        LinearMap.zero_comp]
      apply LinearMap.ext_ring
      show (show ↥((singularChains R X).X 0) →ₗ[R] R from x.1) (sgen R X s) = 0
      exact hall s
    simpa only [ModuleCat.hom_ofHom, ModuleCat.hom_zero] using congrArg ModuleCat.Hom.hom key
  exact Subtype.ext hφzero

/-! ## The zeroth relative cohomology vanishes -/

/-- **The zeroth relative cohomology `H⁰(X,A;R)` of a nonempty subset of a path-connected space is
zero**, for any commutative coefficient ring `R`. -/
theorem isZeroRelCohomologyZero_of_commRing (R : Type) [CommRing R] (X : TopCat) (A : Set X)
    [PathConnectedSpace X] (hA : A.Nonempty) :
    CategoryTheory.Limits.IsZero (Work.Cohomology.relCohomology R X A 0) := by
  have hker := ker_relDiffLM_zero_eq_bot_R R X A hA
  let K := relComplex R X A
  -- in degree `0` there is no incoming differential, so `H⁰` is the kernel of `d⁰`
  have hk : LinearMap.ker (ModuleCat.Hom.hom (K.d 0 1)) = ⊥ := by
    simpa only [K, relComplex_d, relDiff, ModuleCat.hom_ofHom] using hker
  have hf : (K.sc 0).f = 0 := rfl
  have hZ : IsZero (kernel (K.d 0 1)) := isZero_kernel_of_ker_eq_bot_R _ hk
  have hZc' : IsZero ((K.sc' 0 0 1).cycles) :=
    IsZero.of_iso hZ (ShortComplex.cyclesIsoKernel (K.sc' 0 0 1))
  have hZc : IsZero (K.cycles 0) :=
    IsZero.of_iso hZc' (K.cyclesIsoSc' 0 0 1 (by simp) (by simp))
  exact IsZero.of_iso hZc (ShortComplex.asIsoHomologyπ (K.sc 0) hf).symm

/-- **The zeroth relative cohomology `H⁰(X,A;ℚ)` of a nonempty subset of a path-connected space is
zero.** -/
theorem isZeroRelCohomologyZero_rat (X : TopCat) (A : Set X) [PathConnectedSpace X]
    (hA : A.Nonempty) :
    CategoryTheory.Limits.IsZero (Work.Cohomology.relCohomology ℚ X A 0) :=
  isZeroRelCohomologyZero_of_commRing ℚ X A hA

end

end Work.Serre
