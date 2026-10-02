import Mathlib
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.singularCohomology_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The zeroth relative cohomology of a nonempty subset of a path-connected space

For a topological space `X`, a subset `A ⊆ X` and coefficients in a ring `R`, the relative
cohomology `H⁰(X,A;R)` is the kernel of the restriction `H⁰(X;R) ⟶ H⁰(A;R)` (exactness of the
long exact sequence of the pair at `H⁰(X,A)`).  A degree zero cohomology class is a locally
constant function on `X` (for `R = ℤ`, an integer valued function constant on path components);
restricting to the nonempty subset `A` of a path-connected space `X`, such a function is
determined by its value at any point of `A`.  Hence the restriction is injective and

`H⁰(X,A; ℤ) = 0`   for `A` nonempty and `X` path-connected,

which is `isZeroRelCohomologyZero` below.

The argument is carried out directly on the cochain complex, without the long exact sequence: the
relative cochain complex `C^*(X,A)` (`relComplex`) is the subcomplex of `C^*(X)` of the cochains
vanishing on chains lying in `A` (`relKern`), so in degree `0` there is no incoming differential
and

`H⁰(X,A; ℤ) ≅ ker (d⁰ : C⁰(X,A) ⟶ C¹(X,A))`.

Thus it suffices to prove that `relDiffLM ℤ X A 0` is injective (`ker_relDiffLM_zero_eq_bot`), and
for that we show that a linear functional `φ` on the `0`-chains of `X` which vanishes on the
`0`-chains of `A` and kills the boundary `d₁ : C₁(X) ⟶ C₀(X)` is zero:

* killing `d₁` makes `φ` constant on the `0`-simplices representing the same path component
  (`eval_constancy`), hence constant because `X` is path-connected;
* vanishing on `A` and `A ≠ ∅` makes `φ` vanish at one `0`-simplex (the image of a `0`-simplex of
  `A`), so `φ` vanishes on every `0`-simplex;
* the `0`-simplices generate `C₀(X)` (`SSet.chainComplex_hom_ext`), so `φ = 0`.

The transfer of `ker = ⊥` to the vanishing of `H⁰(X,A;ℤ)` is the standard `IsZero ↔ Subsingleton`
for modules, together with the isomorphism `H⁰ ≅ ker d⁰` described above.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## Two elementary lemmas about the singular chains -/

/-- **The chain map induced by the inclusion `A ⊆ X` on the generators of `C₀`**: the `0`-chain of
`A` given by a `0`-simplex `σ` is sent to the `0`-chain of `X` given by the image `0`-simplex. -/
lemma chainMap_subtypeIncl_sgen (X : TopCat) (A : Set X)
    (σ : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op ⦋0⦌)) :
    (chainMap ℤ (TopCat.of A) X (subtypeIncl X A)).f 0 (sgen ℤ (TopCat.of A) σ)
      = sgen ℤ X ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋0⦌) σ) := by
  simp only [chainMap_f_eq, sgen]
  exact congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (singularChains ℤ X).X 0) => ModuleCat.Hom.hom g 1)
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of A)) (TopCat.toSSet.obj X)
      (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of ℤ ℤ) σ)

/-- A morphism of `ℤ`-modules whose underlying linear map has trivial kernel has zero kernel. -/
lemma isZero_kernel_of_ker_eq_bot {M N : ModuleCat ℤ} (f : M ⟶ N)
    (h : LinearMap.ker (ModuleCat.Hom.hom f) = ⊥) : IsZero (kernel f) := by
  have hsub : Subsingleton ↥(LinearMap.ker (ModuleCat.Hom.hom f)) := by
    refine ⟨fun a b => ?_⟩
    exact Subtype.ext (by
      have ha : (a : M) = 0 := (Submodule.mem_bot ℤ).mp (h ▸ a.2)
      have hb : (b : M) = 0 := (Submodule.mem_bot ℤ).mp (h ▸ b.2)
      rw [ha, hb])
  have : Subsingleton (ModuleCat.of ℤ ↥(LinearMap.ker (ModuleCat.Hom.hom f))) := hsub
  exact (Iso.isZero_iff (ModuleCat.kernelIsoKer f)).2 (ModuleCat.isZero_of_subsingleton _)

/-! ## The differential `C⁰(X,A) ⟶ C¹(X,A)` is injective -/

/-- **A relative `0`-cocycle is zero** when `X` is path-connected and `A` is nonempty; equivalently
the differential `d⁰ : C⁰(X,A) ⟶ C¹(X,A)` of the relative cochain complex is injective. -/
theorem ker_relDiffLM_zero_eq_bot (X : TopCat) (A : Set X) [PathConnectedSpace X]
    (hA : A.Nonempty) : LinearMap.ker (relDiffLM ℤ X A 0) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨a, ha⟩ := hA
  -- `x` is a linear functional on the `0`-chains of `X` which kills the boundary `d₁`.
  have hf : (show ↥((singularChains ℤ X).X 0) →ₗ[ℤ] ℤ from x.1).comp
      ((singularChains ℤ X).d 1 0).hom = 0 := by
    have hdiff : cochainDiff ℤ (TopCat.toSSet.obj X)
        (show ↥((singularChains ℤ X).X 0) →ₗ[ℤ] ℤ from x.1) = 0 := by
      rw [← singularCochain_d_apply ℤ X (show ↥((singularChains ℤ X).X 0) →ₗ[ℤ] ℤ from x.1)]
      simpa only [relDiffLM_coe, Submodule.coe_zero] using congrArg Subtype.val hx
    simp only [cochainDiff] at hdiff
    exact hdiff
  -- a `0`-simplex of `A`
  let σ : (TopCat.toSSet.obj (TopCat.of A)).obj (Opposite.op ⦋0⦌) :=
    (TopCat.toSSetObj₀Equiv (X := TopCat.of A)).symm ⟨a, ha⟩
  -- the functional vanishes on the image in `X` of that simplex, since it vanishes on `A`
  have hval : (show ↥((singularChains ℤ X).X 0) →ₗ[ℤ] ℤ from x.1)
      (sgen ℤ X ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋0⦌) σ)) = 0 := by
    have h0 : ((chainMap ℤ (TopCat.of A) X (subtypeIncl X A)).f 0).hom.dualMap x.1 = 0 := x.2
    have h2 := congrArg (fun g : ↥((singularChains ℤ (TopCat.of A)).X 0) →ₗ[ℤ] ℤ =>
      g (sgen ℤ (TopCat.of A) σ)) h0
    simp only [LinearMap.zero_apply] at h2
    rw [LinearMap.dualMap_apply, chainMap_subtypeIncl_sgen] at h2
    exact h2
  -- hence it vanishes on *every* `0`-simplex, by constancy along the path components
  have hall : ∀ s, (show ↥((singularChains ℤ X).X 0) →ₗ[ℤ] ℤ from x.1) (sgen ℤ X s) = 0 := by
    intro s
    exact (eval_constancy ℤ X (show ↥((singularChains ℤ X).X 0) →ₗ[ℤ] ℤ from x.1) hf s).trans
      ((eval_constancy ℤ X (show ↥((singularChains ℤ X).X 0) →ₗ[ℤ] ℤ from x.1) hf
        ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋0⦌) σ)).symm.trans hval)
  -- and the `0`-simplices generate `C₀(X)`
  have hφzero : (show ↥((singularChains ℤ X).X 0) →ₗ[ℤ] ℤ from x.1) = 0 := by
    have key : (ModuleCat.ofHom (show ↥((singularChains ℤ X).X 0) →ₗ[ℤ] ℤ from x.1)
        : (singularChains ℤ X).X 0 ⟶ ModuleCat.of ℤ ℤ) = 0 := by
      apply SSet.chainComplex_hom_ext (n := 0) (T := ModuleCat.of ℤ ℤ)
      intro s
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
        LinearMap.zero_comp]
      apply LinearMap.ext_ring
      show (show ↥((singularChains ℤ X).X 0) →ₗ[ℤ] ℤ from x.1) (sgen ℤ X s) = 0
      exact hall s
    simpa only [ModuleCat.hom_ofHom, ModuleCat.hom_zero] using congrArg ModuleCat.Hom.hom key
  exact Subtype.ext hφzero

/-! ## The zeroth relative cohomology vanishes -/

/-- **The zeroth relative cohomology `H⁰(X,A;ℤ)` of a nonempty subset of a path-connected space is
zero.** -/
theorem isZeroRelCohomologyZero (X : TopCat) (A : Set X) [PathConnectedSpace X] (hA : A.Nonempty) :
    CategoryTheory.Limits.IsZero (Work.Cohomology.relCohomology ℤ X A 0) := by
  have hker := ker_relDiffLM_zero_eq_bot X A hA
  let K := relComplex ℤ X A
  -- in degree `0` there is no incoming differential, so `H⁰` is the kernel of `d⁰`
  have hk : LinearMap.ker (ModuleCat.Hom.hom (K.d 0 1)) = ⊥ := by
    simpa only [K, relComplex_d, relDiff, ModuleCat.hom_ofHom] using hker
  have hf : (K.sc 0).f = 0 := rfl
  have hZ : IsZero (kernel (K.d 0 1)) := isZero_kernel_of_ker_eq_bot _ hk
  have hZc' : IsZero ((K.sc' 0 0 1).cycles) :=
    IsZero.of_iso hZ (ShortComplex.cyclesIsoKernel (K.sc' 0 0 1))
  have hZc : IsZero (K.cycles 0) :=
    IsZero.of_iso hZc' (K.cyclesIsoSc' 0 0 1 (by simp) (by simp))
  exact IsZero.of_iso hZc (ShortComplex.asIsoHomologyπ (K.sc 0) hf).symm

end

end Work.Cohomology
