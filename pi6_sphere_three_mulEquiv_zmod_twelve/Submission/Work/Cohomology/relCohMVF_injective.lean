import Mathlib
import Submission.Work.Cohomology.relCohMVDefs

/-!
# Injectivity of the first map of the relative cohomological Mayer–Vietoris sequence

The chain level relative Mayer–Vietoris sequence

`C^{U,V}(U ∩ V, U ∩ V ∩ A) --β--> C^{U,V}(U, U ∩ A) ⊞ C^{U,V}(V, V ∩ A) --α--> C^{U,V}(X,A)`

is degreewise short exact (`Work.Cohomology.relMVChainDegreewise_surjective`,
`Work.Cohomology.relMVChainDegreewise_ker`).  The second chain map `α = relMVChainRight` is
therefore degreewise surjective, and its transpose

`relCohMVF = biprod.lift (dual α₁) (dual α₂) : C^*(X,A) ⟶ C^*(U, U ∩ A) ⊞ C^*(V, V ∩ A)`

is degreewise injective: a `ℤ`-linear functional on the `n`-chains of `(X,A)` that annihilates
both components of `α` annihilates every element of the image of `α`, hence is zero.

The proof is elementwise.  Writing `Aᵢ` for the two components of `α` at degree `n` and using that
`α = biprod.desc α₁ α₂` together with

`(biprod.inl ∘ biprod.fst + biprod.inr ∘ biprod.snd) w = w`   (`biprodTotal_apply_chain`),

every `w` in the middle term has `α w = A₁ (fst w) + A₂ (snd w)`; consequently a functional `φ`
with `φ ∘ A₁ = 0 = φ ∘ A₂` kills the whole image of `α`.

## Main result

* `relCohMVF_injective` — `(relCohMVF).f n` is injective.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (X : TopCat) (A U V : Set X) (n : ℕ)

/-! ## The components of the maps at degree `n` -/

/-- The `fst`-component of `relCohMVF` at degree `n`, evaluated on a cochain, is the transpose of
`relMVChainAlpha₁`. -/
lemma relCohMVF_fst_apply_aux (x : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ) :
    ModuleCat.Hom.hom ((biprod.fst : dualComplex ℤ (relMVUU X A U V) ⊞
        dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVUU X A U V)).f n)
      (ModuleCat.Hom.hom ((relCohMVF X A U V).f n)
        (x : ↑((dualComplex ℤ (relMVTopC X A U V)).X n)))
    = x.comp ((relMVChainAlpha₁ X A U V).f n).hom := by
  have hfst : (relCohMVF X A U V).f n ≫ (biprod.fst : dualComplex ℤ (relMVUU X A U V) ⊞
      dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVUU X A U V)).f n
      = (dualComplexMap ℤ (relMVUU X A U V) (relMVTopC X A U V)
          (relMVChainAlpha₁ X A U V)).f n := by
    rw [relCohMVF, HomologicalComplex.biprod_lift_fst_f]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hfst, dualComplexMap_f]
  exact dualComplexMapComp_apply' ℤ (relMVUU X A U V) (relMVTopC X A U V)
    (relMVChainAlpha₁ X A U V) n x

/-- The `snd`-component of `relCohMVF` at degree `n`, evaluated on a cochain, is the transpose of
`relMVChainAlpha₂`. -/
lemma relCohMVF_snd_apply_aux (x : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ) :
    ModuleCat.Hom.hom ((biprod.snd : dualComplex ℤ (relMVUU X A U V) ⊞
        dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVVV X A U V)).f n)
      (ModuleCat.Hom.hom ((relCohMVF X A U V).f n)
        (x : ↑((dualComplex ℤ (relMVTopC X A U V)).X n)))
    = x.comp ((relMVChainAlpha₂ X A U V).f n).hom := by
  have hsnd : (relCohMVF X A U V).f n ≫ (biprod.snd : dualComplex ℤ (relMVUU X A U V) ⊞
      dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVVV X A U V)).f n
      = (dualComplexMap ℤ (relMVVV X A U V) (relMVTopC X A U V)
          (relMVChainAlpha₂ X A U V)).f n := by
    rw [relCohMVF, HomologicalComplex.biprod_lift_snd_f]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hsnd, dualComplexMap_f]
  exact dualComplexMapComp_apply' ℤ (relMVVV X A U V) (relMVTopC X A U V)
    (relMVChainAlpha₂ X A U V) n x

/-- Degreewise, the second chain map `relMVChainRight` sends `w` to the sum of the images of its two
components `fst w` and `snd w` under the components `relMVChainAlpha₁`, `relMVChainAlpha₂`. -/
lemma relMVChainRight_apply_aux (w : ↥((relMVUU X A U V ⊞ relMVVV X A U V).X n)) :
    ModuleCat.Hom.hom ((relMVChainRight X A U V).f n) w
      = ((relMVChainAlpha₁ X A U V).f n).hom
          (ModuleCat.Hom.hom ((biprod.fst : relMVUU X A U V ⊞ relMVVV X A U V ⟶
            relMVUU X A U V).f n) w)
        + ((relMVChainAlpha₂ X A U V).f n).hom
          (ModuleCat.Hom.hom ((biprod.snd : relMVUU X A U V ⊞ relMVVV X A U V ⟶
            relMVVV X A U V).f n) w) := by
  have htot := biprodTotal_apply_chain (relMVUU X A U V) (relMVVV X A U V) n w
  have hR := congrArg (ModuleCat.Hom.hom ((relMVChainRight X A U V).f n)) htot
  rw [map_add] at hR
  rw [← hR]
  congr 1

/-! ## Injectivity -/

/-- **The first map of the relative cohomological Mayer–Vietoris sequence is degreewise
injective.** -/
theorem relCohMVF_injective (X : TopCat) (A U V : Set X) (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom ((Work.Cohomology.relCohMVF X A U V).f n)) := by
  intro x y hxy
  -- the two components of `relCohMVF x` and `relCohMVF y` agree
  have h1 : (x : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ).comp ((relMVChainAlpha₁ X A U V).f n).hom
      = (y : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ).comp
          ((relMVChainAlpha₁ X A U V).f n).hom := by
    have h := congrArg (fun (w : ↥((dualComplex ℤ (relMVUU X A U V) ⊞
        dualComplex ℤ (relMVVV X A U V)).X n)) =>
      ModuleCat.Hom.hom ((biprod.fst : dualComplex ℤ (relMVUU X A U V) ⊞
        dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVUU X A U V)).f n) w) hxy
    simpa only [relCohMVF_fst_apply_aux X A U V n] using h
  have h2 : (x : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ).comp ((relMVChainAlpha₂ X A U V).f n).hom
      = (y : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ).comp
          ((relMVChainAlpha₂ X A U V).f n).hom := by
    have h := congrArg (fun (w : ↥((dualComplex ℤ (relMVUU X A U V) ⊞
        dualComplex ℤ (relMVVV X A U V)).X n)) =>
      ModuleCat.Hom.hom ((biprod.snd : dualComplex ℤ (relMVUU X A U V) ⊞
        dualComplex ℤ (relMVVV X A U V) ⟶ dualComplex ℤ (relMVVV X A U V)).f n) w) hxy
    simpa only [relCohMVF_snd_apply_aux X A U V n] using h
  change (x : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ) = (y : (relMVTopC X A U V).X n →ₗ[ℤ] ℤ)
  apply LinearMap.ext
  intro z
  -- every `z` is in the image of `relMVChainRight`
  obtain ⟨w, hw⟩ := relMVChainDegreewise_surjective X A U V n z
  rw [← hw, relMVChainRight_apply_aux X A U V n]
  rw [map_add, map_add]
  congr 1
  · simpa only [LinearMap.comp_apply] using
      LinearMap.congr_fun h1 (ModuleCat.Hom.hom ((biprod.fst : relMVUU X A U V ⊞
        relMVVV X A U V ⟶ relMVUU X A U V).f n) w)
  · simpa only [LinearMap.comp_apply] using
      LinearMap.congr_fun h2 (ModuleCat.Hom.hom ((biprod.snd : relMVUU X A U V ⊞
        relMVVV X A U V ⟶ relMVVV X A U V).f n) w)

end

end Work.Cohomology
