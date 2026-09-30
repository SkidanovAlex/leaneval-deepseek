import Mathlib
import ChallengeDeps
import Submission.Work.HomologyExtra.Basic
import Submission.Work.HomologyExtra.CycleClass
import Submission.Work.HomologyExtra.SimplexClass

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Reductions towards the generator statement

This file records the elementary reductions that turn the two halves of the contract for
`(Δⁿ, ∂Δⁿ)` into each other:

* `epi_self_zmod_isIso` — an epimorphism `ℤ ⟶ ℤ` of `ℤ`-modules is an isomorphism;
* `isIso_simplexGenMap_of_epi` — hence, if `simplexGenMap n` is an epimorphism ("the identity
  simplex generates `Hₙ(Δⁿ,∂Δⁿ)`") and `Hₙ(Δⁿ,∂Δⁿ) ≅ ℤ`, then `simplexGenMap n` is an isomorphism;
* `isIso_pairδ_of_isZero` — the connecting map `δ : H_{k+1}(Δⁿ,∂Δⁿ) ⟶ H_k(∂Δⁿ)` of the pair is an
  isomorphism as soon as the two outer terms of the exact sequence vanish
  (`H_{k+1}(Δⁿ) = 0` and `H_k(Δⁿ) = 0`), which is the step that transfers the computation from the
  sphere `∂Δⁿ` to the pair.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- **An epimorphism `ℤ ⟶ ℤ` is an isomorphism.** A `ℤ`-linear self-map of `ℤ` is multiplication by
its value at `1`; being surjective forces that value to be a unit. -/
theorem epi_self_zmod_isIso (f : Work.Homology.ZMod ⟶ Work.Homology.ZMod) (hf : Epi f) :
    IsIso f := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have hsurj : Function.Surjective (ModuleCat.Hom.hom f) := (ModuleCat.epi_iff_surjective f).mp hf
  have key : ∀ x : ℤ, ModuleCat.Hom.hom f x = x * ModuleCat.Hom.hom f 1 := by
    intro x
    have h := map_zsmul (ModuleCat.Hom.hom f) x (1 : ℤ)
    simpa using h
  have ha : ModuleCat.Hom.hom f 1 = 1 ∨ ModuleCat.Hom.hom f 1 = -1 := by
    obtain ⟨n, hn⟩ := hsurj 1
    have h : (n : ℤ) * ModuleCat.Hom.hom f 1 = 1 := by
      rw [← key n, hn]
    have h' : ModuleCat.Hom.hom f 1 * (n : ℤ) = 1 := by
      rw [mul_comm]; exact h
    exact Int.eq_one_or_neg_one_of_mul_eq_one h'
  refine ⟨fun x y hxy => ?_, hsurj⟩
  rw [key x, key y] at hxy
  rcases ha with h | h
  · rw [h, mul_one, mul_one] at hxy
    exact hxy
  · rw [h, mul_neg, mul_one, mul_neg, mul_one] at hxy
    exact neg_inj.mp hxy

/-- If the class of the identity simplex generates `Hₙ(Δⁿ,∂Δⁿ)` (i.e. `simplexGenMap n` is an
epimorphism) and `Hₙ(Δⁿ,∂Δⁿ) ≅ ℤ`, then `simplexGenMap n` is an isomorphism. -/
theorem isIso_simplexGenMap_of_epi (n : ℕ) (hg : Epi (simplexGenMap n))
    (h : Nonempty (Work.Homology.relHomology Work.Homology.ZMod n (simplex n)
      (simplexBoundary n) ≅ Work.Homology.ZMod)) :
    IsIso (simplexGenMap n) := by
  obtain ⟨e⟩ := h
  have hφ : Epi (simplexGenMap n ≫ e.hom) := epi_comp _ _
  have hbij : Function.Bijective
      (ModuleCat.Hom.hom (simplexGenMap n ≫ e.hom)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp (epi_self_zmod_isIso _ hφ)
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy => hbij.1 ?_, (ModuleCat.epi_iff_surjective (simplexGenMap n)).mp hg⟩
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hxy]

/-- **The connecting map of the pair `(Δⁿ, ∂Δⁿ)` is an isomorphism** as soon as the outer terms of
the exact sequence vanish (`H_{k+1}(Δⁿ) = 0` and `H_k(Δⁿ) = 0`): this is the standard computation
`H_{k+1}(Δⁿ,∂Δⁿ) ≅ H_k(∂Δⁿ)` for the contractible simplex. -/
theorem isIso_pairδ_of_isZero (n k : ℕ)
    (h1 : IsZero (Work.Homology.singHomology Work.Homology.ZMod (k + 1) (simplex n)))
    (h2 : IsZero (Work.Homology.singHomology Work.Homology.ZMod k (simplex n))) :
    IsIso (Work.Homology.pairδ Work.Homology.ZMod (simplex n) (simplexBoundary n) k) := by
  have hf : (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (Work.Homology.relProj Work.Homology.ZMod (simplex n) (simplexBoundary n)) (k + 1))
      (Work.Homology.pairδ Work.Homology.ZMod (simplex n) (simplexBoundary n) k)
      ((Work.Homology.pairSeq_shortExact Work.Homology.ZMod (simplex n)
        (simplexBoundary n)).comp_δ (k + 1) k (by simp))).f = 0 := h1.eq_of_src _ 0
  have hmono : Mono (Work.Homology.pairδ Work.Homology.ZMod (simplex n) (simplexBoundary n) k) :=
    (ShortComplex.exact_iff_mono _ hf).1
      (Work.Homology.pairHomRel_exact Work.Homology.ZMod (simplex n) (simplexBoundary n) k)
  have hg : (ShortComplex.mk
      (Work.Homology.pairδ Work.Homology.ZMod (simplex n) (simplexBoundary n) k)
      (HomologicalComplex.homologyMap
        (Work.Homology.inclChain Work.Homology.ZMod (simplex n) (simplexBoundary n)) k)
      ((Work.Homology.pairSeq_shortExact Work.Homology.ZMod (simplex n)
        (simplexBoundary n)).δ_comp (k + 1) k (by simp))).g = 0 :=
    h2.eq_of_tgt _ 0
  have hepi : Epi (Work.Homology.pairδ Work.Homology.ZMod (simplex n) (simplexBoundary n) k) :=
    (ShortComplex.exact_iff_epi _ hg).1
      (Work.Homology.pairHomA_exact Work.Homology.ZMod (simplex n) (simplexBoundary n) k)
  exact isIso_of_mono_of_epi _

end

end Work.HomologyExtra
