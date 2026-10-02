import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Cohomology.Endgame.tripleLESSurj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-!
# Shrinking a pair when the third term of its triple vanishes

Let `A ⊆ A' ⊆ X` be subsets and consider the short exact sequence of the triple,
`0 ⟶ C^*(X,A') ⟶ C^*(X,A) ⟶ C^*(A', A'∩A) ⟶ 0` (`Work.Cohomology.Endgame.relCohTriple_shortExact`).
If the cohomology of the pair `(A', A'∩A)` vanishes in all degrees, then the inclusion
`C^*(X,A') ⊆ C^*(X,A)` is a quasi-isomorphism:

  `H^{n}(X,A') ≅ H^{n}(X,A)`.

This is the standard "shrinking" step in the proof of the good-pair theorem: it lets one replace the
pair `(X,A)` by a pair `(X,A')` with a smaller second member, provided the difference
`(A', A'∩A)` is acyclic.
-/

namespace Work.ThomBordism.Grassmann

open CategoryTheory

noncomputable section

/-- **Shrinking: `H^{n+1}(X,A') ≅ H^{n+1}(X,A)` when the pair `(A', A'∩A)` is acyclic.** -/
theorem relCohomology_iso_of_tripleVanishing (X : TopCat) (A A' : Set X) (h : A ⊆ A')
    (hzero : ∀ j : ℕ, Subsingleton (Work.Cohomology.relCohomology ℤ (TopCat.of ↥A')
      ((Subtype.val : ↥A' → ↑X) ⁻¹' A) j)) (m : ℕ) :
    Nonempty (Work.Cohomology.relCohomology ℤ X A' (m + 1) ≃ₗ[ℤ]
      Work.Cohomology.relCohomology ℤ X A (m + 1)) := by
  have hh : ∀ x ∈ Work.Cohomology.Endgame.preA X A A',
      (CategoryTheory.ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A :=
    fun x hx => hx
  have hS : (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).ShortExact :=
    Work.Cohomology.Endgame.relCohTriple_shortExact X A A' h hh
  have hij : (ComplexShape.up ℕ).Rel m (m + 1) := by simp [ComplexShape.up]
  -- the homology map of the first map of the triple sequence
  have hsurj : Function.Surjective (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap
        (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).f (m + 1))) := by
    haveI : Subsingleton ((Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).X₃.homology
        (m + 1)) := hzero (m + 1)
    have hex := hS.homology_exact₂ (m + 1)
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
    have hker : LinearMap.ker (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap
          (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).g (m + 1))) = ⊤ :=
      LinearMap.ker_eq_top.mpr (LinearMap.ext (fun y => Subsingleton.elim _ _))
    rw [hker] at hex
    intro y
    have hy : y ∈ LinearMap.range (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap
          (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).f (m + 1))) := by
      rw [hex]; exact Submodule.mem_top
    exact hy
  have hinj : Function.Injective (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap
        (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).f (m + 1))) := by
    haveI : Subsingleton ((Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).X₃.homology
        m) := hzero m
    have hδ : ModuleCat.Hom.hom (hS.δ m (m + 1) hij) = 0 := by
      apply LinearMap.ext
      intro y
      change ModuleCat.Hom.hom (hS.δ m (m + 1) hij) y = 0
      have hy : y = 0 := Subsingleton.elim y 0
      rw [hy, map_zero]
    have hex := hS.homology_exact₁ m (m + 1) hij
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
    rw [hδ, LinearMap.range_zero] at hex
    have hbot : LinearMap.ker (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap
          (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).f (m + 1))) = ⊥ :=
      hex.symm
    exact LinearMap.ker_eq_bot.mp hbot
  exact ⟨LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩⟩

end

end Work.ThomBordism.Grassmann
