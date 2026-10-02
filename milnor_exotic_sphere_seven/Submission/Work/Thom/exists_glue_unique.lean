import Mathlib
import Submission.Work.Thom.Glue2
import Submission.Work.Cohomology.relCohMV_honest_les
import Submission.Work.Thom.nonempty_thomClass_of_disjoint_cover

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-!
# Uniqueness of the glued class

`Work.Thom.exists_glue` produces *some* global class restricting to a compatible pair `w` of piece
classes.  Here we show that the global class is unique as soon as the relative cohomology of the
overlap in degree `n - 1` is a subsingleton: the obstruction to uniqueness is the connecting map
`δ : Hᵐ⁻¹(U∩V) → Hᵐ(X,A)` (`m = n`), whose source vanishes by hypothesis.

In degree `n = 0` there is no connecting map and the injectivity of the two restrictions is the
general fact `Work.Thom.honestF_injective_zero`.
-/

namespace Work.Thom

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **Injectivity of `honestF` under a vanishing overlap.**  If `H^{m-1}(U ∩ V, U∩V∩A)` is a
subsingleton then the two restrictions `H^m(X,A) → H^m(U,U∩A) ⊞ H^m(V,V∩A)` are injective: their
kernel is the image of the connecting map `δ : H^{m-1}(U∩V, U∩V∩A) → H^m(X,A)`, which is zero. -/
theorem honestF_injective_of_subsingleton_overlap {X : TopCat} {A U V : Set X} (m : ℕ)
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hsub : Subsingleton (Work.Cohomology.pdCohSub X A (U ∩ V) (m - 1))) :
    Function.Injective (ModuleCat.Hom.hom (Work.Cohomology.honestF X A U V m)) := by
  rcases m with _ | k
  · exact honestF_injective_zero X A U V hU hV hcov
  · -- `m = k + 1`: `m - 1 = k`, and the source of `honestDelta` is a subsingleton
    haveI : Subsingleton (Work.Cohomology.pdCohSub X A (U ∩ V) k) := hsub
    have hdelta0 : ModuleCat.Hom.hom
        (Work.Cohomology.honestDelta X A U V hU hV hcov k) = 0 := by
      refine LinearMap.ext (fun x => ?_)
      rw [Subsingleton.elim x 0]
      simp
    have hex := Work.Cohomology.honest_exact₁ X A U V hU hV hcov k
    have h' : LinearMap.range
          (ModuleCat.Hom.hom (Work.Cohomology.honestDelta X A U V hU hV hcov k))
        = LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.honestF X A U V (k + 1))) :=
      ShortComplex.Exact.moduleCat_range_eq_ker hex
    rw [hdelta0, LinearMap.range_zero] at h'
    exact LinearMap.ker_eq_bot.mp h'.symm

/-- **The glued class is unique.**  A pair of piece-relative classes satisfying the overlap
condition is the restriction of at most one global class, because the overlap cohomology in degree
`n - 1` vanishes. -/
theorem exists_glue_unique {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι) (n : ℕ) {U V : Set B}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hUV : Subsingleton (Work.Cohomology.pdCohSub (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' U ∩ Z.proj ⁻¹' V) (n - 1)))
    (w : Work.Cohomology.pdCohBiprod (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)
    (h : (Work.Cohomology.honestG (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n).hom w = 0) :
    ∃! τ : Work.Thom.OpenThom Z n, (Work.Cohomology.honestF (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n).hom τ = w := by
  obtain ⟨τ, hτ⟩ := exists_glue Z n hU hV hcov w h
  refine ⟨τ, hτ, ?_⟩
  have hcov' : Z.proj ⁻¹' U ∪ Z.proj ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, hcov, Set.preimage_univ]
  have hinj : Function.Injective (ModuleCat.Hom.hom (Work.Cohomology.honestF
      (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (Z.proj ⁻¹' U) (Z.proj ⁻¹' V) n)) :=
    honestF_injective_of_subsingleton_overlap n (hU.preimage Z.continuous_proj)
      (hV.preimage Z.continuous_proj) hcov' hUV
  intro τ' hτ'
  exact hinj (by rw [hτ', hτ])

end

end Work.Thom
