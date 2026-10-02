import Mathlib
import Submission.Work.Serre.TripleCohLES

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

/-- **A relative class extends uniquely through a triple when the obstruction and the ambiguity
vanish.**

Let `S ⊆ T ⊆ X` and let `n` be a degree in which the relative cohomology `H^n(X,T)` of the *upper*
pair vanishes and the connecting target `H^{n+1}(X,T)` vanishes.  Then every class in
`H^n(T, S∩T)` is the restriction of a unique class in `H^n(X,S)`.

The restriction is `tripleRestr` of the triple LES proved in `Submission/Work/Serre/TripleCohLES.lean`
(see `tripleCoh_exact₃`, `tripleCoh_exact₁` there): its image is the kernel of the connecting map
`tripleCohδ : H^n(T,S) → H^{n+1}(X,T)`, which is zero by `h2`; and its kernel is the image of the
forgetful map `H^n(X,T) → H^n(X,S)`, which is zero by `h1`.  This is the step that produces the Thom
class `U ∈ H^{r+1}(cyl q, Set.range (cylIncl q))` from the class over the old part in the cellular
induction (with `n = r+1`, `X = cyl q`, `S = Set.range (cylIncl q)`,
`T = (cylRetract q) ⁻¹' Set.range (attachIncl (D-2) Γ ι f) ∪ Set.range (cylIncl q)`). -/
theorem relCoh_extension (X : TopCat) (S T : Set X) (hST : S ⊆ T) (n : ℕ)
    (h1 : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ n X T))
    (h2 : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (n + 1) X T))
    (y : Work.Thom.RelCoh ℚ n (TopCat.of T) {x : ↥T | (x : X) ∈ S}) :
    ∃ U : Work.Thom.RelCoh ℚ n X S,
      (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ X S T hST) n).hom U = y ∧
        ∀ U' : Work.Thom.RelCoh ℚ n X S,
          (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ X S T hST) n).hom U' = y →
            U' = U := by
  -- The connecting map vanishes because its target `H^{n+1}(X,T)` is zero.
  have hδ : (Work.Serre.tripleCohδ ℚ X S T hST n) = 0 :=
    h2.eq_zero_of_tgt (Work.Serre.tripleCohδ ℚ X S T hST n)
  have hδ' : ModuleCat.Hom.hom (Work.Serre.tripleCohδ ℚ X S T hST n) = 0 := by
    rw [hδ]; rfl
  -- The forgetful map vanishes because its source `H^n(X,T)` is zero.
  have hincl : (HomologicalComplex.homologyMap (Work.Serre.tripleIncl ℚ X S T hST) n) = 0 :=
    h1.eq_zero_of_src (HomologicalComplex.homologyMap (Work.Serre.tripleIncl ℚ X S T hST) n)
  have hincl' : ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (Work.Serre.tripleIncl ℚ X S T hST) n) = 0 := by
    rw [hincl]; rfl
  -- Exactness at `H^n(T,S)`: the restriction is surjective.
  have hsurj : Function.Surjective
      (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ X S T hST) n)) := by
    rw [← LinearMap.range_eq_top, Work.Serre.tripleCoh_exact₃_range ℚ X S T hST n, hδ',
      LinearMap.ker_zero]
  -- Exactness at `H^n(X,S)`: the restriction is injective.
  have hinj : Function.Injective
      (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ X S T hST) n)) := by
    rw [← LinearMap.ker_eq_bot, ← Work.Serre.tripleCoh_exact₂_range ℚ X S T hST n, hincl',
      LinearMap.range_zero]
  obtain ⟨U, hU⟩ := hsurj y
  exact ⟨U, hU, fun U' hU' => hinj (by rw [hU', hU])⟩

end Work.Serre
