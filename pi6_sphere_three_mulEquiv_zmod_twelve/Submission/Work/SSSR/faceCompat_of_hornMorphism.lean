import Mathlib
import Submission.Work.SSSR.HornDefs
import Submission.Work.SSSR.morphSimplex_naturality_apply
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory
noncomputable section

/-- The face case of `Work.SSSR.morphSimplex_naturality_apply`: restricting an `(m+1)`-simplex
along the `p`-th face map `δ p` amounts to precomposing the corresponding continuous map with
`stdSimplex.map (Fin.succAbove p)`. -/
theorem morphSimplex_delta_apply {X : Type} [TopologicalSpace X] {m : ℕ}
    (σ : SSet.stdSimplex.obj (SimplexCategory.mk (m + 1)) ⟶ TopCat.toSSet.obj (TopCat.of X))
    (p : Fin (m + 2)) (z : stdSimplex ℝ (Fin (m + 1))) :
    ⇑(morphSimplex m X (SSet.stdSimplex.δ p ≫ σ)) z =
      ⇑(morphSimplex (m + 1) X σ) (stdSimplex.map (Fin.succAbove p) z) := by
  rw [show SSet.stdSimplex.δ p = SSet.stdSimplex.map (SimplexCategory.δ p) from rfl]
  have h := morphSimplex_naturality_apply (k := m) (m := m + 1) (φ := SimplexCategory.δ p) σ z
  rwa [SimplexCategory.coe_δ] at h

/-- **Face compatibility, shifted form.**  For a morphism `f` out of the horn `Λ[m+2, i]`, the
faces `j < l` (both different from `i`) agree on their common codimension-`2` face. -/
theorem faceCompat_gen {X : Type} [TopologicalSpace X] {m : ℕ} {i : Fin (m + 3)}
    (f : (SSet.horn (m + 2) i).toSSet ⟶ TopCat.toSSet.obj (TopCat.of X)) :
    ∀ (j l : Fin (m + 3)) (hj : j ≠ i) (hl : l ≠ i) (hjl : j < l),
      ⇑(faceSimplex f j hj) ∘
          (stdSimplex.map ((l.pred (Fin.ne_zero_of_lt hjl)).succAbove)) =
      ⇑(faceSimplex f l hl) ∘
          (stdSimplex.map ((j.castPred (Fin.ne_last_of_lt hjl)).succAbove)) := by
  intro j l hj hl hjl
  funext z
  simp only [Function.comp_apply]
  -- the two corners of `Δ[m+2]` cut out by the faces `j` and `l` coincide
  have key : SSet.stdSimplex.δ (l.pred (Fin.ne_zero_of_lt hjl)) ≫ (SSet.horn.ι i j hj ≫ f) =
      SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjl)) ≫ (SSet.horn.ι i l hl ≫ f) := by
    simpa only [Category.assoc] using SSet.horn.IsCompatible.of_hom (n := m + 1) f j l hj hl hjl
  simp only [faceSimplex]
  rw [← morphSimplex_delta_apply (σ := SSet.horn.ι i j hj ≫ f)
        (p := l.pred (Fin.ne_zero_of_lt hjl)) z,
      ← morphSimplex_delta_apply (σ := SSet.horn.ι i l hl ≫ f)
        (p := j.castPred (Fin.ne_last_of_lt hjl)) z]
  rw [key]

/-- The faces of a morphism from a horn are compatible on their common codimension-`2` face. -/
theorem faceCompat_of_hornMorphism {X : Type} [TopologicalSpace X] {n : ℕ} {i : Fin (n + 2)}
    (f : (SSet.horn (n + 1) i).toSSet ⟶ TopCat.toSSet.obj (TopCat.of X)) :
    ∀ (j l : Fin (n + 2)) (hj : j ≠ i) (hl : l ≠ i) (hjl : j < l),
      ⇑(Work.SSSR.faceSimplex f j hj) ∘
          (stdSimplex.map ((l.pred (Fin.ne_zero_of_lt hjl)).succAbove)) =
      ⇑(Work.SSSR.faceSimplex f l hl) ∘
          (stdSimplex.map ((j.castPred (Fin.ne_last_of_lt hjl)).succAbove)) := by
  rcases n with _ | m
  · -- `Λ[1, i]` has two faces, so `j ≠ i`, `l ≠ i` force `j = l`, contradicting `j < l`
    intro j l hj hl hjl
    have h : j = l := by fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all
    exact absurd hjl (by simp [h])
  · exact faceCompat_gen (m := m) f

end

end Work.SSSR
