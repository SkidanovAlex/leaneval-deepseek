import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.Geometry

namespace Work.RPB1a

/-- If a smooth embedding `γ` of the circle into `ℝ × ℝ` has image equal to the image of
`v : ℝ → ℂ` under the real-linear homeomorphism `Complex.equivRealProdCLM : ℂ ≃ ℝ × ℝ`,
then `Set.range v` is a Jordan curve. -/
theorem isJordanCurveSet_range_of_descend (v : ℝ → ℂ) (γ : Circle → ℝ × ℝ)
    (hemb : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hrange : Set.range γ = Complex.equivRealProdCLM '' Set.range v) :
    Work.RPB1a.IsJordanCurveSet (Set.range v) := by
  rw [IsJordanCurveSet]
  -- `γ` exhibits `Set.range γ` as a topological circle.
  have hγ : Nonempty (Circle ≃ₜ Set.range γ) := by
    refine ⟨(Homeomorph.Set.univ Circle).symm.trans ?_⟩
    refine (hemb.isEmbedding.homeomorphImage Set.univ).trans (Homeomorph.setCongr ?_)
    simp [Set.image_univ]
  -- `Complex.equivRealProdCLM` carries `Set.range v` onto `Set.range γ`.
  have he : Set.range v ≃ₜ Set.range γ :=
    (Complex.equivRealProdCLM.toHomeomorph.image (Set.range v)).trans
      (Homeomorph.setCongr (by rw [hrange]; rfl))
  obtain ⟨hγ⟩ := hγ
  exact ⟨he.trans hγ.symm⟩

end Work.RPB1a
