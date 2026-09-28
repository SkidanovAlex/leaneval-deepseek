import Mathlib
import Submission.Work.Stems.HurewiczSphere

set_option synthInstance.maxHeartbeats 400000

/-!
# The complement of a point of `Sⁿ` is contractible

Stereographic projection identifies `Sⁿ ∖ {y}` with the hyperplane `(ℝ∙y)ᗮ ≅ ℝⁿ`; the straight-line
contraction of that vector space to a point gives a *based* contraction of the complement.  As a
consequence, a map `Sⁿ → Sⁿ` whose image misses a point is homotopic to the corresponding constant
map, relative to a fixed base point.

This is the last step of the smooth degree-theoretic proof of Hopf's theorem
(`Work.Stems.smooth_selfmap_degree_zero_homotopic_rel`): once a homotopy has removed all preimages
of a regular value, the map misses a point and hence is null-homotopic.
-/

open scoped Topology unitInterval
open Metric

namespace Work.Stems

noncomputable section

/-- **Stereographic projection** identifies the complement of `y : Sⁿ` with the hyperplane of `ℝⁿ⁺¹`
orthogonal to `y`. -/
def sphereComplHomeo (n : ℕ) (y : sphere n) :
    {z : sphere n // z ≠ y} ≃ₜ (ℝ ∙ (y : EuclideanSpace ℝ (Fin (n + 1))))ᗮ :=
  (((stereographic (norm_eq_of_mem_sphere y)).symm).toHomeomorphSourceTarget).symm.trans
    (Homeomorph.Set.univ ((ℝ ∙ (y : EuclideanSpace ℝ (Fin (n + 1))))ᗮ))

/-- The straight-line ("affine") contraction of a real topological vector space to a point. -/
def affineContraction (E : Type*) [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] (v₀ : E) : C(I × E, E) where
  toFun p := (1 - (p.1 : ℝ)) • p.2 + (p.1 : ℝ) • v₀
  continuous_toFun := by fun_prop

/-- **The complement of a point of `Sⁿ` is contractible** (to any of its points): the based
contraction of the complement of `y` at the point `x₀ ≠ y`. -/
def sphereComplContraction (n : ℕ) (y x₀ : sphere n) (h : x₀ ≠ y) :
    C(I × {z : sphere n // z ≠ y}, {z : sphere n // z ≠ y}) :=
  ((sphereComplHomeo n y).symm : C((ℝ ∙ (y : EuclideanSpace ℝ (Fin (n + 1))))ᗮ,
      {z : sphere n // z ≠ y})).comp
    ((affineContraction ((ℝ ∙ (y : EuclideanSpace ℝ (Fin (n + 1))))ᗮ)
        ((sphereComplHomeo n y) ⟨x₀, h⟩)).comp
      ((ContinuousMap.fst).prodMk
        (((sphereComplHomeo n y) :
          C({z : sphere n // z ≠ y}, (ℝ ∙ (y : EuclideanSpace ℝ (Fin (n + 1))))ᗮ)).comp
          ContinuousMap.snd)))

theorem affineContraction_zero (E : Type*) [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] (v₀ w : E) :
    affineContraction E v₀ (0, w) = w := by
  simp [affineContraction]

theorem affineContraction_one (E : Type*) [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] (v₀ w : E) :
    affineContraction E v₀ (1, w) = v₀ := by
  simp [affineContraction]

theorem affineContraction_self (E : Type*) [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] (v₀ : E) (t : I) :
    affineContraction E v₀ (t, v₀) = v₀ := by
  simp only [affineContraction, ContinuousMap.coe_mk]
  rw [← add_smul, sub_add_cancel, one_smul]

/-- The based contraction of the complement of `y` fixes its base point. -/
theorem sphereComplContraction_self (n : ℕ) (y x₀ : sphere n) (h : x₀ ≠ y) (t : I) :
    sphereComplContraction n y x₀ h (t, ⟨x₀, h⟩) = ⟨x₀, h⟩ := by
  show (sphereComplHomeo n y).symm
    (affineContraction _ ((sphereComplHomeo n y) ⟨x₀, h⟩) (t, (sphereComplHomeo n y) ⟨x₀, h⟩)) =
      ⟨x₀, h⟩
  rw [affineContraction_self]
  exact (sphereComplHomeo n y).symm_apply_apply ⟨x₀, h⟩

theorem sphereComplContraction_zero (n : ℕ) (y x₀ : sphere n) (h : x₀ ≠ y) (z) :
    sphereComplContraction n y x₀ h (0, z) = z := by
  show (sphereComplHomeo n y).symm
    (affineContraction _ ((sphereComplHomeo n y) ⟨x₀, h⟩) (0, (sphereComplHomeo n y) z)) = z
  rw [affineContraction_zero]
  exact (sphereComplHomeo n y).symm_apply_apply z

theorem sphereComplContraction_one (n : ℕ) (y x₀ : sphere n) (h : x₀ ≠ y) (z) :
    sphereComplContraction n y x₀ h (1, z) = ⟨x₀, h⟩ := by
  show (sphereComplHomeo n y).symm
    (affineContraction _ ((sphereComplHomeo n y) ⟨x₀, h⟩) (1, (sphereComplHomeo n y) z)) =
      ⟨x₀, h⟩
  rw [affineContraction_one]
  exact (sphereComplHomeo n y).symm_apply_apply ⟨x₀, h⟩

theorem homotopicRel_const_of_misses (n : ℕ) {b x₀ y : sphere n} (g : C(sphere n, sphere n))
    (hg : ∀ z, g z ≠ y) (hgb : g b = x₀) :
    ContinuousMap.HomotopicRel g (ContinuousMap.const _ x₀) {b} := by
  have hne : x₀ ≠ y := by
    rw [← hgb]
    exact hg b
  refine ⟨{ toFun := fun p => sphereComplContraction n y x₀ hne (p.1, ⟨g p.2, hg p.2⟩)
            continuous_toFun := continuous_subtype_val.comp
              ((sphereComplContraction n y x₀ hne).continuous.comp
                (continuous_fst.prodMk
                  (Continuous.subtype_mk (g.continuous.comp continuous_snd) _)))
            map_zero_left := fun z =>
              congrArg Subtype.val (sphereComplContraction_zero n y x₀ hne ⟨g z, hg z⟩)
            map_one_left := fun z =>
              congrArg Subtype.val (sphereComplContraction_one n y x₀ hne ⟨g z, hg z⟩)
            prop' := fun t z hz => by
              rw [Set.mem_singleton_iff] at hz
              subst hz
              have hfix := congrArg Subtype.val (sphereComplContraction_self n y x₀ hne t)
              have hz' : (⟨g z, hg z⟩ : {w : sphere n // w ≠ y}) = ⟨x₀, hne⟩ := Subtype.ext hgb
              show (↑((sphereComplContraction n y x₀ hne)
                (t, (⟨g z, hg z⟩ : {w : sphere n // w ≠ y}))) : sphere n) = g z
              rw [hz', hfix, hgb] }⟩

end

end Work.Stems
