import Mathlib
import Submission.Work.Whitney.EuclidModel
import Submission.Work.Whitney.fderiv_euclidModel

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- The range of a composite of continuous linear maps is the image of the range of the second
under the first: the continuous linear version of `LinearMap.range_comp`. -/
private lemma comp_range_clm {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (A : F →L[𝕜] G) (B : E →L[𝕜] F) :
    (A.comp B).range = Submodule.map (A : F →ₗ[𝕜] G) B.range := by
  ext x
  rw [LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨B y, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩

/-- The range of `euclidOfLp n` is everything (it is a linear isomorphism onto `Fin n → ℝ`). -/
private lemma euclidOfLp_range' (n : ℕ) : (euclidOfLp n).range = ⊤ :=
  LinearMap.range_eq_top.mpr (fun z => ⟨lpOfEuclid n z, by simp⟩)

/-- **The new double point of the transported scaled model is transverse**: the two tangent images
at the two preimages of its double point span the whole space.

By `Work.Whitney.fderiv_euclidModel` the derivative at `scaledPt n lam a` is
`pairToE n ∘ (fderiv ℝ β a) ∘ euclidOfLp n` (the scaling cancels because `lam • euclidOfLp n u = a`
at that point), so its range is `pairToE n '' (fderiv ℝ β a).range`; similarly at `scaledPt n lam b`
the range is `pairToE n '' (fderiv ℝ β b).range`.  Their supremum is
`pairToE n '' ((fderiv ℝ β a).range ⊔ (fderiv ℝ β b).range)`, and the `coprod` hypothesis
(`det ≠ 0` for an endomorphism of `(Fin n → ℝ) × (Fin n → ℝ)`, whose range is the supremum of the
two ranges by `LinearMap.range_coprod`) makes the inner supremum equal to `⊤`; the transport
`pairToE n` is surjective, so the outer image is `⊤`. -/
theorem euclidModel_range_sup {n : ℕ} {lam : ℝ}
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) (a b : Fin n → ℝ)
    (hlam : 0 < lam) (hβab : β a = β b)
    (hdet : LinearMap.det (((fderiv ℝ β a).coprod (fderiv ℝ β b)).toLinearMap) ≠ 0) :
    (fderiv ℝ (Work.Whitney.euclidModel n lam β) (Work.Whitney.scaledPt n lam a)).range ⊔
        (fderiv ℝ (Work.Whitney.euclidModel n lam β) (Work.Whitney.scaledPt n lam b)).range
      = ⊤ := by
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  -- The `coprod` of the two derivatives is an endomorphism of `(Fin n → ℝ) × (Fin n → ℝ)` with
  -- non-zero determinant, hence surjective, hence of full range.
  have hFtop : (((fderiv ℝ β a).coprod (fderiv ℝ β b)).toLinearMap).range = ⊤ := by
    have hker : (((fderiv ℝ β a).coprod (fderiv ℝ β b)).toLinearMap).ker = ⊥ := by
      by_contra h
      exact hdet ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr h)
    exact LinearMap.range_eq_top.mpr
      (LinearMap.surjective_of_injective (LinearMap.ker_eq_bot.mp hker))
  -- Its range is the supremum of the two individual ranges.
  have hsupAB : (fderiv ℝ β a).range ⊔ (fderiv ℝ β b).range = ⊤ := by
    rw [← ContinuousLinearMap.range_coprod (fderiv ℝ β a) (fderiv ℝ β b)]
    exact hFtop
  -- The range of the derivative of `euclidModel` at `scaledPt n lam a` is the image under
  -- `pairToE n` of the range of `fderiv ℝ β a`.
  have hr_a : (fderiv ℝ (euclidModel n lam β) (scaledPt n lam a)).range
      = Submodule.map ((pairToE n) : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ]
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (fderiv ℝ β a).range := by
    rw [fderiv_euclidModel β hlam0 (scaledPt n lam a)]
    -- the scaling cancels at the transported double point
    have hpt : lam • euclidOfLp n (scaledPt n lam a) = a := by
      rw [scaledPt_eq, map_smul, euclidOfLp_lpOfEuclid, smul_smul, one_div,
        mul_inv_cancel₀ hlam0, one_smul]
    rw [hpt]
    rw [comp_range_clm, comp_range_clm, euclidOfLp_range', Submodule.map_top]
  have hr_b : (fderiv ℝ (euclidModel n lam β) (scaledPt n lam b)).range
      = Submodule.map ((pairToE n) : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ]
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (fderiv ℝ β b).range := by
    rw [fderiv_euclidModel β hlam0 (scaledPt n lam b)]
    have hpt : lam • euclidOfLp n (scaledPt n lam b) = b := by
      rw [scaledPt_eq, map_smul, euclidOfLp_lpOfEuclid, smul_smul, one_div,
        mul_inv_cancel₀ hlam0, one_smul]
    rw [hpt]
    rw [comp_range_clm, comp_range_clm, euclidOfLp_range', Submodule.map_top]
  rw [hr_a, hr_b]
  rw [← Submodule.map_sup]
  rw [hsupAB, Submodule.map_top]
  exact pairToE_range n

end Work.Whitney
