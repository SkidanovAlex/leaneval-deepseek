import Mathlib
import Submission.Work.Whitney.PairDet
import Submission.Work.Whitney.DoubleDetC

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

/-- The range of a composite of continuous linear maps is the image of the range of the second map
under the first: the continuous linear version of `LinearMap.range_comp`. -/
private lemma range_comp_clm {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (A : F →L[𝕜] G) (B : E →L[𝕜] F) :
    (A ∘L B).range = Submodule.map (A : F →ₗ[𝕜] G) B.range := by
  ext x
  rw [LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨B y, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩

/-- Two arbitrary continuous linear maps `A, B : ℝⁿ → ℝ^{2n}` have complementary ranges exactly
when the determinant of `pairEquiv n ∘ (A coprod B)` is nonzero.  This is the two-map form of
`Work.Whitney.doubleDetRep_ne_zero_iff`. -/
private theorem det_coprod_ne_zero_iff {n : ℕ}
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))) :
    LinearMap.det (((Work.Projection.pairEquiv n).toLinearMap).comp
      ((A.coprod B).toLinearMap)) ≠ 0 ↔ A.range ⊔ B.range = ⊤ := by
  set Ap : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) := A with hAp
  set Aq : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) := B with hAq
  set L : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2 * n)) := Ap.coprod Aq with hL
  set Φ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    ((Work.Projection.pairEquiv n).toLinearMap).comp L.toLinearMap with hΦ
  have hdetiff : (LinearMap.det Φ ≠ 0) ↔ Function.Injective ⇑Φ := by
    rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
  rw [hdetiff]
  have hinjiff : Function.Injective ⇑Φ ↔ Function.Injective ⇑(L.toLinearMap) := by
    constructor
    · intro h x y hxy
      apply h
      simp only [hΦ, LinearMap.comp_apply, hxy]
    · intro h x y hxy
      apply h
      have := congrArg (⇑((Work.Projection.pairEquiv n).symm)) hxy
      simpa only [hΦ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        using this
  have hLrange : L.toLinearMap.range = Ap.range ⊔ Aq.range := by
    rw [hL, ContinuousLinearMap.coe_coprod, LinearMap.range_coprod]
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    omega
  have hiff : Function.Injective ⇑(L.toLinearMap) ↔ Ap.range ⊔ Aq.range = ⊤ := by
    rw [← hLrange, LinearMap.range_eq_top]
    exact LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
  rw [hinjiff, hiff, hAp, hAq]

-- FIXED STATEMENT (after review): the review found that `MDifferentiableAt` of the chart
-- *inverse* alone is not enough (a cube-type chart inverse has vanishing derivative), so we also
-- assume that the charts themselves are differentiable at the two points.  Then
-- `mfderiv cᵢ p ∘ mfderiv cᵢ.symm (cᵢ p) = id` (chain rule applied to `cᵢ.symm ∘ cᵢ = id` near `p`)
-- makes `mfderiv cᵢ.symm (cᵢ p)` surjective, and the two ranges agree.
--
-- Suggested proof:
--  * generalise `Work.Whitney.doubleDetRep_ne_zero_iff` (DoubleDetC.lean, whose proof is already
--    written in the two-map form with `Ap := fderiv ℝ g u`, `Aq := fderiv ℝ g v`) to the statement
--      `LinearMap.det ((pairEquiv n).toLinearMap |>.comp ((A.coprod B).toLinearMap)) ≠ 0 ↔
--        A.range ⊔ B.range = ⊤`
--    for arbitrary `A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2*n))`; then
--    `pairDet f c₁ c₂ p q ≠ 0 ↔ (fderiv ℝ (f ∘ c₁.symm) (c₁ p)).range ⊔
--      (fderiv ℝ (f ∘ c₂.symm) (c₂ q)).range = ⊤` is `rfl`/`Iff.rfl`-level;
--  * chain rule (`mfderiv_comp`) for `f ∘ c₁.symm` at `c₁ p`, using `c₁.left_inv hp` to identify
--    `c₁.symm (c₁ p)` with `p`, gives
--    `fderiv ℝ (f ∘ c₁.symm) (c₁ p) = mfderiv f p ∘L mfderiv c₁.symm (c₁ p)`
--    (`mfderiv` of a map between vector spaces is `fderiv`);
--  * `mfderiv c₁.symm (c₁ p)` surjective gives
--    `(mfderiv f p ∘L mfderiv c₁.symm (c₁ p)).range = (mfderiv f p).range`
--    (`LinearMap.range_comp`, `Submodule.map_top`).
theorem pairDet_ne_zero_iff {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (p q : M)
    (hp : p ∈ c₁.source) (hq : q ∈ c₂.source)
    (hc₁ : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c₁ p)
    (hc₂ : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c₂ q)
    (hs₁ : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c₁.symm (c₁ p))
    (hs₂ : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c₂.symm (c₂ q))
    (hf₁ : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p)
    (hf₂ : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q) :
    Work.Whitney.pairDet f c₁ c₂ p q ≠ 0 ↔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q).range = ⊤ := by
  -- The derivative of the inverse of a chart is surjective: differentiate `c.symm ∘ c = id`
  -- near `p` with the chain rule.
  have hsurj₁ : (mfderiv (𝓡 n) (𝓡 n) c₁.symm (c₁ p)).range = ⊤ := by
    have heq : (c₁.symm ∘ c₁) =ᶠ[𝓝 p] (id : M → M) := by
      filter_upwards [c₁.open_source.mem_nhds hp] with x hx
      exact c₁.left_inv hx
    have hid : mfderiv (𝓡 n) (𝓡 n) (c₁.symm ∘ c₁) p
        = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) p) := by
      rw [Filter.EventuallyEq.mfderiv_eq heq, mfderiv_id]; ext v; rfl
    have hcomp := mfderiv_comp (f := c₁) (x := p) (g := (c₁.symm : EuclideanSpace ℝ (Fin n) → M))
      hs₁ hc₁
    have hid2 : (mfderiv (𝓡 n) (𝓡 n) c₁.symm (c₁ p)).comp (mfderiv (𝓡 n) (𝓡 n) c₁ p)
        = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) p) := by
      rw [← hcomp]
      exact hid
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨(mfderiv (𝓡 n) (𝓡 n) c₁ p) y, ?_⟩
    exact congrArg (fun L => L y) hid2
  have hsurj₂ : (mfderiv (𝓡 n) (𝓡 n) c₂.symm (c₂ q)).range = ⊤ := by
    have heq : (c₂.symm ∘ c₂) =ᶠ[𝓝 q] (id : M → M) := by
      filter_upwards [c₂.open_source.mem_nhds hq] with x hx
      exact c₂.left_inv hx
    have hid : mfderiv (𝓡 n) (𝓡 n) (c₂.symm ∘ c₂) q
        = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) q) := by
      rw [Filter.EventuallyEq.mfderiv_eq heq, mfderiv_id]; ext v; rfl
    have hcomp := mfderiv_comp (f := c₂) (x := q) (g := (c₂.symm : EuclideanSpace ℝ (Fin n) → M))
      hs₂ hc₂
    have hid2 : (mfderiv (𝓡 n) (𝓡 n) c₂.symm (c₂ q)).comp (mfderiv (𝓡 n) (𝓡 n) c₂ q)
        = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) q) := by
      rw [← hcomp]
      exact hid
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨(mfderiv (𝓡 n) (𝓡 n) c₂ q) y, ?_⟩
    exact congrArg (fun L => L y) hid2
  -- The range of the chart representation is the range of the manifold derivative.
  have hA : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₁.symm u)) (c₁ p)).range
      = (mfderiv (𝓡 n) (𝓡 (2 * n)) f p).range := by
    let B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      mfderiv (𝓡 n) (𝓡 n) c₁.symm (c₁ p)
    let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
      mfderiv (𝓡 n) (𝓡 (2 * n)) f (c₁.symm (c₁ p))
    have hB : B.range = ⊤ := hsurj₁
    have hchainA : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₁.symm u)) (c₁ p)
        = A ∘L B := by
      have h := mfderiv_comp (f := (c₁.symm : EuclideanSpace ℝ (Fin n) → M)) (x := c₁ p)
        (g := f) (by simpa [c₁.left_inv hp] using hf₁) hs₁
      have h2 : mfderiv (𝓡 n) (𝓡 (2 * n)) (f ∘ c₁.symm) (c₁ p)
          = fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₁.symm u)) (c₁ p) :=
        mfderiv_eq_fderiv
      rw [h2] at h
      exact h
    rw [hchainA, range_comp_clm, hB, Submodule.map_top]
    exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) =>
      L.range) (mfderiv_congr_point (f := f) (c₁.left_inv hp))
  have hB' : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₂.symm u)) (c₂ q)).range
      = (mfderiv (𝓡 n) (𝓡 (2 * n)) f q).range := by
    let B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      mfderiv (𝓡 n) (𝓡 n) c₂.symm (c₂ q)
    let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
      mfderiv (𝓡 n) (𝓡 (2 * n)) f (c₂.symm (c₂ q))
    have hB : B.range = ⊤ := hsurj₂
    have hchainA : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₂.symm u)) (c₂ q)
        = A ∘L B := by
      have h := mfderiv_comp (f := (c₂.symm : EuclideanSpace ℝ (Fin n) → M)) (x := c₂ q)
        (g := f) (by simpa [c₂.left_inv hq] using hf₂) hs₂
      have h2 : mfderiv (𝓡 n) (𝓡 (2 * n)) (f ∘ c₂.symm) (c₂ q)
          = fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f (c₂.symm u)) (c₂ q) :=
        mfderiv_eq_fderiv
      rw [h2] at h
      exact h
    rw [hchainA, range_comp_clm, hB, Submodule.map_top]
    exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) =>
      L.range) (mfderiv_congr_point (f := f) (c₂.left_inv hq))
  rw [pairDet, det_coprod_ne_zero_iff, hA, hB']
  rfl

end Work.Whitney
