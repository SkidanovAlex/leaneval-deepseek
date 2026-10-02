import Mathlib
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.ThomBordism.CofAtlas.range_mfderiv_v_eq_range_e

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The sign of `det (ℓ j ∘ Lv ∘ N)` is independent of the coframing index `j`

`Work.ThomBordism.LeadChapter.sgnZ_cofIndex` (see `ASSEMBLY.md`, step 5 of S1): in the notation of
`CofAtlas`, if `Lv` is a linear map whose range is the coframed subspace
`range (e (jx x) x) ⊆ ℝⁿ` (the case of the derivative of the level function), then for every
coframing index `j` active at `x` the sign of `det (ℓ j ∘ Lv ∘ N)` agrees with the sign of
`det (ℓ (jx x) ∘ Lv ∘ N)`, with `N : ℝᵏ → ℝ^{9+k}` arbitrary.

The mathematical content: `Lv = e (jx x) x ∘ (ℓ (jx x) ∘ Lv)` (because the range of `Lv` is the
range of `e (jx x) x`, on which `ℓ (jx x)` is a left inverse of `e (jx x) x`), so that
`det (ℓ j ∘ Lv ∘ N) = det (ℓ j ∘ e (jx x) x) · det (ℓ (jx x) ∘ Lv ∘ N)`.  The prefactor is
positive: the transition `α := ℓ (jx x) ∘ e j x : ℝᵏ → ℝᵏ` has positive determinant by the positive
cocycle condition `Cof.hpos`, and `(ℓ j ∘ e (jx x) x) ∘ α = 1` (both `e j x` and `e (jx x) x` land
in the fixed space of the projection `P x`), so `det (ℓ j ∘ e (jx x) x) = (det α)⁻¹ > 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism.LeadChapter

noncomputable section

/-- `sgnZ` is invariant under multiplication by a positive scalar. -/
theorem sgnZ_cofIndex_mul_pos {c r : ℝ} (hc : 0 < c) : sgnZ (c * r) = sgnZ r := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [sgnZ, if_neg (not_lt.mpr (le_of_lt (mul_neg_of_pos_of_neg hc h))), sgnZ,
      if_neg (not_lt.mpr (le_of_lt h))]
  · subst h; simp [sgnZ]
  · rw [sgnZ, if_pos (mul_pos hc h), sgnZ, if_pos h]

/-- The determinant of a composition of continuous linear endomorphisms of `ℝᵏ` is the product of
the determinants. -/
theorem sgnZ_cofIndex_det_comp {k : ℕ}
    (f g : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    LinearMap.det ((f.comp g : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
        EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
      = LinearMap.det (f : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
        * LinearMap.det (g : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := by
  rw [show ((f.comp g : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
        EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
      = ((f : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))).comp
        ((g : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))) from rfl]
  rw [LinearMap.det_comp]

open scoped Manifold ContDiff Topology in
theorem sgnZ_cofIndex (k n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace (CofAtlas.NN k)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (CofAtlas.NN k)) ((⊤ : ENat) : WithTop ENat) M]
    (D : CofAtlas.Cof k n M) (x : D.S.Pre)
    (Lv : CofAtlas.ModN k →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : EuclideanSpace ℝ (Fin k) →L[ℝ] CofAtlas.ModN k)
    (hrange : LinearMap.range Lv.toLinearMap
      = LinearMap.range (D.e (D.jx x) (x : M)).toLinearMap)
    (j : Fin D.m) (hj : (x : M) ∈ D.U j) :
    Work.ThomBordism.LeadChapter.sgnZ (LinearMap.det (((D.ℓ j).comp (Lv.comp N)) :
        EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)))
      = Work.ThomBordism.LeadChapter.sgnZ (LinearMap.det (((D.ℓ (D.jx x)).comp (Lv.comp N)) :
        EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))) := by
  -- The fixed space of `P x` is the range of `e (jx x) x`.
  have hfix : ((LinearMap.range (D.e (D.jx x) (x : M)).toLinearMap :
      Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))
      = {z | D.P (x : M) z = z} := by
    rw [← Work.ThomBordism.CofAtlas.range_mfderiv_v_eq_range_e D x (D.mem_src_self x)]
    exact D.hlink (x : M) x.2
  -- `range (e j x) ⊆ range (e (jx x) x)`.
  have hle : LinearMap.range (D.e j (x : M)).toLinearMap
      ≤ LinearMap.range (D.e (D.jx x) (x : M)).toLinearMap := by
    rintro z ⟨c, rfl⟩
    have hmem : D.e j (x : M) c ∈ (LinearMap.range (D.e (D.jx x) (x : M)).toLinearMap :
        Set (EuclideanSpace ℝ (Fin n))) := by
      rw [hfix]
      exact (D.hℓe j (x : M) hj c).2
    exact hmem
  -- `e (jx x) x` retracts onto its range along `ℓ (jx x)`.
  have hretr : ∀ w : EuclideanSpace ℝ (Fin n),
      w ∈ (LinearMap.range (D.e (D.jx x) (x : M)).toLinearMap : Set (EuclideanSpace ℝ (Fin n))) →
      D.e (D.jx x) (x : M) (D.ℓ (D.jx x) w) = w := by
    rintro w ⟨c, rfl⟩
    exact congrArg (fun t => D.e (D.jx x) (x : M) t)
      (D.hℓe (D.jx x) (x : M) (D.mem_U_jx x) c).1
  -- `Lv = e (jx x) x ∘ (ℓ (jx x) ∘ Lv)`.
  have hE0D1 : (D.e (D.jx x) (x : M)).comp ((D.ℓ (D.jx x)).comp Lv) = Lv := by
    apply ContinuousLinearMap.ext
    intro v
    exact hretr (Lv v) (by rw [← hrange]; exact ⟨v, rfl⟩)
  -- `(ℓ j ∘ e (jx x) x) ∘ (ℓ (jx x) ∘ e j x) = 1`.
  have hCα : ((D.ℓ j).comp (D.e (D.jx x) (x : M))).comp
      ((D.ℓ (D.jx x)).comp (D.e j (x : M))) = 1 := by
    apply ContinuousLinearMap.ext
    intro c
    show D.ℓ j (D.e (D.jx x) (x : M) (D.ℓ (D.jx x) (D.e j (x : M) c))) = c
    rw [hretr (D.e j (x : M) c) (hle ⟨c, rfl⟩)]
    exact (D.hℓe j (x : M) hj c).1
  -- The transition `ℓ (jx x) ∘ e j x` has positive determinant (positive cocycle condition).
  have hdetα : 0 < LinearMap.det (((D.ℓ (D.jx x)).comp (D.e j (x : M))) :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :=
    D.hpos j (D.jx x) (x : M) hj (D.mem_U_jx x)
  -- Hence `det (ℓ j ∘ e (jx x) x) = (det α)⁻¹ > 0`.
  have hdetCα : LinearMap.det (((D.ℓ j).comp (D.e (D.jx x) (x : M))) :
        EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
      * LinearMap.det (((D.ℓ (D.jx x)).comp (D.e j (x : M))) :
        EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) = 1 := by
    rw [← sgnZ_cofIndex_det_comp ((D.ℓ j).comp (D.e (D.jx x) (x : M)))
      ((D.ℓ (D.jx x)).comp (D.e j (x : M))), hCα]
    simp
  have hdetC : 0 < LinearMap.det (((D.ℓ j).comp (D.e (D.jx x) (x : M))) :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :=
    pos_of_mul_pos_left (by rw [hdetCα]; norm_num) hdetα.le
  -- `ℓ j ∘ Lv ∘ N = (ℓ j ∘ e (jx x) x) ∘ (ℓ (jx x) ∘ Lv ∘ N)`.
  have hAcomp : (D.ℓ j).comp (Lv.comp N)
      = ((D.ℓ j).comp (D.e (D.jx x) (x : M))).comp ((D.ℓ (D.jx x)).comp (Lv.comp N)) := by
    apply ContinuousLinearMap.ext
    intro v
    show D.ℓ j (Lv (N v)) = D.ℓ j (D.e (D.jx x) (x : M) (D.ℓ (D.jx x) (Lv (N v))))
    rw [hretr (Lv (N v)) (by rw [← hrange]; exact ⟨N v, rfl⟩)]
  have hAcompL : (((D.ℓ j).comp (Lv.comp N)) :
        EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
      = (((((D.ℓ j).comp (D.e (D.jx x) (x : M))).comp
            ((D.ℓ (D.jx x)).comp (Lv.comp N))) :
          EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
        EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) :=
    congrArg (fun f : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) =>
      (f : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k))) hAcomp
  rw [hAcompL, sgnZ_cofIndex_det_comp ((D.ℓ j).comp (D.e (D.jx x) (x : M)))
    ((D.ℓ (D.jx x)).comp (Lv.comp N)), sgnZ_cofIndex_mul_pos hdetC]

end

end Work.ThomBordism.LeadChapter
