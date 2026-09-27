import Mathlib
import Submission.Work.Drive.cappingProjCoords

namespace Work.Drive

/-! ## Elementary algebra of a unit complex number

The two computations below are used for the cap coordinate (`(‖z₂‖/z₂)² = w²`) and for the disk
coordinate (`√2 z₁z₂/‖z₂‖ = d`) of the sphere lift. -/

private lemma mul_star_eq_one {w : ℂ} (hw : ‖w‖ = 1) : w * star w = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
  norm_num

private lemma star_mul_eq_one {w : ℂ} (hw : ‖w‖ = 1) : star w * w = 1 := by
  rw [mul_comm]; exact mul_star_eq_one hw

private lemma star_ne_zero_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) : star w ≠ 0 := by
  intro h
  have : star w * w = 0 := by rw [h, zero_mul]
  rw [star_mul_eq_one hw] at this
  exact one_ne_zero this

open Manifold in
open scoped Manifold ContDiff in
/-- **The sphere lift of a point of the cap solid torus.**  The identification
`Work.Drive.lensToProj : Work.Drive.LensSpace → ℝP³` is the descent of `projOfUnitSphere` through the
quotient map `phi : S³ → LensSpace` (`Work.Drive.lensToProj_phi : lensToProj (phi v) = projOfUnitSphere v`);
its definition goes through `Function.surjInv`, so nothing about it can be unfolded, and this statement
gives the explicit formula on the cap solid torus `CapTorus = S¹ × D²`.

Because the cap coordinate of `LensSpace` is `(‖z₂‖/z₂)²` — a *square* of a unit complex number — the
formula necessarily involves a chosen square root `w` of `circleOf θ` (the two choices differ by
`w ↦ -w`, which is the antipodal identification of the sphere, so the projective class does not depend
on the choice).  With such a `w` the sphere point of the class of `(θ, d)` is
`(d · w / √2, w̄ · √(1 - ‖d‖²/2)) ∈ ℂ² = ℝ⁴ = Eucl 3`, i.e. `Work.Drive.capProjVecOf w d`, a unit
vector (`Work.Drive.norm_capProjVecOf`) which never vanishes
(`Work.Drive.capProjVecOf_ne_zero`).

Route: put `V := capProjVecOf w d`, `v := ⟨V, norm_capProjVecOf ⋯⟩`; show `‖c₁ V‖ ≤ ‖c₂ V‖` (it is
`‖d‖/√2 ≤ √(1 - ‖d‖²/2)`), so the `if` in `phi` takes its cap branch and
`phi v = Quotient.mk'' (Sum.inl (capPt ⟨v, ⋯⟩))`; compute `capPt ⟨v, ⋯⟩ = (θ, d)`:
`(‖c₂ V‖/c₂ V)² = (1/w̄)² = w² = circleOf θ` (whence `circOf ⋯ = θ`, by `Work.Drive.circleOf_circOf`
and injectivity of `circleOf`, `Work.Drive.circleOf_injective`) and
`√2 c₁ V c₂ V / ‖c₂ V‖ = d w w̄ = d`.  Then
`lensToProj (phi v) = projOfUnitSphere v = Projectivization.mk ℝ v.1 ⋯`, and `v.1 = V` is `rfl`, so
the two sides are the same projective point up to the (irrelevant) non-vanishing proof
(`Work.Drive.projectivizationMk_congr` is available for that step). -/
theorem lensToProj_capTorus (θ : UnitAddCircle) (d : Metric.closedBall (0 : ℂ) 1) {w : ℂ}
    (hw : w ^ 2 = circleOf θ) :
    Work.Drive.lensToProj
        (Quotient.mk'' (Sum.inl (θ, d) : Work.Drive.CapTorus ⊕ Work.Drive.ConfTorus) :
          Work.Drive.LensSpace)
      = Projectivization.mk ℝ (Work.Drive.capProjVecOf w (d : ℂ))
          (Work.Drive.capProjVecOf_ne_zero (Work.Drive.norm_eq_one_of_sq_eq_circleOf hw)
            (Work.Drive.norm_coe_closedBall_le_one d)) := by
  have hw1 : ‖w‖ = 1 := norm_eq_one_of_sq_eq_circleOf hw
  have hd : ‖(d : ℂ)‖ ≤ 1 := norm_coe_closedBall_le_one d
  have hd0 : (0 : ℝ) ≤ ‖(d : ℂ)‖ := norm_nonneg _
  have hVnorm : ‖capProjVecOf w (d : ℂ)‖ = 1 := norm_capProjVecOf hw1 hd
  have hVmem : capProjVecOf w (d : ℂ) ∈ unitSphere 3 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hVnorm
  have hle : ‖c₁ (capProjVecOf w (d : ℂ))‖ ≤ ‖c₂ (capProjVecOf w (d : ℂ))‖ := by
    rw [show ‖c₁ (capProjVecOf w (d : ℂ))‖ = ‖(d : ℂ)‖ / Real.sqrt 2 from by
          rw [c₁_capProjVecOf, norm_div, norm_mul, hw1, mul_one]
          congr 1
          rw [Complex.norm_of_nonneg (Real.sqrt_nonneg 2)],
        show ‖c₂ (capProjVecOf w (d : ℂ))‖ = Real.sqrt (1 - ‖(d : ℂ)‖ ^ 2 / 2) from by
          rw [c₂_capProjVecOf, norm_mul, norm_star, hw1, one_mul]
          rw [Complex.norm_of_nonneg (Real.sqrt_nonneg _)]]
    rw [Real.le_sqrt (by positivity) (by nlinarith)]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  have hs_pos : 0 < Real.sqrt (1 - ‖(d : ℂ)‖ ^ 2 / 2) := sqrt_one_sub_pos hd
  have hnc2 : ‖c₂ (capProjVecOf w (d : ℂ))‖ = Real.sqrt (1 - ‖(d : ℂ)‖ ^ 2 / 2) := by
    rw [c₂_capProjVecOf, norm_mul, norm_star, hw1, one_mul]
    rw [Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hsC : ((Real.sqrt (1 - ‖(d : ℂ)‖ ^ 2 / 2) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hs_pos
  -- the cap coordinate of the sphere point is `circleOf θ`
  have hfirst : ((((‖c₂ (capProjVecOf w (d : ℂ))‖ : ℝ) : ℂ) / c₂ (capProjVecOf w (d : ℂ)))
        ^ 2) = circleOf θ := by
    have hratio : (((‖c₂ (capProjVecOf w (d : ℂ))‖ : ℝ) : ℂ) / c₂ (capProjVecOf w (d : ℂ)))
        = w := by
      rw [hnc2, c₂_capProjVecOf]
      rw [mul_comm (star w) ((Real.sqrt (1 - ‖(d : ℂ)‖ ^ 2 / 2) : ℝ) : ℂ)]
      rw [div_eq_iff (mul_ne_zero hsC (star_ne_zero_of_norm_eq_one hw1))]
      rw [← mul_assoc, mul_comm w ((Real.sqrt (1 - ‖(d : ℂ)‖ ^ 2 / 2) : ℝ) : ℂ),
        mul_assoc _ w (star w), mul_star_eq_one hw1, mul_one]
    rw [hratio, hw]
  -- the disk coordinate of the sphere point is `d`
  have hsecond : (Real.sqrt 2 : ℂ) * c₁ (capProjVecOf w (d : ℂ)) * c₂ (capProjVecOf w (d : ℂ))
      / (((‖c₂ (capProjVecOf w (d : ℂ))‖ : ℝ)) : ℂ) = (d : ℂ) := by
    rw [hnc2, c₁_capProjVecOf, c₂_capProjVecOf]
    have h2C : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hws : w * star w = 1 := mul_star_eq_one hw1
    rw [mul_div_assoc', mul_div_cancel_left₀ ((d : ℂ) * w) h2C]
    rw [← mul_assoc, mul_assoc (d : ℂ) w (star w), hws, mul_one]
    rw [mul_comm (d : ℂ) ((Real.sqrt (1 - ‖(d : ℂ)‖ ^ 2 / 2) : ℝ) : ℂ),
      mul_div_cancel_left₀ (d : ℂ) hsC]
  -- `capPt` of that sphere point is exactly `(θ, d)`
  have hcapt : capPt ⟨(⟨capProjVecOf w (d : ℂ), hVmem⟩ : unitSphere 3), hle⟩ = (θ, d) := by
    refine Prod.ext ?_ ?_
    · apply circleOf_injective
      rw [capPt_fst, circleOf_circOf]
      exact hfirst
    · refine Subtype.ext ?_
      rw [capPt_snd]
      exact hsecond
  -- hence `phi` of that sphere point is the class of `(θ, d)`
  have hphi : phi (⟨capProjVecOf w (d : ℂ), hVmem⟩ : unitSphere 3)
      = (Quotient.mk'' (Sum.inl (θ, d) : Work.Drive.CapTorus ⊕ Work.Drive.ConfTorus) :
          Work.Drive.LensSpace) := by
    unfold phi
    rw [dif_pos hle, hcapt]
  rw [← hphi, lensToProj_phi]
  exact projectivizationMk_congr ℝ (Eucl 3)

end Work.Drive
