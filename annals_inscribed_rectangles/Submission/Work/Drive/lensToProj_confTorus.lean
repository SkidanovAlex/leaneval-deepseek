import Mathlib
import Submission.Work.Drive.cappingProjCoords
import Submission.Work.Drive.phi_surjective

namespace Work.Drive

noncomputable section

/-! ## The coordinate norms of the configuration sphere lift

`confProjVecOf u d = (u · √(1 - ‖d‖²/2), ū · d/√2)` has coordinate norms
`‖c₁‖ = √(1 - ‖d‖²/2)` and `‖c₂‖ = ‖d‖/√2`, so that `‖c₂‖ ≤ ‖c₁‖` as soon as `‖d‖ ≤ 1`; this is what
selects the configuration branch of the glueing map `phi`. -/

/-- The norm of the first coordinate of `confProjVecOf`: `‖u · √(1 - ‖d‖²/2)‖ = √(1 - ‖d‖²/2)` for
`‖u‖ = 1`. -/
lemma norm_c₁_confProjVecOf {u : ℂ} (hu : ‖u‖ = 1) (d : ℂ) :
    ‖c₁ (confProjVecOf u d)‖ = Real.sqrt (1 - ‖d‖ ^ 2 / 2) := by
  rw [c₁_confProjVecOf, norm_mul, hu, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The norm of the second coordinate of `confProjVecOf`: `‖ū · d/√2‖ = ‖d‖/√2`. -/
lemma norm_c₂_confProjVecOf {u : ℂ} (hu : ‖u‖ = 1) (d : ℂ) :
    ‖c₂ (confProjVecOf u d)‖ = ‖d‖ / Real.sqrt 2 := by
  rw [c₂_confProjVecOf, norm_div, norm_mul, norm_star, hu, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- A complex number of norm `1` satisfies `ū u = 1`. -/
lemma star_mul_self_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) : star u * u = 1 := by
  have h : star u * u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
    simpa [Complex.star_def] using Complex.conj_mul' u
  rw [h, hu]
  norm_num

/-- The algebraic identity computing the disk coordinate of `confPt` on the configuration sphere
lift: `√2 · (ū d/√2) · (u r) / r = d` for `ū u = 1` and `r ≠ 0`. -/
lemma sqrt_two_mul_star_mul_div (u d r : ℂ) (hu : star u * u = 1) (hr : r ≠ 0)
    (hs : (Real.sqrt 2 : ℂ) ≠ 0) :
    (Real.sqrt 2 : ℂ) * (star u * d / (Real.sqrt 2 : ℂ)) * (u * r) / r = d := by
  have step1 : (Real.sqrt 2 : ℂ) * (star u * d / (Real.sqrt 2 : ℂ)) = star u * d := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hs]
  rw [step1]
  have step2 : (star u * d) * (u * r) / r = star u * d * u := by
    rw [show (star u * d) * (u * r) = (star u * d * u) * r by ring, mul_div_cancel_right₀ _ hr]
  rw [step2]
  rw [show star u * d * u = (star u * u) * d by ring, hu, one_mul]

end

open Manifold in
open scoped Manifold ContDiff in
/-- **The sphere lift of a point of the configuration solid torus.**  The identification
`Work.Drive.lensToProj : Work.Drive.LensSpace → ℝP³` is the descent of `projOfUnitSphere` through the
quotient map `phi : S³ → LensSpace`; its definition goes through `Function.surjInv`, so nothing about
it can be unfolded, and this statement gives the explicit formula on the configuration solid torus
`ConfTorus = D² × S¹`.

Because the configuration coordinate of `LensSpace` is `(z₁/‖z₁‖)²` — a *square* of a unit complex
number — the formula necessarily involves a chosen square root `u` of `circleOf η` (the two choices
`±u` differ by the antipodal identification of the sphere, so the projective class does not depend on
the choice).  With such a `u` the sphere point of the class of `(d, η)` is
`(u · √(1 - ‖d‖²/2), ū · d / √2) ∈ ℂ² = ℝ⁴ = Eucl 3`, i.e. `Work.Drive.confProjVecOf u d`, a unit
vector (`Work.Drive.norm_confProjVecOf`) which never vanishes
(`Work.Drive.confProjVecOf_ne_zero`).

Route: identical to the cap case with `c₁` and `c₂` exchanged and `confPt` in place of `capPt`
(`phi`'s configuration branch, `‖c₂ V‖ ≤ ‖c₁ V‖`), the identities being
`(‖c₁ V‖/c₁ V)² = (1/ū)² = u² = circleOf η` and `√2 c₂ V c₁ V/‖c₁ V‖ = d ū u = d`. -/
theorem lensToProj_confTorus (d : Metric.closedBall (0 : ℂ) 1) (η : UnitAddCircle) {u : ℂ}
    (hu : u ^ 2 = circleOf η) :
    Work.Drive.lensToProj
        (Quotient.mk'' (Sum.inr (d, η) : Work.Drive.CapTorus ⊕ Work.Drive.ConfTorus) :
          Work.Drive.LensSpace)
      = Projectivization.mk ℝ (Work.Drive.confProjVecOf u (d : ℂ))
          (Work.Drive.confProjVecOf_ne_zero (Work.Drive.norm_eq_one_of_sq_eq_circleOf hu)
            (Work.Drive.norm_coe_closedBall_le_one d)) := by
  have hu1 : ‖u‖ = 1 := norm_eq_one_of_sq_eq_circleOf hu
  have hd1 : ‖(d : ℂ)‖ ≤ 1 := norm_coe_closedBall_le_one d
  have hVnorm : ‖confProjVecOf u (d : ℂ)‖ = 1 := norm_confProjVecOf hu1 hd1
  -- the configuration branch of `phi` is the one selected by `confProjVecOf`
  have hge : ‖c₂ (confProjVecOf u (d : ℂ))‖ ≤ ‖c₁ (confProjVecOf u (d : ℂ))‖ := by
    rw [norm_c₂_confProjVecOf hu1, norm_c₁_confProjVecOf hu1]
    exact div_sqrt_two_le_sqrt_one_sub hd1 (norm_nonneg _)
  have hv : confProjVecOf u (d : ℂ) ∈ unitSphere 3 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    exact hVnorm
  have hrne : ((Real.sqrt (1 - ‖(d : ℂ)‖ ^ 2 / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (sqrt_one_sub_pos hd1))
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hstar : star u * u = 1 := star_mul_self_of_norm_eq_one hu1
  have hge' : ‖c₂ (↑(⟨confProjVecOf u (d : ℂ), hv⟩ : unitSphere 3))‖
      ≤ ‖c₁ (↑(⟨confProjVecOf u (d : ℂ), hv⟩ : unitSphere 3))‖ := hge
  -- the sphere lift re-reads the configuration coordinates as `(d, η)`
  have hconf : confPt ⟨(⟨confProjVecOf u (d : ℂ), hv⟩ : unitSphere 3), hge'⟩ = (d, η) := by
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      show ((confPt ⟨(⟨confProjVecOf u (d:ℂ), hv⟩ : unitSphere 3), hge'⟩).1 : ℂ) = (d : ℂ)
      rw [confPt_fst]
      show (Real.sqrt 2 : ℂ) * c₂ (confProjVecOf u (d:ℂ)) * c₁ (confProjVecOf u (d:ℂ))
        / ((‖c₁ (confProjVecOf u (d:ℂ))‖ : ℝ) : ℂ) = (d : ℂ)
      rw [norm_c₁_confProjVecOf hu1, c₁_confProjVecOf, c₂_confProjVecOf]
      exact sqrt_two_mul_star_mul_div u (d : ℂ) _ hstar hrne hs2
    · show (confPt ⟨(⟨confProjVecOf u (d:ℂ), hv⟩ : unitSphere 3), hge'⟩).2 = η
      rw [confPt_snd]
      apply circleOf_injective
      rw [circleOf_circOf]
      show (c₁ (confProjVecOf u (d:ℂ)) / ((‖c₁ (confProjVecOf u (d:ℂ))‖ : ℝ) : ℂ)) ^ 2
        = circleOf η
      rw [norm_c₁_confProjVecOf hu1, c₁_confProjVecOf]
      show (u * ((Real.sqrt (1 - ‖(d:ℂ)‖^2/2) : ℝ) : ℂ)
        / ((Real.sqrt (1 - ‖(d:ℂ)‖^2/2) : ℝ) : ℂ)) ^ 2 = circleOf η
      rw [mul_div_cancel_right₀ u hrne]
      exact hu
  have hphi : phi (⟨confProjVecOf u (d : ℂ), hv⟩ : unitSphere 3)
      = Quotient.mk'' (Sum.inr ((d, η) : ConfTorus) : CapTorus ⊕ ConfTorus) := by
    rw [phi_of_conf _ hge']
    exact Quotient.sound (Or.inl (congrArg Sum.inr hconf))
  rw [← hphi, lensToProj_phi]
  exact projectivizationMk_congr ℝ (Eucl 3)

end Work.Drive
