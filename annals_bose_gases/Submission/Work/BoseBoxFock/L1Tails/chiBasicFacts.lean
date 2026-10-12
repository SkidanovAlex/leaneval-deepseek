import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseBoxFock.L1Tails.chiChiCoulAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.chiBasicFacts` — elementary facts about the corpus window

The vocabulary module for the `L¹`-tail chapter: the support of the corpus bump
`χ = chiBase / √(∫χBase²)` (`CubicChi.chi`), its scalings `chiScale ℓ x = χ (ℓ⁻¹ • x)`,
and the complexification `chiC ℓ x = ((chiScale ℓ x : ℝ) : ℂ)`.

The point of this file is the *flat* ball-support of the scaling:

* `chiScale ℓ x ≠ 0 ↔ ‖x‖ < ℓ/2` (the support is the open ball of radius `ℓ/2`);
* `chiScale ℓ x ≤ 1`-type bounds are **false** (the corpus bump is only `L²`-normalised,
  hence its sup is `(∫χBase²)^{-1/2} > 1`); what is true and used everywhere is
  nonnegativity (`chiScale_nonneg`) and the norm identity `‖chiC ℓ x‖ = chiScale ℓ x`;
* the closed half-ball `halfBall ℓ = closedBall 0 (ℓ/2)` of the `y`-variable in `psiM` is
  contained in the corpus box `corpusBox.boxL ℓ = {x | ∀ i, |x i| ≤ ℓ/2}` (`halfBall_subset_boxL`),
  which is where the `w`-Dirichlet energy `pairDir'` is integrated.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Real Topology ContDiff InnerProductSpace

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1. The support of the corpus bump -/

/-- The corpus bump `chiBase` is non-zero exactly inside the open ball of radius `1/2`
(the support field of `ContDiffBump`). -/
theorem chiBase_ne_zero_iff_norm_lt_half (x : E3) :
    Submission.BoseGases.chiBase x ≠ 0 ↔ ‖x‖ < 1 / 2 := by
  have hr : Submission.BoseGases.chiBump.rOut = 1 / 2 := rfl
  constructor
  · intro h
    by_contra hle
    exact h (ContDiffBump.zero_of_le_dist (f := Submission.BoseGases.chiBump)
      (by rw [hr, dist_zero_right]; exact not_lt.mp hle))
  · intro hlt
    exact ne_of_gt (ContDiffBump.pos_of_mem_ball (f := Submission.BoseGases.chiBump)
      (by rw [Metric.mem_ball, dist_zero_right, hr]; exact hlt))

/-- The (L²-normalised) corpus bump `chi` is non-zero exactly inside the open ball of radius
`1/2`. -/
theorem chi_ne_zero_iff (x : E3) : Submission.BoseGases.chi x ≠ 0 ↔ ‖x‖ < 1 / 2 := by
  rw [Submission.BoseGases.chi, div_ne_zero_iff]
  constructor
  · rintro ⟨h1, _⟩
    exact (chiBase_ne_zero_iff_norm_lt_half x).1 h1
  · intro hx
    exact ⟨(chiBase_ne_zero_iff_norm_lt_half x).2 hx, Submission.BoseGases.chi_sqrt_ne_zero⟩

/-- `chiScale ℓ ·` is non-zero exactly inside the open ball of radius `ℓ/2`. -/
theorem chiScale_ne_zero_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (x : E3) :
    Submission.BoseGases.chiScale ℓ x ≠ 0 ↔ ‖x‖ < ℓ / 2 := by
  have hiff : ℓ⁻¹ * ‖x‖ < 1 / 2 ↔ ‖x‖ < ℓ / 2 := by
    constructor
    · intro h
      have h2 : ℓ * (ℓ⁻¹ * ‖x‖) < ℓ * (1 / 2) := mul_lt_mul_of_pos_left h hℓ
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hℓ), one_mul] at h2
      linarith
    · intro h
      have h2 : ℓ⁻¹ * ‖x‖ < ℓ⁻¹ * (ℓ / 2) := mul_lt_mul_of_pos_left h (inv_pos.mpr hℓ)
      have h3 : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by
        rw [show ℓ⁻¹ * (ℓ / 2) = (ℓ * ℓ⁻¹) / 2 by ring, mul_inv_cancel₀ (ne_of_gt hℓ),
          one_div]
      linarith
  rw [Submission.BoseGases.chiScale, chi_ne_zero_iff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hℓ)]
  exact hiff

/-- `chiScale ℓ ·` vanishes outside the closed ball of radius `ℓ/2`. -/
theorem chiScale_eq_zero_of_half_le_norm {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3}
    (hx : ℓ / 2 ≤ ‖x‖) : Submission.BoseGases.chiScale ℓ x = 0 := by
  by_contra h
  exact absurd ((chiScale_ne_zero_iff hℓ x).1 h) (not_lt.mpr hx)

/-! ## 2. Positivity and the complexified window -/

theorem chiScale_nonneg (ℓ : ℝ) (x : E3) : 0 ≤ Submission.BoseGases.chiScale ℓ x :=
  Submission.BoseGases.chi_nonneg _

/-- The norm of the complexified window is the window. -/
theorem norm_chiC (ℓ : ℝ) (x : E3) : ‖chiC ℓ x‖ = Submission.BoseGases.chiScale ℓ x := by
  have h1 : Complex.normSq (chiC ℓ x) = (Submission.BoseGases.chiScale ℓ x) ^ 2 := by
    rw [chiC, Complex.normSq_ofReal]
    ring
  have h2 : ‖chiC ℓ x‖ ^ 2 = (Submission.BoseGases.chiScale ℓ x) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, h1]
  have h3 : ‖chiC ℓ x‖ = |Submission.BoseGases.chiScale ℓ x| := by
    calc ‖chiC ℓ x‖ = Real.sqrt (‖chiC ℓ x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt ((Submission.BoseGases.chiScale ℓ x) ^ 2) := by rw [h2]
      _ = |Submission.BoseGases.chiScale ℓ x| := Real.sqrt_sq_eq_abs _
  rwa [abs_of_nonneg (chiScale_nonneg ℓ x)] at h3

/-- The complexified window vanishes iff the real window does. -/
theorem chiC_ne_zero_iff (ℓ : ℝ) (x : E3) :
    chiC ℓ x ≠ 0 ↔ Submission.BoseGases.chiScale ℓ x ≠ 0 := by
  have h1 : chiC ℓ x = 0 ↔ Submission.BoseGases.chiScale ℓ x = 0 := by
    rw [chiC]
    exact Complex.ofReal_eq_zero
  exact not_congr h1

/-- `chiScale ℓ` is `C^∞`. -/
theorem contDiff_chiScale (ℓ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.chiScale ℓ) := by
  rw [show Submission.BoseGases.chiScale ℓ
      = fun x : E3 => Submission.BoseGases.chi ((ℓ⁻¹ : ℝ) • x) from rfl]
  exact Submission.BoseGases.chi_contDiff.comp (contDiff_const_smul (ℓ⁻¹ : ℝ))

/-- The complexified window `chiC ℓ` is `C^∞`. -/
theorem contDiff_chiC (ℓ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (chiC ℓ) := by
  rw [show chiC ℓ
      = fun x : E3 => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) from rfl]
  exact Complex.ofRealCLM.contDiff.comp (contDiff_chiScale ℓ)

/-! ## 3. The half ball inside the corpus box -/

/-- The closed ball of radius `ℓ/2` (about the origin) is contained in the corpus box
`corpusBox.boxL ℓ = ℓ • unitCell = {x | ∀ i, |x i| ≤ ℓ/2}`. -/
theorem mem_boxL_of_norm_le {ℓ : ℝ} (hℓ : 0 < ℓ) {y : E3} (hy : ‖y‖ ≤ ℓ / 2) :
    y ∈ Work.BoseK15.corpusBox.boxL ℓ := by
  rw [Work.BoseB4.BoxData.boxL, Work.BoseK15.corpusBox,
    Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)]
  simp only [Work.BoseB4.unitCell, Set.mem_ofPred_eq]
  intro i
  have h1 : ‖(ℓ⁻¹ : ℝ) • y‖ = ℓ⁻¹ * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
  have h2 : ‖((ℓ⁻¹ : ℝ) • y).ofLp i‖ ≤ ℓ⁻¹ * ‖y‖ := by
    rw [← h1]
    exact PiLp.norm_apply_le _ i
  have h3 : ℓ⁻¹ * ‖y‖ ≤ 1 / 2 := by
    have h4 : ℓ⁻¹ * ‖y‖ ≤ ℓ⁻¹ * (ℓ / 2) :=
      mul_le_mul_of_nonneg_left hy (le_of_lt (inv_pos.mpr hℓ))
    have h5 : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by
      rw [show ℓ⁻¹ * (ℓ / 2) = (ℓ * ℓ⁻¹) / 2 by ring, mul_inv_cancel₀ (ne_of_gt hℓ),
        one_div]
    linarith
  rw [Real.norm_eq_abs] at h2
  linarith

/-- The half ball of the `y`-variable of `psiM` sits inside the corpus box. -/
theorem halfBall_subset_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    halfBall ℓ ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro y hy
  rw [halfBall, Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
  exact mem_boxL_of_norm_le hℓ hy

/-- The corpus box is compact (`boxL ℓ = ℓ • unitCell` is the image of the compact unit cube). -/
theorem isCompact_boxL (ℓ : ℝ) : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) := by
  rw [Work.BoseB4.BoxData.boxL, Work.BoseK15.corpusBox]
  exact Work.BoseK15.corpusBox.cell_compact.image (continuous_const_smul ℓ)

/-! ## 4. Flatness of a function vanishing outside a ball, at the boundary -/

/-- **Flatness at the boundary of a ball.**  If `f` vanishes on the closed exterior of the ball of
radius `R` and is differentiable at a point `x₀` of the boundary (`‖x₀‖ = R`), then
`fderiv ℝ f x₀ = 0`.

This is the parametric statement behind the fact that the derivative of the corpus window
`chiScale ℓ = χ ((ℓ⁻¹) • ·)` vanishes on the whole sphere `‖x‖ = ℓ/2`, not only outside the ball:
in a direction pointing outwards the difference quotient vanishes identically for `t > 0`, so the
(two-sided) derivative vanishes, and the outward half-space spans the space. -/
theorem fderiv_eq_zero_of_norm_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {x₀ : E3} {f : E3 → F}
    (hR : ‖x₀‖ = R) (hd : DifferentiableAt ℝ f x₀)
    (hzero : ∀ x, R ≤ ‖x‖ → f x = 0) : fderiv ℝ f x₀ = 0 := by
  have hfx₀ : f x₀ = 0 := hzero x₀ (le_of_eq hR.symm)
  have key : ∀ v : E3, 0 ≤ ⟪x₀, v⟫_ℝ → fderiv ℝ f x₀ v = 0 := by
    intro v hv
    have hpath : ∀ t : ℝ, 0 < t → f (x₀ + t • v) = 0 := by
      intro t ht
      refine hzero _ ?_
      have hsq : R ^ 2 ≤ ‖x₀ + t • v‖ ^ 2 := by
        rw [norm_add_sq_real]
        have hR2 : R ^ 2 = ‖x₀‖ ^ 2 := by rw [hR]
        rw [hR2]
        have h2 : 0 ≤ 2 * ⟪x₀, t • v⟫_ℝ := by
          rw [real_inner_smul_right]
          exact mul_nonneg (by norm_num) (mul_nonneg ht.le hv)
        nlinarith [sq_nonneg ‖t • v‖]
      have hRnn : 0 ≤ R := by rw [← hR]; exact norm_nonneg _
      nlinarith [norm_nonneg (x₀ + t • v)]
    have hpath_deriv : HasDerivAt (fun t : ℝ => x₀ + t • v) v 0 := by
      have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
      simpa using h1.const_add x₀
    have hder : HasDerivAt (fun t : ℝ => f (x₀ + t • v)) (fderiv ℝ f x₀ v) 0 :=
      HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => x₀ + t • v) (x := (0 : ℝ))
        (by simpa using hd.hasFDerivAt) hpath_deriv
    have hlim : Tendsto (slope (fun t : ℝ => f (x₀ + t • v)) 0) (𝓝[>] (0 : ℝ))
        (𝓝 (fderiv ℝ f x₀ v)) :=
      (hasDerivAt_iff_tendsto_slope_left_right.mp hder).2
    have hslope : slope (fun t : ℝ => f (x₀ + t • v)) 0 =ᶠ[𝓝[>] (0 : ℝ)] 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have h0 : f (x₀ + (0 : ℝ) • v) = 0 := by simpa using hfx₀
      rw [slope_def_module, hpath t ht, h0]
      simp
    have hlim0 : Tendsto (slope (fun t : ℝ => f (x₀ + t • v)) 0) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      (tendsto_congr' hslope).2 tendsto_const_nhds
    exact tendsto_nhds_unique hlim hlim0
  refine ContinuousLinearMap.ext fun v => ?_
  change fderiv ℝ f x₀ v = (0 : F)
  by_cases hv : 0 ≤ ⟪x₀, v⟫_ℝ
  · exact key v hv
  · have hv' : 0 ≤ ⟪x₀, -v⟫_ℝ := by
      rw [inner_neg_right]
      exact neg_nonneg.mpr (le_of_lt (not_le.mp hv))
    have h := key (-v) hv'
    rw [map_neg] at h
    exact neg_eq_zero.mp h

end Work.BoseBoxFock.L1Tails
