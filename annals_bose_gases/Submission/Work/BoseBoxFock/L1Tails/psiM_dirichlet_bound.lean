import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.continuous_fderiv_chiC_mul
import Submission.Work.BoseBoxFock.L1Tails.fderiv_chiC_mul_eq_zero_of_half_le_norm
import Submission.Work.BoseBoxFock.L1Tails.setIntegral_le_of_eq_zero_of_notMem
import Submission.Work.BoseBoxFock.L1Tails.sq_setIntegral_le_volumeReal_mul
import Submission.Work.BoseBoxFock.L1Tails.volumeReal_halfBall_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.psiM_dirichlet_bound` — the `w`-Dirichlet bound for `psiM`

The `H¹`-half of the `χχ`-images pairing `T7` of `sources/boseDCF/bose_L1tails.md`: on the ball
`‖z‖ ≤ 2R` the derivative of

  `psiM ℓ m G z = ∫_{‖y‖ ≤ ℓ/2} χ_ℓ(y)·χ_ℓ(z + y − ℓ•latVec m)·G (z + y − ℓ•latVec m) y dy`

is controlled by the *gap hypothesis* (`χ_ℓ(z + y − ℓ•latVec m) ≠ 0 ⟹ χ_ℓ(y) ≤ ε`), which makes
the window factor in the `y`-variable pay an `ε`:

  `∑_j ∫_{‖z‖ ≤ 2R} ‖∂_j psiM z‖² ≤ ε²·ℓ³·∫_y∫_w ∑_j ‖∂_j(χ_ℓ G) (w,y)‖²`.

**Proof.**  `∂_j psiM z = ∫_y χ_ℓ(y)·∂_j(χ_ℓ G)(z + y − ℓm, y) dy` (`hfderiv`), and the corpus
window `χ_ℓ` has the ball `‖w‖ ≤ ℓ/2` as its support, its *derivative* vanishing on the whole
closed ball `‖w‖ ≤ ℓ/2` (`fderiv_eq_zero_of_norm_eq` applied to the flat bump, for the sphere, and
local vanishing outside).  Hence the `y`-integrand differs from `∂_j(χ_ℓ G)(z + y − ℓm, y)` only
where `χ_ℓ(z + y − ℓm) ≠ 0`, and there the gap hypothesis gives

  `χ_ℓ(y)·‖∂_j(χ_ℓ G)(z + y − ℓm, y)‖ ≤ ε·‖∂_j(χ_ℓ G)(z + y − ℓm, y)‖`.

Cauchy–Schwarz in `y` (with total mass `vol (halfBall ℓ) ≤ ℓ³`) and then Tonelli, the shear
`(z, y) ↦ (z + y − ℓm, y)` and the `w`-support of `∂_j(χ_ℓ G)` (inside the corpus box
`boxL ℓ = {w | ∀ i, |w i| ≤ ℓ/2}`) move the double integral to `∫_{boxL}∫_{boxL}`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real Topology ContDiff InnerProductSpace

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 1. The pointwise gap bound -/

/-- **The pointwise gap bound.**  Where the derivative `∂_j(χ_ℓ G)(·, y)` is non-zero, the second
window `χ_ℓ (z + y − ℓm)` is non-zero (the closed window's support is the ball of radius `ℓ/2`),
so the gap hypothesis bounds the *first* window `χ_ℓ y` by `ε`. -/
theorem chiScale_mul_pairVj_le {ℓ R ε : ℝ} (hℓ : 0 < ℓ)
    {m : Fin 3 → ℤ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G))
    (hgap : ∀ {z y : E3}, ‖z‖ ≤ 2 * R →
      Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m) ≠ 0 →
      Submission.BoseGases.chiScale ℓ y ≤ ε)
    {z y : E3} (hz : ‖z‖ ≤ 2 * R) (j : Fin 3) :
    Submission.BoseGases.chiScale ℓ y * ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖
      ≤ ε * ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ := by
  by_cases hc : Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m) ≠ 0
  · exact mul_le_mul_of_nonneg_right (hgap hz hc) (norm_nonneg _)
  · have hw : ℓ / 2 ≤ ‖z + y - ℓ • Work.BoseBoxFock.latVec m‖ := by
      by_contra hlt
      exact ((chiScale_ne_zero_iff hℓ _).2 (not_le.mp hlt)) (not_not.mp hc)
    have hz0 : fderiv ℝ (fun w' => chiC ℓ w' * G w' y)
        (z + y - ℓ • Work.BoseBoxFock.latVec m) = 0 :=
      fderiv_chiC_mul_eq_zero_of_half_le_norm hℓ hG hw
    have hv0 : pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y = 0 := by
      rw [pairVj, hz0]
      simp
    rw [hv0]
    simp

/-! ## 2. Joint continuity of the pair derivative and of the parametric integrals -/

theorem continuous_pairVj {ℓ : ℝ} {m : Fin 3 → ℤ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (j : Fin 3) :
    Continuous (fun p : E3 × E3 => pairVj ℓ G j p.1 p.2) := by
  simpa only [pairVj] using continuous_fderiv_chiC_mul (ℓ := ℓ) (G := G) hG j

/-- Continuity of `z ↦ ∫_{halfBall ℓ} χ_ℓ(y)·∂_j(χ_ℓ G)(z + y − ℓm, y) dy`. -/
theorem continuous_setIntegral_chiC_pairVj {ℓ : ℝ} {m : Fin 3 → ℤ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (j : Fin 3) :
    Continuous (fun z : E3 => ∫ y in halfBall ℓ,
      chiC ℓ y * pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y) := by
  have hcontj := continuous_pairVj (ℓ := ℓ) (m := m) (G := G) hG j
  have hmap : Continuous (fun p : E3 × E3 =>
      (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m, p.2)) := by
    refine Continuous.prodMk ?_ continuous_snd
    exact (continuous_fst.add continuous_snd).sub continuous_const
  have hcont : Continuous (fun p : E3 × E3 =>
      chiC ℓ p.2 * pairVj ℓ G j (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m) p.2) :=
    ((contDiff_chiC ℓ).continuous.comp continuous_snd).mul (hcontj.comp hmap)
  refine continuous_parametric_integral_of_continuous
    (f := fun z y : E3 => chiC ℓ y * pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y)
    (s := halfBall ℓ) ?_ (isCompact_closedBall (0 : E3) (ℓ / 2))
  show Continuous (Function.uncurry
    (fun z y : E3 => chiC ℓ y * pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y))
  exact hcont

/-- Continuity of `z ↦ ∫_{halfBall ℓ} ‖∂_j(χ_ℓ G)(z + y − ℓm, y)‖² dy`. -/
theorem continuous_setIntegral_pairVj_sq_shift {ℓ : ℝ} {m : Fin 3 → ℤ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (j : Fin 3) :
    Continuous (fun z : E3 => ∫ y in halfBall ℓ,
      ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2) := by
  have hcontj := continuous_pairVj (ℓ := ℓ) (m := m) (G := G) hG j
  have hmap : Continuous (fun p : E3 × E3 =>
      (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m, p.2)) := by
    refine Continuous.prodMk ?_ continuous_snd
    exact (continuous_fst.add continuous_snd).sub continuous_const
  refine continuous_parametric_integral_of_continuous
    (f := fun z y : E3 => ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2)
    (s := halfBall ℓ) ?_ (isCompact_closedBall (0 : E3) (ℓ / 2))
  show Continuous (Function.uncurry
    (fun z y : E3 => ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2))
  exact ((hcontj.comp hmap).norm.pow 2)

/-- Continuity of `y ↦ ∫_{boxL ℓ} ‖∂_j(χ_ℓ G)(w, y)‖² dw`. -/
theorem continuous_setIntegral_pairVj_sq_box {ℓ : ℝ} {m : Fin 3 → ℤ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (j : Fin 3) :
    Continuous (fun y : E3 => ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
      ‖pairVj ℓ G j w y‖ ^ 2) := by
  have hcontj := continuous_pairVj (ℓ := ℓ) (m := m) (G := G) hG j
  refine continuous_parametric_integral_of_continuous
    (f := fun y w : E3 => ‖pairVj ℓ G j w y‖ ^ 2)
    (s := Work.BoseK15.corpusBox.boxL ℓ) ?_ (isCompact_boxL ℓ)
  show Continuous (Function.uncurry (fun y w : E3 => ‖pairVj ℓ G j w y‖ ^ 2))
  exact ((hcontj.comp continuous_swap).norm.pow 2)

/-- Continuity of `y ↦ ∫_{‖z‖ ≤ 2R} ‖∂_j(χ_ℓ G)(z + y − ℓm, y)‖² dz`. -/
theorem continuous_setIntegral_pairVj_sq_ball {ℓ R : ℝ} {m : Fin 3 → ℤ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (j : Fin 3) :
    Continuous (fun y : E3 => ∫ z in Metric.closedBall (0 : E3) (2 * R),
      ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2) := by
  have hcontj := continuous_pairVj (ℓ := ℓ) (m := m) (G := G) hG j
  have hmap : Continuous (fun p : E3 × E3 =>
      (p.2 + p.1 - ℓ • Work.BoseBoxFock.latVec m, p.1)) := by
    refine Continuous.prodMk ?_ continuous_fst
    exact (continuous_snd.add continuous_fst).sub continuous_const
  refine continuous_parametric_integral_of_continuous
    (f := fun y z : E3 => ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2)
    (s := Metric.closedBall (0 : E3) (2 * R)) ?_ (isCompact_closedBall (0 : E3) (2 * R))
  show Continuous (Function.uncurry
    (fun y z : E3 => ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2))
  exact ((hcontj.comp hmap).norm.pow 2)

/-! ## 3. The shear/support comparison for a single `y` -/

/-- **The shear step.**  For a fixed `y`, the `z`-integral over the ball `‖z‖ ≤ 2R` of the pair
derivative at the shifted point `z + y − ℓm` is bounded by the `w`-integral over the corpus box,
because `∂_j(χ_ℓ G)(·, y)` is supported in the ball `‖w‖ ≤ ℓ/2`, and the translation
`z ↦ z + y − ℓm` is measure preserving. -/
theorem setIntegral_shift_le {ℓ R : ℝ} (hℓ : 0 < ℓ) {m : Fin 3 → ℤ} {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) (j : Fin 3) (y : E3) :
    ∫ z in Metric.closedBall (0 : E3) (2 * R),
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2
      ≤ ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖pairVj ℓ G j w y‖ ^ 2 := by
  have hcontj := continuous_pairVj (ℓ := ℓ) (m := m) (G := G) hG j
  have hfun : (fun z : E3 => z + y - ℓ • Work.BoseBoxFock.latVec m)
      = (fun z : E3 => z + (y - ℓ • Work.BoseBoxFock.latVec m)) := by
    funext z
    abel
  have hmp : MeasurePreserving (fun z : E3 => z + y - ℓ • Work.BoseBoxFock.latVec m)
      volume volume := by
    rw [hfun]
    exact measurePreserving_add_right volume _
  have hmb : MeasurableEmbedding (fun z : E3 => z + y - ℓ • Work.BoseBoxFock.latVec m) := by
    rw [hfun]
    exact (Homeomorph.addRight _).isClosedEmbedding.measurableEmbedding
  have heq : ∫ w in (fun z : E3 => z + y - ℓ • Work.BoseBoxFock.latVec m) ''
        (Metric.closedBall (0 : E3) (2 * R)), ‖pairVj ℓ G j w y‖ ^ 2
      = ∫ z in Metric.closedBall (0 : E3) (2 * R),
          ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 :=
    MeasurePreserving.setIntegral_image_emb hmp hmb (fun w => ‖pairVj ℓ G j w y‖ ^ 2) _
  rw [← heq]
  refine setIntegral_le_of_eq_zero_of_notMem (fun w => sq_nonneg _) ?_ ?_
  · intro w hw
    have hnorm : ℓ / 2 ≤ ‖w‖ := by
      by_contra hlt
      exact hw (mem_boxL_of_norm_le hℓ (not_le.mp hlt).le)
    have hzero : pairVj ℓ G j w y = 0 := by
      have hzw : fderiv ℝ (fun w' => chiC ℓ w' * G w' y) w = 0 :=
        fderiv_chiC_mul_eq_zero_of_half_le_norm hℓ hG hnorm
      rw [pairVj, hzw]
      simp
    rw [hzero]
    simp
  · refine ContinuousOn.integrableOn_compact (isCompact_boxL ℓ) ?_
    have hcw : Continuous (fun w : E3 => ‖pairVj ℓ G j w y‖ ^ 2) :=
      (hcontj.comp (continuous_id.prodMk continuous_const)).norm.pow 2
    exact hcw.continuousOn

/-! ## 4. The per-`j` estimate -/

theorem psiM_dirichlet_per_j {ℓ R ε : ℝ} (hℓ : 0 < ℓ) (hεnn : 0 ≤ ε)
    {m : Fin 3 → ℤ} {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G))
    (hfderiv : ∀ z w : EuclideanSpace ℝ (Fin 3),
        fderiv ℝ (Work.BoseBoxFock.L1Tails.psiM ℓ m G) z w
      = ∫ y in Work.BoseBoxFock.L1Tails.halfBall ℓ,
          Work.BoseBoxFock.L1Tails.chiC ℓ y *
            fderiv ℝ (fun w' => Work.BoseBoxFock.L1Tails.chiC ℓ w' * G w' y)
              (z + y - ℓ • Work.BoseBoxFock.latVec m) w)
    (hgap : ∀ {z y : EuclideanSpace ℝ (Fin 3)}, ‖z‖ ≤ 2 * R →
      Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m) ≠ 0 →
      Submission.BoseGases.chiScale ℓ y ≤ ε)
    (j : Fin 3) :
    ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * R),
        ‖fderiv ℝ (Work.BoseBoxFock.L1Tails.psiM ℓ m G) z
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ ε ^ 2 * ℓ ^ 3 * ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖pairVj ℓ G j w y‖ ^ 2 := by
  have hcontj := continuous_pairVj (ℓ := ℓ) (m := m) (G := G) hG j
  -- the derivative identity in `pairVj` form
  have hder : ∀ z : E3, fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))
      = ∫ y in halfBall ℓ,
          chiC ℓ y * pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y := by
    intro z
    rw [hfderiv z (EuclideanSpace.single j (1 : ℝ))]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with y
    simp only [pairVj]
  -- (A) the pointwise bound
  have hpoint : ∀ z : E3, ‖z‖ ≤ 2 * R →
      ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖
        ≤ ε * ∫ y in halfBall ℓ,
            ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ := by
    intro z hz
    have hmapz : Continuous (fun y : E3 =>
        (z + y - ℓ • Work.BoseBoxFock.latVec m, y)) := by
      refine Continuous.prodMk ?_ continuous_id
      exact (continuous_const.add continuous_id).sub continuous_const
    have hyc : Continuous (fun y : E3 =>
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) :=
      (hcontj.comp hmapz).norm
    have hint1 : IntegrableOn (fun y : E3 => Submission.BoseGases.chiScale ℓ y *
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) (halfBall ℓ) volume :=
      ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E3) (ℓ / 2))
        (((contDiff_chiScale ℓ).continuous.mul hyc).continuousOn)
    have hint2 : IntegrableOn (fun y : E3 => ε *
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) (halfBall ℓ) volume :=
      ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E3) (ℓ / 2))
        ((continuous_const.mul hyc).continuousOn)
    rw [hder z]
    calc ‖∫ y in halfBall ℓ,
            chiC ℓ y * pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖
        ≤ ∫ y in halfBall ℓ,
            ‖chiC ℓ y * pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ y in halfBall ℓ, Submission.BoseGases.chiScale ℓ y *
            ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ := by
          refine setIntegral_congr_fun measurableSet_closedBall fun y _ => ?_
          rw [norm_mul, norm_chiC]
      _ ≤ ∫ y in halfBall ℓ, ε *
            ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ :=
          setIntegral_mono_on hint1 hint2 measurableSet_closedBall
            fun y _ => chiScale_mul_pairVj_le hℓ hG hgap hz j
      _ = ε * ∫ y in halfBall ℓ,
            ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ := by
          rw [MeasureTheory.integral_const_mul]
  -- (B) Cauchy-Schwarz in `y`
  have hCS : ∀ z : E3,
      (∫ y in halfBall ℓ,
          ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) ^ 2
        ≤ (volume : Measure E3).real (halfBall ℓ) *
            ∫ y in halfBall ℓ,
              ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := by
    intro z
    have hmapz : Continuous (fun y : E3 =>
        (z + y - ℓ • Work.BoseBoxFock.latVec m, y)) := by
      refine Continuous.prodMk ?_ continuous_id
      exact (continuous_const.add continuous_id).sub continuous_const
    have hyc : Continuous (fun y : E3 =>
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) :=
      (hcontj.comp hmapz).norm
    have hint : IntegrableOn (fun y : E3 =>
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) (halfBall ℓ) volume :=
      ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E3) (ℓ / 2)) hyc.continuousOn
    have hint2 : IntegrableOn (fun y : E3 =>
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2) (halfBall ℓ) volume :=
      ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E3) (ℓ / 2))
        ((hyc.pow 2).continuousOn)
    have hne : (volume : Measure E3) (halfBall ℓ) ≠ ⊤ :=
      (isCompact_closedBall (0 : E3) (ℓ / 2)).measure_lt_top.ne
    exact sq_setIntegral_le_volumeReal_mul hne hint hint2
      (Filter.Eventually.of_forall fun y => norm_nonneg _)
  -- (C) the pointwise squared bound
  have hstep : ∀ z : E3, ‖z‖ ≤ 2 * R →
      ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ ε ^ 2 * (volume : Measure E3).real (halfBall ℓ) *
            ∫ y in halfBall ℓ,
              ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := by
    intro z hz
    calc ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ (ε * ∫ y in halfBall ℓ,
              ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hpoint z hz) 2
      _ = ε ^ 2 * (∫ y in halfBall ℓ,
              ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) ^ 2 := by ring
      _ ≤ ε ^ 2 * ((volume : Measure E3).real (halfBall ℓ) *
            ∫ y in halfBall ℓ,
              ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hCS z) (by positivity)
      _ = ε ^ 2 * (volume : Measure E3).real (halfBall ℓ) *
            ∫ y in halfBall ℓ,
              ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := by ring
  -- (D) integrate over the ball
  have hLint : IntegrableOn (fun z : E3 =>
      ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      (Metric.closedBall (0 : E3) (2 * R)) volume := by
    have h1 : Continuous (fun z : E3 =>
        fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))) := by
      rw [funext hder]
      exact continuous_setIntegral_chiC_pairVj (ℓ := ℓ) (m := m) (G := G) hG j
    exact ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E3) (2 * R))
      ((h1.norm.pow 2).continuousOn)
  have hRint : IntegrableOn (fun z : E3 => ε ^ 2 * (volume : Measure E3).real (halfBall ℓ) *
      ∫ y in halfBall ℓ,
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2)
      (Metric.closedBall (0 : E3) (2 * R)) volume := by
    have h1 : Continuous (fun z : E3 => ∫ y in halfBall ℓ,
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2) :=
      continuous_setIntegral_pairVj_sq_shift (ℓ := ℓ) (m := m) (G := G) hG j
    exact ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E3) (2 * R))
      ((continuous_const.mul h1).continuousOn)
  have hzint : ∫ z in Metric.closedBall (0 : E3) (2 * R),
        ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ ∫ z in Metric.closedBall (0 : E3) (2 * R),
          ε ^ 2 * (volume : Measure E3).real (halfBall ℓ) *
            ∫ y in halfBall ℓ,
              ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := by
    refine setIntegral_mono_on hLint hRint measurableSet_closedBall fun z hzB => ?_
    have hz : ‖z‖ ≤ 2 * R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hzB
      exact hzB
    exact hstep z hz
  -- (E) the Fubini/shear chain
  have hinter : Integrable (fun p : E3 × E3 =>
      ‖pairVj ℓ G j (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m) p.2‖ ^ 2)
      ((volume.restrict (Metric.closedBall (0 : E3) (2 * R))).prod
        (volume.restrict (halfBall ℓ))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    refine ContinuousOn.integrableOn_compact ?_ ?_
    · exact (isCompact_closedBall (0 : E3) (2 * R)).prod (isCompact_closedBall (0 : E3) (ℓ / 2))
    · have hmap : Continuous (fun p : E3 × E3 =>
          (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m, p.2)) := by
        refine Continuous.prodMk ?_ continuous_snd
        exact (continuous_fst.add continuous_snd).sub continuous_const
      exact ((hcontj.comp hmap).norm.pow 2).continuousOn
  have hswap : ∫ z in Metric.closedBall (0 : E3) (2 * R), ∫ y in halfBall ℓ,
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2
      = ∫ y in halfBall ℓ, ∫ z in Metric.closedBall (0 : E3) (2 * R),
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 :=
    integral_integral_swap hinter
  have hinner : ∫ z in Metric.closedBall (0 : E3) (2 * R), ∫ y in halfBall ℓ,
        ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2
      ≤ ∫ y in halfBall ℓ, ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖pairVj ℓ G j w y‖ ^ 2 := by
    rw [hswap]
    refine setIntegral_mono_on ?_ ?_ measurableSet_closedBall
      fun y _ => setIntegral_shift_le hℓ hG j y
    · exact ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E3) (ℓ / 2))
        ((continuous_setIntegral_pairVj_sq_ball (R := R) (ℓ := ℓ) (m := m) (G := G) hG j).continuousOn)
    · exact ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E3) (ℓ / 2))
        ((continuous_setIntegral_pairVj_sq_box (ℓ := ℓ) (m := m) (G := G) hG j).continuousOn)
  have hshift : ∫ y in halfBall ℓ, ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖pairVj ℓ G j w y‖ ^ 2
      ≤ ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖pairVj ℓ G j w y‖ ^ 2 := by
    refine setIntegral_mono_set ?_ ?_ ?_
    · exact ContinuousOn.integrableOn_compact (isCompact_boxL ℓ)
        ((continuous_setIntegral_pairVj_sq_box (ℓ := ℓ) (m := m) (G := G) hG j).continuousOn)
    · filter_upwards with y
      exact integral_nonneg fun w => sq_nonneg _
    · filter_upwards with y hy
      exact halfBall_subset_boxL hℓ hy
  have hvol : (volume : Measure E3).real (halfBall ℓ) ≤ ℓ ^ 3 := volumeReal_halfBall_le hℓ
  -- assembly
  calc ∫ z in Metric.closedBall (0 : E3) (2 * R),
        ‖fderiv ℝ (psiM ℓ m G) z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ ∫ z in Metric.closedBall (0 : E3) (2 * R),
          ε ^ 2 * (volume : Measure E3).real (halfBall ℓ) *
            ∫ y in halfBall ℓ,
              ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := hzint
    _ = ε ^ 2 * (volume : Measure E3).real (halfBall ℓ) *
          ∫ z in Metric.closedBall (0 : E3) (2 * R), ∫ y in halfBall ℓ,
            ‖pairVj ℓ G j (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ε ^ 2 * (volume : Measure E3).real (halfBall ℓ) *
          ∫ y in halfBall ℓ, ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
            ‖pairVj ℓ G j w y‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ ε ^ 2 * (volume : Measure E3).real (halfBall ℓ) *
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
            ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖pairVj ℓ G j w y‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hshift (by positivity)
    _ ≤ ε ^ 2 * ℓ ^ 3 * ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖pairVj ℓ G j w y‖ ^ 2 := by
        have hA0 : 0 ≤ ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
            ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖pairVj ℓ G j w y‖ ^ 2 :=
          integral_nonneg fun y => integral_nonneg fun w => sq_nonneg _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvol (by positivity)) hA0

/-! ## 5. The target -/

theorem psiM_dirichlet_bound {ℓ R ε : ℝ} (hℓ : 0 < ℓ) (hεnn : 0 ≤ ε)
    {m : Fin 3 → ℤ} {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G))
    (hfderiv : ∀ z w : EuclideanSpace ℝ (Fin 3), fderiv ℝ (Work.BoseBoxFock.L1Tails.psiM ℓ m G) z w
      = ∫ y in Work.BoseBoxFock.L1Tails.halfBall ℓ,
          Work.BoseBoxFock.L1Tails.chiC ℓ y *
            fderiv ℝ (fun w' => Work.BoseBoxFock.L1Tails.chiC ℓ w' * G w' y)
              (z + y - ℓ • Work.BoseBoxFock.latVec m) w)
    (hgap : ∀ {z y : EuclideanSpace ℝ (Fin 3)}, ‖z‖ ≤ 2 * R →
      Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m) ≠ 0 →
      Submission.BoseGases.chiScale ℓ y ≤ ε) :
    ∑ j : Fin 3, ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * R),
        ‖fderiv ℝ (Work.BoseBoxFock.L1Tails.psiM ℓ m G) z
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ ε ^ 2 * ℓ ^ 3 * Work.BoseBoxFock.L1Tails.pairDir' ℓ G := by
  have hsum : (∑ j : Fin 3, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖pairVj ℓ G j w y‖ ^ 2)
      = pairDir' ℓ G := by
    rw [pairDir']
    rw [← MeasureTheory.integral_finsetSum]
    · refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with y
      rw [MeasureTheory.integral_finsetSum]
      intro j _
      refine ContinuousOn.integrableOn_compact (isCompact_boxL ℓ) ?_
      have hc : Continuous (fun w : E3 => ‖pairVj ℓ G j w y‖ ^ 2) :=
        ((continuous_pairVj (ℓ := ℓ) (m := m) (G := G) hG j).comp
          (continuous_id.prodMk continuous_const)).norm.pow 2
      exact hc.continuousOn
    · intro j _
      exact ContinuousOn.integrableOn_compact (isCompact_boxL ℓ)
        ((continuous_setIntegral_pairVj_sq_box (ℓ := ℓ) (m := m) (G := G) hG j).continuousOn)
  calc ∑ j : Fin 3, ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * R),
        ‖fderiv ℝ (Work.BoseBoxFock.L1Tails.psiM ℓ m G) z
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ ∑ j : Fin 3, ε ^ 2 * ℓ ^ 3 * ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖pairVj ℓ G j w y‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => psiM_dirichlet_per_j hℓ hεnn hG hfderiv hgap j
    _ = ε ^ 2 * ℓ ^ 3 * (∑ j : Fin 3, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ‖pairVj ℓ G j w y‖ ^ 2) := by
        rw [Finset.mul_sum]
    _ = ε ^ 2 * ℓ ^ 3 * Work.BoseBoxFock.L1Tails.pairDir' ℓ G := by rw [hsum]

end Work.BoseBoxFock.L1Tails
