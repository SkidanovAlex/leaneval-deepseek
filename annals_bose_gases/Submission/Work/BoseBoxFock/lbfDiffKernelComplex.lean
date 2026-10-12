import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.integrable_riesz_pair_real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.lbfDiffKernelComplex`

The complex-valued Riesz difference kernel is additive over the real and imaginary parts:
`diffKernel g = diffKernel (re g) + diffKernel (im g)` for a Lipschitz, compactly supported
`g : ℝ³ → ℂ`.

The proof is the pointwise identity
`‖z - w‖² = ‖re z - re w‖² + ‖im z - im w‖²`
together with the integrability of the three Riesz pair integrands.  Integrability of the
`g`-integrand is the `rieszDom` domination argument of `SqrtKin.riesz_pair_integrable`, which
uses only the Lipschitz bound near the diagonal and the sup bound away from it; here the function
is only assumed Lipschitz (not smooth), and the bounds `hLip`/`hBd` are supplied directly.  The
`re`/`im` integrands are dominated by the `g`-integrand because `|re z| ≤ ‖z‖` and `|im z| ≤ ‖z‖`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **`diffKernel` as a single integral over the product space.**  This is the shape in which the
additivity of the integrand can be used. -/
lemma diffKernel_eq_integral_prod {u : ℝ³ → ℂ}
    (h : Integrable (fun q : ℝ³ × ℝ³ => ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖u q.1 - u q.2‖ ^ 2)
      (volume.prod volume)) :
    diffKernel u = ∫ q : ℝ³ × ℝ³, ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖u q.1 - u q.2‖ ^ 2 := by
  rw [diffKernel]
  exact (integral_prod (fun q : ℝ³ × ℝ³ =>
    ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖u q.1 - u q.2‖ ^ 2) h).symm

/-- **The pointwise decomposition of the squared complex difference**:
`‖z - w‖² = ‖re z - re w‖² + ‖im z - im w‖²`. -/
lemma norm_sq_sub_eq_re_add_im (z w : ℂ) :
    ‖z - w‖ ^ 2
      = ‖((z.re : ℂ) - (w.re : ℂ))‖ ^ 2 + ‖((z.im : ℂ) - (w.im : ℂ))‖ ^ 2 := by
  rw [norm_sq_ofReal_sub, norm_sq_ofReal_sub]
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- **The Riesz pair integrand of a Lipschitz, compactly supported `g : ℝ³ → ℂ` is
product-measure integrable.**  This is `SqrtKin.riesz_pair_integrable` with the smoothness
hypothesis replaced by the explicit Lipschitz and sup bounds (which is what the domination
argument actually consumes). -/
lemma integrable_riesz_pair_of_lipschitz {g : ℝ³ → ℂ} {C B : ℝ} (hgm : Measurable g)
    (hLip : ∀ x y : ℝ³, ‖g x - g y‖ ≤ C * ‖x - y‖) (hBd : ∀ x : ℝ³, ‖g x‖ ≤ B)
    (hgc : HasCompactSupport g) :
    Integrable (fun q : ℝ³ × ℝ³ =>
      ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2) (volume.prod volume) := by
  have hTmeas : MeasurableSet (tsupport g) := (isClosed_tsupport g).measurableSet
  have hTfin : volume (tsupport g) ≠ ⊤ := hgc.isCompact.measure_lt_top.ne
  have hG : Integrable (fun q : ℝ³ × ℝ³ => SqrtKin.rieszDom C B (q.1 - q.2) *
      ((tsupport g).indicator (fun _ => (1 : ℝ)) q.1 +
        (tsupport g).indicator (fun _ => (1 : ℝ)) q.2)) (volume.prod volume) :=
    SqrtKin.integrable_sub_kernel_mul_indicator (SqrtKin.integrable_rieszDom C B)
      (SqrtKin.rieszDom_even C B) hTmeas hTfin
  refine Integrable.mono' hG ?_ ?_
  · have hk : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ =>
        ‖q.1 - q.2‖ ^ (-(4 : ℝ))) (volume.prod volume) :=
      (by fun_prop : Measurable fun q : ℝ³ × ℝ³ =>
        ‖q.1 - q.2‖ ^ (-(4 : ℝ))).aestronglyMeasurable
    have hb : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ =>
        ‖g q.1 - g q.2‖ ^ 2) (volume.prod volume) :=
      (((hgm.comp measurable_fst).sub (hgm.comp measurable_snd)).norm.pow_const 2
        ).aestronglyMeasurable
    exact hk.mul hb
  · filter_upwards with q
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _))]
    exact SqrtKin.rieszDom_pointwise_bound hLip hBd
      (fun x hx => by by_contra h; exact hx (subset_tsupport g h)) q

/-- **Domination transfer.**  If the squared difference of `u` is pointwise dominated by that of
`v` (in norm), the Riesz pair integrand of `u` is integrable as soon as that of `v` is. -/
lemma integrable_of_sq_le {u v : ℝ³ → ℂ}
    (hAESM : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ =>
      ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖u q.1 - u q.2‖ ^ 2) (volume.prod volume))
    (hle : ∀ x y : ℝ³, ‖u x - u y‖ ^ 2 ≤ ‖v x - v y‖ ^ 2)
    (hv : Integrable (fun q : ℝ³ × ℝ³ =>
      ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖v q.1 - v q.2‖ ^ 2) (volume.prod volume)) :
    Integrable (fun q : ℝ³ × ℝ³ =>
      ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖u q.1 - u q.2‖ ^ 2) (volume.prod volume) := by
  refine Integrable.mono' hv hAESM ?_
  filter_upwards with q
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left (hle q.1 q.2) (Real.rpow_nonneg (norm_nonneg _) _)

/-- The pointwise additivity of the Riesz pair integrand over `re`/`im`. -/
lemma diffIntegrand_decomp (g : ℝ³ → ℂ) (q : ℝ³ × ℝ³) :
    ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2
      = ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖((g q.1).re : ℂ) - ((g q.2).re : ℂ)‖ ^ 2
        + ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖((g q.1).im : ℂ) - ((g q.2).im : ℂ)‖ ^ 2 := by
  rw [norm_sq_sub_eq_re_add_im (g q.1) (g q.2)]
  ring

theorem lbfDiffKernelComplex {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ∃ C, ∀ x y, ‖g x - g y‖ ≤ C * ‖x - y‖) (hgc : HasCompactSupport g) :
    diffKernel g = diffKernel (fun x : EuclideanSpace ℝ (Fin 3) => ((g x).re : ℂ))
      + diffKernel (fun x : EuclideanSpace ℝ (Fin 3) => ((g x).im : ℂ)) := by
  obtain ⟨C₀, hC₀⟩ := hg
  have hLip : ∀ x y : ℝ³, ‖g x - g y‖ ≤ max C₀ 0 * ‖x - y‖ := fun x y =>
    (hC₀ x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hcont : Continuous g := by
    have hL : LipschitzWith (Real.toNNReal (max C₀ 0)) g := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (le_max_right _ _)]
      exact hLip x y
    exact hL.continuous
  have hgm : Measurable g := hcont.measurable
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hgc
  have hIg : Integrable (fun q : ℝ³ × ℝ³ =>
      ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2) (volume.prod volume) :=
    integrable_riesz_pair_of_lipschitz hgm hLip hB hgc
  have hcr : Continuous fun x : ℝ³ => ((g x).re : ℂ) :=
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp hcont)
  have hci : Continuous fun x : ℝ³ => ((g x).im : ℂ) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp hcont)
  have hIre : Integrable (fun q : ℝ³ × ℝ³ =>
      ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖((g q.1).re : ℂ) - ((g q.2).re : ℂ)‖ ^ 2)
      (volume.prod volume) := by
    refine integrable_of_sq_le (u := fun x : ℝ³ => ((g x).re : ℂ)) (v := g) ?_ ?_ hIg
    · have hk : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ =>
          ‖q.1 - q.2‖ ^ (-(4 : ℝ))) (volume.prod volume) :=
        (by fun_prop : Measurable fun q : ℝ³ × ℝ³ =>
          ‖q.1 - q.2‖ ^ (-(4 : ℝ))).aestronglyMeasurable
      have hb : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ =>
          ‖((g q.1).re : ℂ) - ((g q.2).re : ℂ)‖ ^ 2) (volume.prod volume) :=
        (((hcr.comp continuous_fst).sub (hcr.comp continuous_snd)).norm.pow 2
          ).aestronglyMeasurable
      exact hk.mul hb
    · intro x y
      rw [norm_sq_ofReal_sub]
      have hz : (g x).re - (g y).re = (g x - g y).re := (Complex.sub_re _ _).symm
      rw [hz]
      calc ((g x - g y).re) ^ 2 = |(g x - g y).re| ^ 2 := (sq_abs _).symm
        _ ≤ ‖g x - g y‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  have hIim : Integrable (fun q : ℝ³ × ℝ³ =>
      ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖((g q.1).im : ℂ) - ((g q.2).im : ℂ)‖ ^ 2)
      (volume.prod volume) := by
    refine integrable_of_sq_le (u := fun x : ℝ³ => ((g x).im : ℂ)) (v := g) ?_ ?_ hIg
    · have hk : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ =>
          ‖q.1 - q.2‖ ^ (-(4 : ℝ))) (volume.prod volume) :=
        (by fun_prop : Measurable fun q : ℝ³ × ℝ³ =>
          ‖q.1 - q.2‖ ^ (-(4 : ℝ))).aestronglyMeasurable
      have hb : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ =>
          ‖((g q.1).im : ℂ) - ((g q.2).im : ℂ)‖ ^ 2) (volume.prod volume) :=
        (((hci.comp continuous_fst).sub (hci.comp continuous_snd)).norm.pow 2
          ).aestronglyMeasurable
      exact hk.mul hb
    · intro x y
      rw [norm_sq_ofReal_sub]
      have hz : (g x).im - (g y).im = (g x - g y).im := (Complex.sub_im _ _).symm
      rw [hz]
      calc ((g x - g y).im) ^ 2 = |(g x - g y).im| ^ 2 := (sq_abs _).symm
        _ ≤ ‖g x - g y‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
  have h1 : diffKernel g
      = ∫ q : ℝ³ × ℝ³, ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2 :=
    diffKernel_eq_integral_prod hIg
  have h2 : diffKernel (fun x : ℝ³ => ((g x).re : ℂ))
      = ∫ q : ℝ³ × ℝ³,
          ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖((g q.1).re : ℂ) - ((g q.2).re : ℂ)‖ ^ 2 :=
    diffKernel_eq_integral_prod hIre
  have h3 : diffKernel (fun x : ℝ³ => ((g x).im : ℂ))
      = ∫ q : ℝ³ × ℝ³,
          ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖((g q.1).im : ℂ) - ((g q.2).im : ℂ)‖ ^ 2 :=
    diffKernel_eq_integral_prod hIim
  rw [h1, h2, h3]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun q => diffIntegrand_decomp g q)).trans ?_
  exact integral_add hIre hIim

end Work.BoseBoxFock
