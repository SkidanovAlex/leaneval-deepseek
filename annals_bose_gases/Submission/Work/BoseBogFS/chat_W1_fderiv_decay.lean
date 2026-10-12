import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseBogFS.W1funDecay_momentsAbs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.chat_W1_fderiv_decay`

The gradient of the cosine transform `Ŵ₁ = chat (W1fun v h ℓ)` inherits the `1/(1+‖q‖)` decay
of `Ŵ₁` itself:

  `∃ C, ‖fderiv ℝ (chat (W1fun v h ℓ)) q‖ ≤ C · (1+R)³/(1+‖q‖)`,

with `R` the range of the potential (`tsupport v ⊆ ball 0 R`).

## Route

The cosine transform is `Ŵ₁(q) = ∫ x, W₁(x)·cos⟪q,x⟫ dx` (`chat_eq_cos`, valid for the `L¹`
kernel `W₁ = wScaled ℓ (g₀ v h)`), and differentiating under the integral sign gives the exact
derivative

  `∇Ŵ₁(q) = ∫ x, (−W₁(x)·sin⟪q,x⟫) • (innerSL ℝ x)`

(the dominated derivative `hasFDerivAt_integral_of_dominated_of_fderiv_le`, with the integrable
majorant `‖x‖·|W₁ x|`; `W₁` is supported in `ball 0 R`, so `∫‖x‖|W₁| ≤ R∫|W₁| < ∞`).

Evaluating this continuous linear functional on the standard basis vector `e_j` and expanding
`⟪x,e_j⟫ = x_j` identifies it with the imaginary part of the `p`-convention Fourier transform of
the first moment `x_j W₁(x)`:

  `(∇Ŵ₁(q)) e_j = −∫ x, W₁(x)·sin(⟪q,x⟫)·x_j = Im (kinFT (fun y => y_j·W₁(y)) q)`.

The first-moment bound `W1funDecay_momentsAbs` (the `m = 1` case) therefore yields
`|(∇Ŵ₁(q)) e_j| ≤ K(1+R)³/(1+‖q‖)`, and the operator norm is controlled by the three basis
values (`‖L‖ ≤ ∑_j |L e_j|` for a linear functional on `ℝ³`).
-/

namespace Work.BoseBogFS

open MeasureTheory Metric
open scoped Real Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-- Imaginary part of the Fourier character times a real number: `Im(e^{−it}·w) = −w sin t`. -/
private lemma im_exp_mul_ofReal (t w : ℝ) :
    (Complex.exp (-(Complex.I * (t : ℂ))) * (w : ℂ)).im = -w * Real.sin t := by
  rw [Complex.mul_im, Complex.exp_im, Complex.exp_re, Complex.ofReal_re, Complex.ofReal_im]
  have h1 : (-(Complex.I * (t : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  have h2 : (-(Complex.I * (t : ℂ))).im = -t := by
    simp [Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [h1, h2]
  simp
  ring

/-- The norm of the continuous linear functional `innerSL ℝ x : y ↦ ⟪x,y⟫` is `≤ ‖x‖`. -/
private lemma innerSL_apply_norm_le (x : E3) : ‖innerSL ℝ x‖ ≤ ‖x‖ := by
  calc ‖innerSL ℝ x‖ = ‖(innerSL ℝ : E3 →L⋆[ℝ] E3 →L[ℝ] ℝ) x‖ := rfl
    _ ≤ ‖(innerSL ℝ : E3 →L⋆[ℝ] E3 →L[ℝ] ℝ)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
        exact norm_innerSL_le ℝ
    _ = ‖x‖ := one_mul _

/-- **Differentiation under the integral sign for the cosine transform.**
For an integrable `W` with integrable first moment, the function `q ↦ ∫ x, W x·cos⟪x,q⟫` has
Fréchet derivative `h ↦ −∫ x, W x·sin⟪x,q⟫·⟪x,h⟫` at `q`, i.e. the continuous linear map
`∫ x, (−W x·sin⟪x,q⟫) • innerSL ℝ x`. -/
private lemma hasFDerivAt_cosInt {W : E3 → ℝ} (hint : Integrable W)
    (h1 : Integrable fun y => ‖y‖ * |W y|) (q : E3) :
    HasFDerivAt (fun q : E3 => ∫ x : E3, W x * Real.cos (inner ℝ x q))
      (∫ x : E3, (-(W x * Real.sin (inner ℝ x q))) • (innerSL ℝ x)) q := by
  have htrig : ∀ (f : ℝ → ℝ), Continuous f → ∀ q : E3,
      AEStronglyMeasurable (fun x : E3 => f (inner ℝ x q)) volume :=
    fun f hf q =>
      (hf.comp (by fun_prop : Continuous (fun x : E3 => inner ℝ x q))).aestronglyMeasurable
  have hcos q := htrig Real.cos Real.continuous_cos q
  have hsin q := htrig Real.sin Real.continuous_sin q
  have hclm : AEStronglyMeasurable (fun x : E3 => innerSL ℝ x) volume :=
    (innerSL ℝ : E3 →L⋆[ℝ] E3 →L[ℝ] ℝ).continuous.aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable
      (fun x : E3 => (-(W x * Real.sin (inner ℝ x q))) • (innerSL ℝ x)) volume :=
    ((hint.aestronglyMeasurable.mul (hsin q)).neg).smul hclm
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q x => W x * Real.cos (inner ℝ x q))
    (F' := fun q x => (-(W x * Real.sin (inner ℝ x q))) • (innerSL ℝ x))
    (bound := fun x => ‖x‖ * |W x|) (s := Set.univ) (μ := volume) (x₀ := q)
    ?_ ?_ ?_ hF'meas ?_ h1 ?_
  · exact Filter.univ_mem
  · filter_upwards with x
    exact hint.aestronglyMeasurable.mul (hcos x)
  · exact hint.mul_bdd (hcos q) (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _))
  · filter_upwards with x
    intro q' _
    rw [norm_smul, Real.norm_eq_abs]
    calc |-(W x * Real.sin (inner ℝ x q'))| * ‖innerSL ℝ x‖
        ≤ |-(W x * Real.sin (inner ℝ x q'))| * ‖x‖ :=
          mul_le_mul_of_nonneg_left (innerSL_apply_norm_le x) (abs_nonneg _)
      _ ≤ (|W x| * 1) * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
          rw [abs_neg, abs_mul]
          exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
      _ = ‖x‖ * |W x| := by ring
  · filter_upwards with x
    intro q' _
    have hbase : HasFDerivAt (fun y : E3 => inner ℝ x y) (innerSL ℝ x) q' :=
      ContinuousLinearMap.hasFDerivAt (innerSL ℝ x)
    have h2 : HasFDerivAt (fun y : E3 => Real.cos (inner ℝ x y))
        ((-Real.sin (inner ℝ x q')) • (innerSL ℝ x)) q' := hbase.cos
    have h3 := h2.const_mul (W x)
    have h4 : W x • (-Real.sin (inner ℝ x q') • (innerSL ℝ x))
        = (-(W x * Real.sin (inner ℝ x q'))) • (innerSL ℝ x) := by
      rw [smul_smul]; congr 1; ring
    simpa only [h4] using h3

/-- The derivative of `Ŵ = chat W` is the continuous linear map
`h ↦ −∫ x, W x·sin⟪q,x⟫·⟪x,h⟫`. -/
private lemma fderiv_chat_eq {W : E3 → ℝ} (hint : Integrable W)
    (h1 : Integrable fun y => ‖y‖ * |W y|) (q : E3) :
    fderiv ℝ (Work.BoseFixR.chat W) q
      = ∫ x : E3, (-(W x * Real.sin (inner ℝ x q))) • (innerSL ℝ x) := by
  have h := hasFDerivAt_cosInt hint h1 q
  have heq : Work.BoseFixR.chat W =ᶠ[𝓝 q]
      (fun q : E3 => ∫ x : E3, W x * Real.cos (inner ℝ x q)) := by
    filter_upwards with q'
    rw [Work.BoseFixR.Rb5Lin.chat_eq_cos hint q']
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [real_inner_comm x q']
  exact (h.congr_of_eventuallyEq heq).fderiv

/-- The imaginary part of the `p`-Fourier transform of the first moment `x_j·W(x)` is
`−∫ x, W x·sin⟪q,x⟫·x_j`. -/
private lemma kinFT_im_eq (W : E3 → ℝ) (hint : Integrable W)
    (h1 : Integrable fun y => ‖y‖ * |W y|) (q : E3) (j : Fin 3) :
    (Submission.BoseGases.kinFT (fun y : E3 => (((y.ofLp j : ℝ) : ℂ) * ((W y : ℝ) : ℂ))) q).im
      = ∫ x : E3, (-(W x * Real.sin (inner ℝ x q))) * (x.ofLp j) := by
  have haesm : AEStronglyMeasurable
      (fun y : E3 => (((y.ofLp j : ℝ) : ℂ) * ((W y : ℝ) : ℂ))) volume :=
    ((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun y : E3 => y.ofLp j)
      )).aestronglyMeasurable.mul hint.ofReal.aestronglyMeasurable
  have hintj : Integrable (fun y : E3 => Complex.exp (-(Complex.I * (inner ℝ q y : ℂ)))
      * ((((y.ofLp j : ℝ) : ℂ) * ((W y : ℝ) : ℂ)))) := by
    refine Integrable.mono' (g := fun y => ‖y‖ * |W y|) h1 ?_ ?_
    · exact ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul haesm
    · filter_upwards with y
      rw [norm_mul, Complex.norm_exp]
      have h0 : (-(Complex.I * (inner ℝ q y : ℂ))).re = 0 := by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im]
      rw [h0, Real.exp_zero, one_mul, Complex.norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le y j) (abs_nonneg _)
  rw [Submission.BoseGases.kinFT, ← Complex.imCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hintj]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  simp only [Complex.imCLM_apply]
  rw [show (((y.ofLp j : ℝ) : ℂ) * ((W y : ℝ) : ℂ)) = ((y.ofLp j * W y : ℝ) : ℂ) by
    push_cast; ring]
  rw [im_exp_mul_ofReal]
  have hcomm : inner ℝ q y = inner ℝ y q := real_inner_comm y q
  rw [hcomm]
  push_cast
  ring

/-- **The operator-norm bound.**  If all three first-moment transforms of `W` are bounded by `K`
at `q`, then the continuous linear functional `∫ x, (−W x·sin⟪x,q⟫) • innerSL ℝ x` has operator
norm at most `3K` (its values on the three standard basis vectors are the components). -/
private lemma norm_integral_smul_innerSL_le {W : E3 → ℝ} (hint : Integrable W)
    (h1 : Integrable fun y => ‖y‖ * |W y|) (q : E3) {K : ℝ} (_hK0 : 0 ≤ K)
    (hK : ∀ j : Fin 3, ‖Submission.BoseGases.kinFT
        (fun y : E3 => (((y.ofLp j : ℝ) : ℂ) * ((W y : ℝ) : ℂ))) q‖ ≤ K) :
    ‖∫ x : E3, (-(W x * Real.sin (inner ℝ x q))) • (innerSL ℝ x)‖ ≤ 3 * K := by
  set L : E3 →L[ℝ] ℝ := ∫ x : E3, (-(W x * Real.sin (inner ℝ x q))) • (innerSL ℝ x) with hL
  have hclm : AEStronglyMeasurable (fun x : E3 => innerSL ℝ x) volume :=
    (innerSL ℝ : E3 →L⋆[ℝ] E3 →L[ℝ] ℝ).continuous.aestronglyMeasurable
  have hF'int : Integrable
      (fun x : E3 => (-(W x * Real.sin (inner ℝ x q))) • (innerSL ℝ x)) := by
    refine Integrable.mono' (g := fun x => ‖x‖ * |W x|) h1 ?_ ?_
    · exact ((hint.aestronglyMeasurable.mul ((Real.continuous_sin.comp
        (by fun_prop : Continuous (fun x : E3 => inner ℝ x q))).aestronglyMeasurable)).neg).smul hclm
    · filter_upwards with x
      rw [norm_smul, Real.norm_eq_abs]
      calc |-(W x * Real.sin (inner ℝ x q))| * ‖innerSL ℝ x‖
          ≤ |-(W x * Real.sin (inner ℝ x q))| * ‖x‖ :=
            mul_le_mul_of_nonneg_left (innerSL_apply_norm_le x) (abs_nonneg _)
        _ ≤ (|W x| * 1) * ‖x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
            rw [abs_neg, abs_mul]
            exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = ‖x‖ * |W x| := by ring
  have happly : ∀ h : E3, L h
      = ∫ x : E3, (-(W x * Real.sin (inner ℝ x q))) * (inner ℝ x h) := by
    intro h
    rw [hL, ContinuousLinearMap.integral_apply hF'int h]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  have hbasis : ∀ j : Fin 3, ‖L (EuclideanSpace.single j (1 : ℝ))‖ ≤ K := by
    intro j
    have hbj : L (EuclideanSpace.single j (1 : ℝ))
        = ∫ x : E3, (-(W x * Real.sin (inner ℝ x q))) * (x.ofLp j) := by
      rw [happly]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      simp [EuclideanSpace.inner_single_right]
    rw [hbj, ← kinFT_im_eq W hint h1 q j, Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hK j)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun h => ?_)
  have hdecomp : h = ∑ j : Fin 3, (h.ofLp j) • (EuclideanSpace.single j (1 : ℝ)) := by
    ext j
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hsplit : L h = ∑ j : Fin 3, (h.ofLp j) • (L (EuclideanSpace.single j (1 : ℝ))) := by
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [map_smul])
  calc ‖L h‖ = ‖∑ j : Fin 3, (h.ofLp j) • (L (EuclideanSpace.single j (1 : ℝ)))‖ :=
        by rw [hsplit]
    _ ≤ ∑ j : Fin 3, ‖(h.ofLp j) • (L (EuclideanSpace.single j (1 : ℝ)))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖h‖ * K := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (PiLp.norm_apply_le h j) (hbasis j) (norm_nonneg _) (norm_nonneg h)
    _ = 3 * K * ‖h‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_num
        ring

theorem chat_W1_fderiv_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ℓ : ℝ},
      0 < R → 0 < ℓ → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ q : EuclideanSpace ℝ (Fin 3),
        ‖fderiv ℝ (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)) q‖
          ≤ C * (1 + R) ^ 3 / (1 + ‖q‖) := by
  obtain ⟨K, hK0, hKmom⟩ := W1funDecay_momentsAbs
  refine ⟨3 * K, by positivity, ?_⟩
  intro v h R ℓ hR hℓ hv hvrad hv_supp hRℓ q
  have hW1int : Integrable (Work.BoseFixR.W1fun v h ℓ) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hsupp : ∀ x : E3, Work.BoseFixR.W1fun v h ℓ x ≠ 0 → ‖x‖ < R := by
    intro x hx
    refine lt_of_not_ge (fun hge => hx ?_)
    have hz : Submission.BoseGases.g0 v h x = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hge h
    simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hz]
  have h1 : Integrable (fun y : E3 => ‖y‖ * |Work.BoseFixR.W1fun v h ℓ y|) := by
    refine Integrable.mono' (hW1int.abs.const_mul R) ?_ ?_
    · exact (continuous_norm.aestronglyMeasurable).mul hW1int.aestronglyMeasurable.norm
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg x) (abs_nonneg _))]
      by_cases hx : Work.BoseFixR.W1fun v h ℓ x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_right (hsupp x hx).le (abs_nonneg _)
  have hbound : ∀ j : Fin 3, ‖Submission.BoseGases.kinFT
      (fun y : E3 => (((y.ofLp j : ℝ) : ℂ) * ((Work.BoseFixR.W1fun v h ℓ y : ℝ) : ℂ))) q‖
      ≤ K * (1 + R) ^ 3 / (1 + ‖q‖) := by
    intro j
    have hb := hKmom (v := v) (h := h) (R := R) (ℓ := ℓ)
      hR hℓ hv hvrad hv_supp hRℓ 1 (by norm_num) j q
    have hfun : (fun y : E3 => (((y.ofLp j : ℝ) ^ 1) * Work.BoseFixR.W1fun v h ℓ y : ℂ))
        = (fun y : E3 =>
            (((y.ofLp j : ℝ) : ℂ) * ((Work.BoseFixR.W1fun v h ℓ y : ℝ) : ℂ))) := by
      funext y
      push_cast
      ring
    rw [hfun] at hb
    exact hb
  rw [fderiv_chat_eq hW1int h1 q]
  refine (norm_integral_smul_innerSL_le hW1int h1 q (by positivity) hbound).trans (le_of_eq ?_)
  ring

end Work.BoseBogFS
