/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.BallTent
import Submission.Commons.Analysis.Fourier.exists_ball_bump_fourier_scaled_measurable
import Submission.Vinogradov.DecouplesBridge
import Submission.Commons.Analysis.Fourier.exists_ball_bump_uniform

/-!
# The ball bump and GLYZ Corollary 3.7 (the localised decoupling inequality)

This module turns the Fleet's bump construction
(`Commons.Analysis.Fourier.exists_ball_bump_fourier_scaled_measurable`) into the object GLYZ
Corollary 3.7 needs, and proves the Corollary itself:

* `exists_ball_bump_at` — for a ball `Metric.ball c R` and an exponent `A ≥ 0` there is a bump
  `ψ`, lying in the class `𝒞(B(0,σ))` with `σ R ≤ 1`, with `‖ψ‖ ≥ 1/2` on the ball and the tent
  decay `‖ψ x‖ ≤ C (1 + dist(x,B)/R)^{-A}`;
* `curveDecLoc_of_curveDec` — the localised inequality `CurveDecLoc` follows from the global one
  `CurveDec` at twice the enlargement (the ball absorption `plate_add_ball_subset`).
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The bump adapted to a ball -/

/-- The unit-scale bump `(ψ₀, Φ, σ)` of the commons, translated so that it is adapted to the ball
`Metric.ball c R`.  The translated bump is `x ↦ ψ₀ (x - c)`; translation multiplies the Fourier
density by the unimodular factor `η ↦ e(-⟪c,η⟫)`, so the class and both pointwise bounds are
unchanged. -/
lemma ball_bump_translate {l : ℕ} {A R C σ : ℝ} {c : E l} {ψ₀ : E l → ℂ} {Φ : E l → ℂ}
    (hR : 1 ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C) (hσpos : 0 < σ)
    (hΦmeas : Measurable Φ) (hΦint : Integrable Φ)
    (hΦsupp : ∀ η, Φ η ≠ 0 → η ∈ Metric.closedBall 0 σ)
    (hrep : ∀ x, ψ₀ x
      = ∫ η, Φ η * Complex.exp (2 * Real.pi * Complex.I * ((∑ i, x i * η i : ℝ) : ℂ)))
    (hlow : ∀ x, ‖x‖ ≤ R → (1 / 2 : ℝ) ≤ ‖ψ₀ x‖)
    (hdec : ∀ x, ‖ψ₀ x‖ ≤ C * (1 + ‖x‖ / R) ^ (-A)) :
    ∃ ψ : E l → ℂ, IsFourierRep l (Metric.closedBall 0 σ) ψ ∧
      (∀ x, ‖x - c‖ ≤ R → (1 / 2 : ℝ) ≤ ‖ψ x‖) ∧
      (∀ x, ‖ψ x‖ ≤ C * (1 + Metric.infDist x (Metric.ball c R) / R) ^ (-A)) := by
  have hcchat : Measurable (fun η : E l => chat l (-c) η) :=
    (continuous_chat_left l (-c)).measurable
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hInfl : Integrable (fun η : E l => Φ η * chat l (-c) η)
      ((volume : Measure (E l)).restrict (Metric.closedBall 0 σ)) := by
    refine (hΦint.mono_measure Measure.restrict_le_self).mul_bdd (c := (1 : ℝ))
      hcchat.aestronglyMeasurable (Filter.Eventually.of_forall fun η => ?_)
    rw [chat_norm]
  have hfin : IsFiniteMeasure ((volume : Measure (E l)).restrict (Metric.closedBall 0 σ)) := by
    rw [isFiniteMeasure_iff, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact measure_closedBall_lt_top
  have hclass : IsFourierRep l (Metric.closedBall 0 σ) (fun x => ψ₀ (x - c)) := by
    refine IsFourierRep.mk' (ι := E l) (Γ := fun η : E l => η)
      (ν := (volume : Measure (E l)).restrict (Metric.closedBall 0 σ))
      (φ := fun η : E l => Φ η * chat l (-c) η) hfin hInfl measurable_id
      (hΦmeas.mul hcchat) ?_ ?_
    · intro η hη
      exact hΦsupp η (mul_ne_zero_iff.mp hη).1
    · intro x
      have hpt : ∀ η : E l, Φ η * Complex.exp (2 * Real.pi * Complex.I *
            (((∑ i : Fin l, (x - c) i * η i : ℝ)) : ℂ))
          = Φ η * (chat l x η * chat l (-c) η) := by
        intro η
        congr 1
        rw [← chat_add_left l x (-c) η, show x + -c = x - c from rfl, chat]
        have hinner : (⟪x - c, η⟫ : ℝ) = ∑ i : Fin l, (x - c) i * η i := by
          rw [PiLp.inner_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [mul_comm]
        rw [hinner]
      have hpt2 : ∀ η : E l, Φ η * (chat l x η * chat l (-c) η)
          = (Φ η * chat l (-c) η) * chat l x η := fun η => by ring
      have hsupp : ∀ η : E l, η ∉ Metric.closedBall 0 σ →
          (Φ η * chat l (-c) η) * chat l x η = 0 := by
        intro η hη
        have h0 : Φ η = 0 := by
          by_contra hne
          exact hη (hΦsupp η hne)
        rw [h0, zero_mul, zero_mul]
      calc ψ₀ (x - c)
          = ∫ η : E l, Φ η * (chat l x η * chat l (-c) η) ∂volume := by
              rw [hrep (x - c)]
              exact integral_congr_ae (Filter.Eventually.of_forall hpt)
        _ = ∫ η : E l, (Φ η * chat l (-c) η) * chat l x η ∂volume :=
              integral_congr_ae (Filter.Eventually.of_forall hpt2)
        _ = ∫ η in Metric.closedBall 0 σ, (Φ η * chat l (-c) η) * chat l x η ∂volume :=
              (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
        _ = ∫ η : E l, chat l x η * (Φ η * chat l (-c) η)
              ∂((volume : Measure (E l)).restrict (Metric.closedBall 0 σ)) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
              ring
  refine ⟨fun x => ψ₀ (x - c), hclass, ?_, ?_⟩
  · intro x hx
    exact hlow (x - c) hx
  · intro x
    refine (hdec (x - c)).trans ?_
    have hle : Metric.infDist x (Metric.ball c R) ≤ ‖x - c‖ := by
      have hmem : c ∈ Metric.ball c R := Metric.mem_ball_self hRpos
      simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (s := Metric.ball c R) hmem
    have h0 : (0 : ℝ) ≤ Metric.infDist x (Metric.ball c R) := Metric.infDist_nonneg
    have h1 : 0 < 1 + Metric.infDist x (Metric.ball c R) / R := by
      have : 0 ≤ Metric.infDist x (Metric.ball c R) / R := div_nonneg h0 hRpos.le
      linarith
    have h2 : 1 + Metric.infDist x (Metric.ball c R) / R ≤ 1 + ‖x - c‖ / R := by
      have := div_le_div_of_nonneg_right hle hRpos.le
      linarith
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith : -A ≤ 0)) hC

/-- **The ball bump** (non-uniform version), transported to the ball `Metric.ball c R`. -/
lemma exists_ball_bump_at (l : ℕ) (hl : 1 ≤ l) {A R : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R) (c : E l) :
    ∃ (ψ : E l → ℂ) (σ C : ℝ), 0 < σ ∧ σ * R ≤ 1 ∧ 0 < C ∧
      IsFourierRep l (Metric.closedBall 0 σ) ψ ∧
      (∀ x, ‖x - c‖ ≤ R → (1 / 2 : ℝ) ≤ ‖ψ x‖) ∧
      (∀ x, ‖ψ x‖ ≤ C * (1 + Metric.infDist x (Metric.ball c R) / R) ^ (-A)) := by
  obtain ⟨ψ₀, Φ, σ, C, hσpos, hσR, hCpos, hΦmeas, hΦnn, hΦint, hΦsupp, hrep, hlow, hdec⟩ :=
    Commons.Analysis.Fourier.exists_ball_bump_fourier_scaled_measurable l hl A hA R hR
  obtain ⟨ψ, hcl, hlo, hde⟩ :=
    ball_bump_translate (c := c) hR hA hCpos.le hσpos hΦmeas hΦint hΦsupp hrep hlow hdec
  exact ⟨ψ, σ, C, hσpos, hσR, hCpos, hcl, hlo, hde⟩

/-! ## 2. The ball absorption for a general curve plate -/

/-- The unit box is convex. -/
lemma convex_unitBox' (l : ℕ) : Convex ℝ (unitBox l) := by
  have h : unitBox l = (WithLp.linearEquiv 2 ℝ (Fin l → ℝ)) ⁻¹'
      Set.pi Set.univ (fun _ : Fin l => Set.Icc (-1 : ℝ) 1) := by
    ext y
    simp only [unitBox, Set.mem_preimage, WithLp.coe_linearEquiv, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Icc, abs_le, Set.mem_ofPred_eq]
  rw [h]
  exact (convex_pi fun _ _ => convex_Icc (-1 : ℝ) 1).linear_preimage _

/-- The centred box of the curve plate at scale `δ` about `t` is convex. -/
lemma convex_curvePlateBox {l : ℕ} (D : ℕ → ℝ → E l) (δ t : ℝ) :
    Convex ℝ (curvePlateLin l D δ t '' unitBox l) :=
  (convex_unitBox' l).linear_image (curvePlateLin l D δ t)

lemma zero_mem_curvePlateBox {l : ℕ} (D : ℕ → ℝ → E l) (δ t : ℝ) :
    (0 : E l) ∈ curvePlateLin l D δ t '' unitBox l :=
  ⟨0, by simp [unitBox], map_zero _⟩

/-- **Scaling a plate box.**  For `λ ≥ 1`, `λ` times the centred box at scale `δ` is contained in
the box at scale `λ δ`.  (This is `Projection.smul_curvePlateLin_subset`, reproduced here to keep
this module free of the projection layer.) -/
lemma smul_curvePlateBox_subset {l : ℕ} (D : ℕ → ℝ → E l) {δ t lam : ℝ} (hlam : 1 ≤ lam) :
    lam • (curvePlateLin l D δ t '' unitBox l)
      ⊆ curvePlateLin l D (lam * δ) t '' unitBox l := by
  rintro x ⟨y, ⟨w, hw, rfl⟩, rfl⟩
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  refine ⟨(WithLp.equiv 2 (Fin l → ℝ)).symm (fun i => w i / lam ^ (i.val)), ?_, ?_⟩
  · intro i
    have hcoe : ((WithLp.equiv 2 (Fin l → ℝ)).symm (fun i => w i / lam ^ (i.val))) i
        = w i / lam ^ (i.val) := rfl
    rw [hcoe, abs_div, abs_of_nonneg (pow_nonneg hlam0.le _), div_le_one (pow_pos hlam0 _)]
    exact (hw i).trans (one_le_pow₀ hlam)
  · have hmain : lam • curvePlateLin l D δ t w
        = curvePlateLin l D (lam * δ) t ((WithLp.equiv 2 (Fin l → ℝ)).symm
            (fun i => w i / lam ^ (i.val))) := by
      rw [curvePlateLin_apply, Finset.smul_sum, curvePlateLin_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hcoe : ((WithLp.equiv 2 (Fin l → ℝ)).symm (fun i => w i / lam ^ (i.val))) i
          = w i / lam ^ (i.val) := rfl
      rw [hcoe]
      have hscal : lam * w i * δ ^ (i.val + 1)
          = w i / lam ^ (i.val) * (lam * δ) ^ (i.val + 1) := by
        have h1 : (lam * δ) ^ (i.val + 1) = lam ^ (i.val + 1) * δ ^ (i.val + 1) := mul_pow _ _ _
        rw [h1, pow_succ lam i.val]
        field_simp
      rw [smul_smul, smul_smul, hscal, smul_smul]
    exact hmain.symm

/-- A ball around `D 0 t` inside the curve plate is, after translation, a ball around `0`
inside the centred box. -/
lemma ball_subset_curvePlateBox {l : ℕ} {D : ℕ → ℝ → E l} {δ t ρ : ℝ}
    (h : Metric.ball (D 0 t) ρ ⊆ curvePlate l D δ t) :
    Metric.ball 0 ρ ⊆ curvePlateLin l D δ t '' unitBox l := by
  intro z hz
  have hzn : ‖z‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hz' : D 0 t + z ∈ Metric.ball (D 0 t) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hzn
  obtain ⟨z₀, hz₀, hz₀eq⟩ := h hz'
  exact ⟨z₀, hz₀, add_left_cancel hz₀eq⟩

/-- **The ball absorption for the plate of a general curve.**  If the plate of scale `δ` about
`t` contains the ball of radius `ρ` around its centre, then adding a vector of norm at most
`ε ρ` lands in the plate of scale `(1+ε)δ`. -/
lemma curvePlate_add_ball_subset_of {l : ℕ} {D : ℕ → ℝ → E l} {δ t ρ ε : ℝ} (hε : 0 ≤ ε)
    (hρ : Metric.ball (D 0 t) ρ ⊆ curvePlate l D δ t) {x w : E l}
    (hx : x ∈ curvePlate l D δ t) (hw : ‖w‖ < ε * ρ) :
    x + w ∈ curvePlate l D ((1 + ε) * δ) t := by
  obtain ⟨z, hz, hzx⟩ := hx
  have hKconv : Convex ℝ (curvePlateLin l D δ t '' unitBox l) := convex_curvePlateBox D δ t
  have hK0 : (0 : E l) ∈ curvePlateLin l D δ t '' unitBox l := zero_mem_curvePlateBox D δ t
  have hball : Metric.ball 0 ρ ⊆ curvePlateLin l D δ t '' unitBox l :=
    ball_subset_curvePlateBox hρ
  have hwK : w ∈ ε • (curvePlateLin l D δ t '' unitBox l) := by
    rcases eq_or_lt_of_le hε with h0 | hpos
    · -- `ε = 0`: then `w = 0`
      have hw0 : w = 0 := by
        have : ‖w‖ < 0 := by simpa [← h0, mul_zero] using hw
        exact absurd (norm_nonneg w) (not_le.mpr this)
      subst hw0
      exact ⟨0, hK0, by simp⟩
    · refine ⟨ε⁻¹ • w, hball ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr hε), inv_mul_lt_iff₀ hpos]
        linarith
      · change ε • (ε⁻¹ • w) = w
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  have hsum : curvePlateLin l D δ t z + w
      ∈ (curvePlateLin l D δ t '' unitBox l) + ε • (curvePlateLin l D δ t '' unitBox l) :=
    ⟨curvePlateLin l D δ t z, ⟨z, hz, rfl⟩, w, hwK, rfl⟩
  have hconv : (curvePlateLin l D δ t '' unitBox l) + ε • (curvePlateLin l D δ t '' unitBox l)
      ⊆ (1 + ε) • (curvePlateLin l D δ t '' unitBox l) := by
    rintro q ⟨a, ha, b, ⟨c, hc, rfl⟩, rfl⟩
    have hε1 : (0 : ℝ) < 1 + ε := by linarith
    have hmem : (1 / (1 + ε)) • a + (ε / (1 + ε)) • c ∈ curvePlateLin l D δ t '' unitBox l := by
      refine hKconv ha hc (by positivity) (by positivity) ?_
      field_simp
    refine ⟨(1 / (1 + ε)) • a + (ε / (1 + ε)) • c, hmem, ?_⟩
    change (1 + ε) • ((1 / (1 + ε)) • a + (ε / (1 + ε)) • c) = a + ε • c
    rw [smul_add, smul_smul, smul_smul]
    have h1 : (1 + ε) * (1 / (1 + ε)) = 1 := by field_simp
    have h2 : (1 + ε) * (ε / (1 + ε)) = ε := by field_simp
    rw [h1, h2, one_smul]
  have hscale : (1 + ε) • (curvePlateLin l D δ t '' unitBox l)
      ⊆ curvePlateLin l D ((1 + ε) * δ) t '' unitBox l :=
    smul_curvePlateBox_subset D (by linarith : (1 : ℝ) ≤ 1 + ε)
  obtain ⟨y, hy, hyeq⟩ := hscale (hconv hsum)
  refine ⟨y, hy, ?_⟩
  rw [← hzx]
  show D 0 t + curvePlateLin l D ((1 + ε) * δ) t y
    = D 0 t + curvePlateLin l D δ t z + w
  rw [hyeq]
  abel

/-! ## 3. Corollary 3.7: the localised decoupling inequality -/

/-- The `L^{p_l}` norm of a function against the ball tent, as an `ℝ≥0∞`-valued quantity. -/
noncomputable def tentNorm (l : ℕ) (A : ℝ) (c : E l) (R : ℝ) (F : E l → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, (‖F x‖₊ : ℝ≥0∞) ^ (plExp l) * ballTent l A c R x

/-- `(‖a‖₊)^r = ofReal (‖a‖^r)` for `r ≥ 0`. -/
lemma coe_nnnorm_rpow' (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ((‖a‖₊ : NNReal) : ℝ≥0∞) ^ r = ENNReal.ofReal (‖a‖ ^ r) := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg a) hr]
  simp [ENNReal.ofReal]

/-- The `L^{p_l}` norm of a function, raised to the power `p_l`, is the integral of the
`p_l`-th power of its pointwise norm. -/
lemma lintegral_nnnorm_rpow_eq_lpNorm_pow (l : ℕ) (hl : 1 ≤ l) (F : E l → ℂ) :
    ∫⁻ x, (‖F x‖₊ : ℝ≥0∞) ^ (plExp l) = (lpNorm l (pE l) F) ^ (plExp l) := by
  rw [show plExp l = critQ l from rfl, lpNorm_pow_eq_lintegral l hl F]
  refine lintegral_congr fun x => ?_
  rw [coe_nnnorm_rpow' (F x) (by rw [critQ_eq]; positivity)]

/-- **The localising step of Corollary 3.7.**  If `‖g‖^p ≤ 2^p‖h‖^p` on the ball `B(c,R)`, then
the average of `‖g‖^p` over the ball is at most `|B|^{-1}·2^p` times the full integral of
`‖h‖^p`. -/
lemma ballAvg_le_of_two_mul {l : ℕ} {p : ℝ} {c : E l} {R : ℝ} {g h : E l → ℂ}
    (hpt : ∀ x ∈ Metric.ball c R,
      (‖g x‖₊ : ℝ≥0∞) ^ p ≤ 2 ^ p * (‖h x‖₊ : ℝ≥0∞) ^ p) :
    ballAvg p c R g ≤ (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
      * (2 ^ p * ∫⁻ x, (‖h x‖₊ : ℝ≥0∞) ^ p) := by
  rw [ballAvg_apply]
  refine mul_le_mul' le_rfl ?_
  have h1 : (∫⁻ x in Metric.ball c R, (‖g x‖₊ : ℝ≥0∞) ^ p)
      ≤ ∫⁻ x in Metric.ball c R, 2 ^ p * (‖h x‖₊ : ℝ≥0∞) ^ p := by
    refine lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with x hx
    exact hpt x hx
  have h2 : (∫⁻ x in Metric.ball c R, 2 ^ p * (‖h x‖₊ : ℝ≥0∞) ^ p)
      = 2 ^ p * ∫⁻ x in Metric.ball c R, (‖h x‖₊ : ℝ≥0∞) ^ p :=
    lintegral_const_mul' _ _ (by simp)
  have h3 : (∫⁻ x in Metric.ball c R, (‖h x‖₊ : ℝ≥0∞) ^ p)
      ≤ ∫⁻ x, (‖h x‖₊ : ℝ≥0∞) ^ p := by
    rw [← lintegral_indicator measurableSet_ball]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ Metric.ball c R
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact bot_le
  calc (∫⁻ x in Metric.ball c R, (‖g x‖₊ : ℝ≥0∞) ^ p)
      ≤ ∫⁻ x in Metric.ball c R, 2 ^ p * (‖h x‖₊ : ℝ≥0∞) ^ p := h1
    _ = 2 ^ p * ∫⁻ x in Metric.ball c R, (‖h x‖₊ : ℝ≥0∞) ^ p := h2
    _ ≤ 2 ^ p * ∫⁻ x, (‖h x‖₊ : ℝ≥0∞) ^ p := mul_le_mul' le_rfl h3

/-! ## 4. The two structural steps of Corollary 3.7 -/

/-- **The class of a piece multiplied by the ball bump.**  Under the inradius hypothesis, the
product of a piece of the plate of scale `lam/(2m)` with a bump whose Fourier transform is
supported in a ball of radius `σ ≤ 1/R` (with `R ≥ m^l`) lies in the class of the plate of the
enlarged scale `lam'/(2m)`, provided `lam' ≥ 2 lam`. -/
lemma isFourierRep_mul_ball_bump {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l) {m : ℕ} (hm : 1 ≤ m)
    {lam lam' ρ : ℝ} (hlam : 1 ≤ lam) (hρ : 0 < ρ)
    (hρl : (2 : ℝ) ^ (l + 2) ≤ ρ * lam ^ l)
    (hrad : ∀ j : Fin m, Metric.ball (D 0 (pieceCenter m j)) (ρ * (lam / (2 * m)) ^ l)
              ⊆ curvePlate l D (lam / (2 * m)) (pieceCenter m j))
    (hlam' : 2 * lam ≤ lam') {j : Fin m} {σ R : ℝ} (hσR : σ * R ≤ 1) (hR : (m : ℝ) ^ l ≤ R)
    {ψ : E l → ℂ} (hψ : IsFourierRep l (Metric.closedBall 0 σ) ψ)
    {f : E l → ℂ} (hf : IsFourierRep l (curvePlate l D (lam / (2 * m)) (pieceCenter m j)) f) :
    IsFourierRep l (curvePlate l D (lam' / (2 * m)) (pieceCenter m j))
      (fun x => f x * ψ x) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (pow_pos hmpos l) hR
  have hlampos : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hε' : (1 : ℝ) ≤ lam' / lam - 1 := by
    rw [le_sub_iff_add_le, one_add_one_eq_two]
    exact (le_div_iff₀ hlampos).mpr hlam'
  have hσle : σ ≤ 1 / (m : ℝ) ^ l := by
    have hml : (0 : ℝ) < (m : ℝ) ^ l := pow_pos hmpos l
    have h1 : σ ≤ 1 / R := by
      rw [le_div_iff₀ hRpos]; linarith [hσR]
    have h2 : 1 / R ≤ 1 / (m : ℝ) ^ l := one_div_le_one_div_of_le hml hR
    linarith
  have hbase : (2 : ℝ) / (m : ℝ) ^ l ≤ (ρ / 2) * (lam / (2 * m)) ^ l := by
    have h1 : (ρ / 2) * (lam / (2 * m)) ^ l * (m : ℝ) ^ l = ρ * lam ^ l / 2 ^ (l + 1) := by
      rw [div_pow]
      field_simp
      ring
    rw [div_le_iff₀ (pow_pos hmpos l), h1, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (l + 1))]
    have h2 : (2 : ℝ) * 2 ^ (l + 1) = 2 ^ (l + 2) := by ring
    rw [h2]
    exact hρl
  refine (hf.mul hψ).mono ?_
  rintro z ⟨u, hu, v, hv, rfl⟩
  have hv' : ‖v‖ ≤ σ := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hv
    exact hv
  have hstrict' : ‖v‖ < (lam' / lam - 1) * (ρ / 2 * (lam / (2 * m)) ^ l) := by
    have hstep : (2 : ℝ) / (m : ℝ) ^ l
        ≤ (lam' / lam - 1) * ((ρ / 2) * (lam / (2 * m)) ^ l) := by
      calc (2 : ℝ) / (m : ℝ) ^ l ≤ 1 * ((ρ / 2) * (lam / (2 * m)) ^ l) := by
            rw [one_mul]; exact hbase
        _ ≤ (lam' / lam - 1) * ((ρ / 2) * (lam / (2 * m)) ^ l) :=
            mul_le_mul_of_nonneg_right hε' (by positivity)
    have h2 : 1 / (m : ℝ) ^ l < 2 / (m : ℝ) ^ l := by
      rw [div_lt_div_iff_of_pos_right (pow_pos hmpos l)]
      norm_num
    linarith [hσle]
  have hprev := curvePlate_add_ball_subset_of (D := D) (δ := lam / (2 * m))
    (t := pieceCenter m j) (ρ := ρ / 2 * (lam / (2 * m)) ^ l) (ε := lam' / lam - 1)
    (by positivity) ?_ hu hstrict'
  · convert hprev using 2
    field_simp
    ring
  · refine (Metric.ball_subset_ball ?_).trans (hrad j)
    have hd : 0 < (lam / (2 * m)) ^ l := by positivity
    nlinarith [hρ.le, hd]

/-- **The weighted norm of a piece multiplied by the bump.**  The `L^{p_l}` norm of `f ψ`,
raised to the power `p_l`, is bounded by the tent norm of `f` times the constants of the bump
(there is no loss in the radius: this is where the `|B|` of the `L¹`-normalised tent is used). -/
lemma lpNorm_mul_le_of_decay {l : ℕ} (hl : 1 ≤ l) {A Cb : ℝ} (hCb : 0 < Cb) {c : E l} {R : ℝ}
    (hR : 0 < R) {ψ f : E l → ℂ}
    (hψdec : ∀ x, ‖ψ x‖ ≤ Cb * (1 + Metric.infDist x (Metric.ball c R) / R) ^ (-(A / plExp l))) :
    (lpNorm l (pE l) (fun x => f x * ψ x)) ^ (plExp l)
      ≤ ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
          * tentNorm l A c R f := by
  have hp : 0 < plExp l := by
    rw [plExp]
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  have hpnn : 0 ≤ plExp l := hp.le
  rw [← lintegral_nnnorm_rpow_eq_lpNorm_pow l hl]
  have hpt : ∀ x : E l, (‖f x * ψ x‖₊ : ℝ≥0∞) ^ (plExp l)
      ≤ ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
          * ((‖f x‖₊ : ℝ≥0∞) ^ (plExp l) * ballTent l A c R x) := by
    intro x
    have h1 : (‖ψ x‖₊ : ℝ≥0∞) ^ (plExp l)
        ≤ (ENNReal.ofReal Cb) ^ (plExp l)
            * ENNReal.ofReal ((1 + Metric.infDist x (Metric.ball c R) / R) ^ (-A)) := by
      have h2 : ((Cb * (1 + Metric.infDist x (Metric.ball c R) / R) ^ (-(A / plExp l))) ^ (plExp l))
          = Cb ^ (plExp l) * (1 + Metric.infDist x (Metric.ball c R) / R) ^ (-A) := by
        rw [Real.mul_rpow (le_of_lt hCb)
          (Real.rpow_nonneg (add_nonneg zero_le_one
            (div_nonneg Metric.infDist_nonneg hR.le)) _)]
        congr 1
        rw [← Real.rpow_mul (add_nonneg zero_le_one
          (div_nonneg Metric.infDist_nonneg hR.le))]
        congr 1
        field_simp
      have h3 : (‖ψ x‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal
          (Cb * (1 + Metric.infDist x (Metric.ball c R) / R) ^ (-(A / plExp l))) := by
        have h4 : ((‖ψ x‖₊ : NNReal) : ℝ) ≤ Cb * (1 + Metric.infDist x (Metric.ball c R) / R) ^ (-(A / plExp l)) :=
          hψdec x
        rw [show (↑‖ψ x‖₊ : ℝ≥0∞) = ENNReal.ofReal ((‖ψ x‖₊ : NNReal) : ℝ) from
          ENNReal.ofReal_coe_nnreal.symm]
        exact ENNReal.ofReal_le_ofReal h4
      calc (‖ψ x‖₊ : ℝ≥0∞) ^ (plExp l)
          ≤ (ENNReal.ofReal (Cb * (1 + Metric.infDist x (Metric.ball c R) / R) ^ (-(A / plExp l))))
              ^ (plExp l) := ENNReal.rpow_le_rpow h3 hpnn
        _ = ENNReal.ofReal ((Cb * (1 + Metric.infDist x (Metric.ball c R) / R) ^ (-(A / plExp l)))
              ^ (plExp l)) :=
            ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCb.le
              (Real.rpow_nonneg (add_nonneg zero_le_one
                (div_nonneg Metric.infDist_nonneg hR.le)) _)) hpnn
        _ = ENNReal.ofReal (Cb ^ (plExp l)
              * (1 + Metric.infDist x (Metric.ball c R) / R) ^ (-A)) := by rw [h2]
        _ = ENNReal.ofReal (Cb ^ (plExp l))
              * ENNReal.ofReal ((1 + Metric.infDist x (Metric.ball c R) / R) ^ (-A)) :=
            ENNReal.ofReal_mul (Real.rpow_nonneg hCb.le (plExp l))
        _ = (ENNReal.ofReal Cb) ^ (plExp l)
              * ENNReal.ofReal ((1 + Metric.infDist x (Metric.ball c R) / R) ^ (-A)) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hCb.le hpnn]
    calc (‖f x * ψ x‖₊ : ℝ≥0∞) ^ (plExp l)
        = (‖f x‖₊ : ℝ≥0∞) ^ (plExp l) * (‖ψ x‖₊ : ℝ≥0∞) ^ (plExp l) := by
          rw [nnnorm_mul, ENNReal.coe_mul, ENNReal.mul_rpow_of_nonneg _ _ hpnn]
      _ ≤ (‖f x‖₊ : ℝ≥0∞) ^ (plExp l)
            * ((ENNReal.ofReal Cb) ^ (plExp l)
              * ENNReal.ofReal ((1 + Metric.infDist x (Metric.ball c R) / R) ^ (-A))) :=
          mul_le_mul' le_rfl h1
      _ = ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
            * ((‖f x‖₊ : ℝ≥0∞) ^ (plExp l) * ballTent l A c R x) := by
          rw [← ofReal_volume_mul_ballTent l A c hR x]
          ring
  refine (lintegral_mono hpt).trans ?_
  rw [show (∫⁻ x, ((ENNReal.ofReal Cb) ^ (plExp l)
          * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
        * ((‖f x‖₊ : ℝ≥0∞) ^ (plExp l) * ballTent l A c R x))
      = ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
        * tentNorm l A c R f from by
    rw [tentNorm]
    have hKtop : (ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal ≠ ⊤ :=
      ENNReal.mul_ne_top (by
        rw [ENNReal.ofReal_rpow_of_nonneg hCb.le hpnn]
        exact ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    exact lintegral_const_mul' _ _ hKtop]

theorem curveDecLoc_of_curveDec {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l) {m : ℕ} (hm : 1 ≤ m)
    {lam lam' ρ A : ℝ} (hlam : 1 ≤ lam) (hρ : 0 < ρ)
    (hρl : (2 : ℝ) ^ (l + 2) ≤ ρ * lam ^ l)
    (hrad : ∀ j : Fin m, Metric.ball (D 0 (pieceCenter m j)) (ρ * (lam / (2 * m)) ^ l)
              ⊆ curvePlate l D (lam / (2 * m)) (pieceCenter m j))
    (hA : 0 ≤ A) {C : ℝ≥0∞} (hdec : CurveDec l D m lam' C) (hlam' : 2 * lam ≤ lam') :
    ∃ K : ℝ≥0∞, CurveDecLoc l D m lam A (C * K) := by
  have hp : 0 < plExp l := by
    rw [plExp]
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  have hpnn : 0 ≤ plExp l := hp.le
  have hpA : 0 ≤ A / plExp l := div_nonneg hA hpnn
  obtain ⟨Cb, hCb, hbump0⟩ :=
    Commons.Analysis.Fourier.exists_ball_bump_uniform l hl (A / plExp l) hpA
  refine ⟨ENNReal.ofReal (2 * Cb), ?_⟩
  intro f hf c R hR
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hR1 : (1 : ℝ) ≤ R := le_trans (one_le_pow₀ hm1) hR
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  obtain ⟨σ, ψ₀, Φ, hσpos, hσR, hΦmeas, hΦint, hΦsupp, hrep, hlow, hdecay⟩ := hbump0 R hR1
  obtain ⟨ψ, hψclass, hψlow, hψdec⟩ :=
    ball_bump_translate (c := c) hR1 hpA hCb.le hσpos hΦmeas hΦint hΦsupp hrep hlow hdecay
  set g : E l → ℂ := fun x => ∑ j, f j x with hg
  set h : E l → ℂ := fun x => ∑ j, f j x * ψ x with hh
  have hgh : ∀ x, h x = g x * ψ x := by
    intro x
    simp only [hh, hg, Finset.sum_mul]
  -- classes of the multiplied pieces
  have hclass : ∀ j : Fin m, IsFourierRep l (curvePlate l D (lam' / (2 * m)) (pieceCenter m j))
      (fun x => f j x * ψ x) := fun j =>
    isFourierRep_mul_ball_bump hl D hm hlam hρ hρl hrad hlam' (j := j) hσR hR hψclass (hf j)
  -- the decoupling inequality
  have hdec' : lpNorm l (pE l) h
      ≤ C * l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x)) := by
    have h1 := hdec (fun j => fun x => f j x * ψ x) hclass
    simpa only [hh] using h1
  have hdec2 : (lpNorm l (pE l) h) ^ (plExp l)
      ≤ C ^ (plExp l)
        * (l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x))) ^ (plExp l) := by
    refine (ENNReal.rpow_le_rpow hdec' hpnn).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpnn]
  -- the localising step
  have hpoint : ∀ x ∈ Metric.ball c R,
      (‖g x‖₊ : ℝ≥0∞) ^ (plExp l) ≤ 2 ^ (plExp l) * (‖h x‖₊ : ℝ≥0∞) ^ (plExp l) := by
    intro x hx
    have hx' : ‖x - c‖ ≤ R := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      exact hx.le
    have hψ1 : (1 / 2 : ℝ) ≤ ‖ψ x‖ := hψlow x hx'
    have h1 : ‖g x‖ ≤ 2 * ‖h x‖ := by
      have h2 : ‖h x‖ = ‖g x‖ * ‖ψ x‖ := by rw [hgh x, norm_mul]
      have h3 : ‖g x‖ * (1 / 2 : ℝ) ≤ ‖g x‖ * ‖ψ x‖ :=
        mul_le_mul_of_nonneg_left hψ1 (norm_nonneg _)
      nlinarith [norm_nonneg (g x), norm_nonneg (h x)]
    have h2 : (‖g x‖₊ : ℝ≥0∞) ≤ 2 * (‖h x‖₊ : ℝ≥0∞) := by
      have h3 : (‖g x‖₊ : NNReal) ≤ (2 : NNReal) * ‖h x‖₊ := by
        exact_mod_cast h1
      calc (‖g x‖₊ : ℝ≥0∞) = ((‖g x‖₊ : NNReal) : ℝ≥0∞) := rfl
        _ ≤ (((2 : NNReal) * ‖h x‖₊ : NNReal) : ℝ≥0∞) := by exact_mod_cast h3
        _ = 2 * (‖h x‖₊ : ℝ≥0∞) := by rw [ENNReal.coe_mul]; norm_num
    calc (‖g x‖₊ : ℝ≥0∞) ^ (plExp l) ≤ (2 * (‖h x‖₊ : ℝ≥0∞)) ^ (plExp l) :=
          ENNReal.rpow_le_rpow h2 hpnn
      _ = 2 ^ (plExp l) * (‖h x‖₊ : ℝ≥0∞) ^ (plExp l) :=
          ENNReal.mul_rpow_of_nonneg _ _ hpnn
  have hlocal := ballAvg_le_of_two_mul (p := plExp l) hpoint
  have hlp := lintegral_nnnorm_rpow_eq_lpNorm_pow l hl h
  -- the per-piece bound
  have hj : ∀ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (plExp l)
      ≤ ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
          * tentNorm l A c R (f j) := fun j =>
    lpNorm_mul_le_of_decay hl hCb hRpos (fun x => hψdec x) (f := f j)
  -- assembling
  have hsum2 : (∑ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ))
      ≤ (((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
          ^ (2 / plExp l)) * ∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ)
        = ((lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (plExp l)) ^ (2 / plExp l) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          field_simp
      _ ≤ (((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
            * tentNorm l A c R (f j)) ^ (2 / plExp l) :=
          ENNReal.rpow_le_rpow (hj j) (by positivity)
      _ = ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
            ^ (2 / plExp l) * (tentNorm l A c R (f j)) ^ (2 / plExp l) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
  have hl2 : (l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x))) ^ (plExp l)
      = (∑ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ))
          ^ (plExp l / 2) := by
    rw [l2Norm, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hKpow : (((ENNReal.ofReal Cb) ^ (plExp l)
        * ENNReal.ofReal (volume (Metric.ball c R)).toReal) ^ (2 / plExp l))
      ^ (plExp l / 2)
      = (ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal := by
    rw [← ENNReal.rpow_mul]
    rw [show (2 / plExp l) * (plExp l / 2) = 1 by field_simp]
    rw [ENNReal.rpow_one]
  have hBpos : ENNReal.ofReal (volume (Metric.ball c R)).toReal ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos (μ := volume) c hRpos).ne'
      measure_ball_lt_top.ne
  have hBtop : ENNReal.ofReal (volume (Metric.ball c R)).toReal ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel : (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
        * ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
      = (ENNReal.ofReal Cb) ^ (plExp l) := by
    rw [mul_comm ((ENNReal.ofReal Cb) ^ (plExp l))
      (ENNReal.ofReal (volume (Metric.ball c R)).toReal),
      ← mul_assoc, ENNReal.inv_mul_cancel hBpos hBtop, one_mul]
  have hconst : 2 ^ (plExp l) * ((ENNReal.ofReal Cb) ^ (plExp l) * C ^ (plExp l))
      ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l) := by
    have h1 : (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l)
        = C ^ (plExp l) * (ENNReal.ofReal (2 * Cb)) ^ (plExp l) :=
      ENNReal.mul_rpow_of_nonneg _ _ hpnn
    have h2 : (ENNReal.ofReal (2 * Cb)) ^ (plExp l)
        = (ENNReal.ofReal 2) ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.mul_rpow_of_nonneg _ _ hpnn]
    have h3 : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by norm_num
    rw [h1, h2, h3]
    exact le_of_eq (by ac_rfl)
  calc ballAvg (plExp l) c R g
      ≤ (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * ∫⁻ x, (‖h x‖₊ : ℝ≥0∞) ^ (plExp l)) := hlocal
    _ = (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (lpNorm l (pE l) h) ^ (plExp l)) := by rw [hlp]
    _ ≤ (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * (l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x))) ^ (plExp l))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hdec2)
    _ = (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * (∑ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ))
              ^ (plExp l / 2))) := by rw [hl2]
    _ ≤ (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * ((((ENNReal.ofReal Cb) ^ (plExp l)
                * ENNReal.ofReal (volume (Metric.ball c R)).toReal) ^ (2 / plExp l)
                * ∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl
          (ENNReal.rpow_le_rpow hsum2 (by positivity))))
    _ = (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)))) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hKpow]
    _ = 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)
          * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)) := by
        have hc := hcancel
        calc (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
              * (2 ^ (plExp l) * (C ^ (plExp l)
                * ((ENNReal.ofReal Cb) ^ (plExp l)
                  * ENNReal.ofReal (volume (Metric.ball c R)).toReal
                  * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))))
            = 2 ^ (plExp l) * (C ^ (plExp l)
                * (((ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
                    * ((ENNReal.ofReal Cb) ^ (plExp l)
                      * ENNReal.ofReal (volume (Metric.ball c R)).toReal))
                  * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))) := by
                ring
          _ = 2 ^ (plExp l) * (C ^ (plExp l) * ((ENNReal.ofReal Cb) ^ (plExp l)
                * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))) := by
                rw [hc]
          _ = 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)
                * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)) := by
                ring
    _ ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l)
          * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2) := by
        have h1 : 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l))
            ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l) := by
          have := hconst
          rwa [show 2 ^ (plExp l) * ((ENNReal.ofReal Cb) ^ (plExp l) * C ^ (plExp l))
              = 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)) from by ring] at this
        calc 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))
            = (2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)))
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2) := by ring
          _ ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l)
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2) :=
              mul_le_mul' h1 le_rfl


end Submission.Vinogradov
