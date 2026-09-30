/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.TentCompare
import Submission.Vinogradov.LowerDegree
import Submission.Commons.Measure.Integral.lintegral_ell2_minkowski_rpow
import Submission.Commons.Measure.Integral.ballTent_growth_lintegral_le_C0


/-!
# GLYZ Lemma 3.8 (lower degree decoupling): the assembly

This module assembles `AsymDecFine` (GLYZ arXiv:1912.09798 (3.10) / Lemma 3.8) from the pieces
available in `Corollary 3.7` (`LocalisedDecoupling.curveDecLoc_of_curveDec`), the uncertainty
principle, and the tent comparisons of `TentCompare.lean`.

The chain (see `ROADMAP.lean`, session 52) is, with `M := refLvl l k m'`, `ξ' := c_{I'}`,
`Ψ := projEmbedLin k l (torsionVec k l hlk ξ')`, `r := hBallR k l m'`, `B := ball 0 r`:

1. moving ball: `asymLHS = |B|⁻¹ ∫_z ∫_{w∈B} C1(z+Ψw)C2(z+Ψw)`;
2. sup comparison on the `I'`-factor (`TentCompare.convPow_platePhi_shift_le`, used at `w` and
   at `-w`): `≤ |B|⁻¹ C_sup ∫_z C2 z (∫_{w∈B} C1(z+Ψw))`;
3. convolution swap (`LowerDegree.lintegral_ball_convPow_swap`):
   `∫_{w∈B} C1(z+Ψw) = ∫_t Φ_I t · (∫_{w∈B} ‖f_I((z-t)+Ψw)‖^{p_l})`;
4. Corollary 3.7 on the reparametrised curve of the block `q`
   (`CurveLayer.intervalCurve`, `CurveDecLoc`), giving the `ℓ²`-sum of the ball-tent norms;
5. fusion of the `(z,t)` integral (reflection in `t` + Tonelli);
6. weighted Minkowski (`lintegral_ell2_minkowski_rpow_weighted`);
7. removal of the `H`-ball average (`lintegral_ballTent_shift_le` below): the shift lands on `C2`,
   which *is* comparable on the `H`-ball;
8. the tent comparison `|G_J|^{p_l} ∗ Φ_I ≲ |G_J|^{p_l} ∗ Φ_J`
   (`TentCompare.convPow_platePhi_le_of_plate`) and `AsymRefine.asymDec_of_fine`.

This module currently contains steps 6 and 7 in their abstract form.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. Weighted Minkowski -/

/-- **Minkowski's `L^{p_l}ℓ² ≤ ℓ²L^{p_l}` inequality in the weighted form used by Lemma 3.8.**
This is the commons `Commons.Measure.Integral.lintegral_ell2_minkowski_rpow` applied to the
measure `μ.withDensity W`. -/
theorem lintegral_ell2_minkowski_rpow_weighted {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {W : α → ℝ≥0∞} (hW : AEMeasurable W μ)
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 2 ≤ p) (f : ι → α → ℝ≥0∞)
    (hf : ∀ i, AEMeasurable (f i) μ) :
    (∫⁻ x, W x * (∑ i, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂μ) ^ (1 / p)
      ≤ (∑ i, (∫⁻ x, W x * (f i x) ^ p ∂μ) ^ (2 / p)) ^ ((1 : ℝ) / 2) := by
  have hcore := Commons.Measure.Integral.lintegral_ell2_minkowski_rpow (μ.withDensity W) hp f
    (fun i => by
      obtain ⟨g, hg, hfg⟩ := hf i
      exact ⟨g, hg, (withDensity_absolutelyContinuous μ W).ae_eq hfg⟩)
  have hm : AEMeasurable (fun x => (∑ i, (f i x) ^ (2 : ℝ)) ^ (p / 2)) μ := by
    have h1 : AEMeasurable (fun x => ∑ i, (f i x) ^ (2 : ℝ)) μ := by
      have h := Finset.aemeasurable_sum Finset.univ (fun i _ => (hf i).pow_const (2 : ℝ))
      rwa [Finset.sum_fn] at h
    exact h1.pow_const _
  have h1 : (∫⁻ x, (∑ i, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂(μ.withDensity W))
      = ∫⁻ x, W x * (∑ i, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂μ :=
    lintegral_withDensity_eq_lintegral_mul₀ hW hm
  have h2 : ∀ i, (∫⁻ x, (f i x) ^ p ∂(μ.withDensity W)) = ∫⁻ x, W x * (f i x) ^ p ∂μ :=
    fun i => lintegral_withDensity_eq_lintegral_mul₀ hW ((hf i).pow_const p)
  rw [h1, Finset.sum_congr rfl (fun i _ => by rw [h2 i])] at hcore
  exact hcore

/-! ## 2. The mass of the ball tent -/

/-- **The mass of the `L¹`-normalised ball tent is bounded independently of the radius**
(provided the tent exponent exceeds `2 l`, which is the form in which the commons convolution
estimate `Commons.Analysis.Convolution.ball_tent_lintegral_le` supplies it). -/
theorem exists_ballTent_lintegral_le {l : ℕ} (hl : 1 ≤ l) {A' : ℝ} (hA' : (2 : ℝ) * l < A') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      (∫⁻ w : E l, ballTent l A' 0 R w) ≤ ENNReal.ofReal C := by
  haveI : Inhabited (Fin l) := ⟨⟨0, hl⟩⟩
  haveI : Nontrivial (Fin l → ℝ) := Pi.nontrivial
  haveI : Nontrivial (E l) := inferInstance
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  have hA0 : (0 : ℝ) < A' / 2 := by linarith
  have hfr : A' / 2 + (Module.finrank ℝ (E l) : ℝ) < A' := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
    linarith
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.Analysis.Convolution.ball_tent_lintegral_le (E := E l) (A' / 2) A' hA0 hfr 1 le_rfl
  refine ⟨C, hCpos.le, fun R hR => ?_⟩
  have h := hC R 0 hR le_rfl
  have hmax : ∀ w : E l, max 1 ((0 : ℝ) - 1 * ‖w‖ / R) = 1 := by
    intro w
    have h2 : (0 : ℝ) ≤ ‖w‖ / R := by positivity
    rw [one_mul, show (0 : ℝ) - ‖w‖ / R = -(‖w‖ / R) from by ring]
    exact max_eq_left (by linarith)
  have hrhs : ENNReal.ofReal ((max 1 (0 : ℝ)) ^ (-(A' / 2))) = 1 := by
    rw [max_eq_left zero_le_one, Real.one_rpow, ENNReal.ofReal_one]
  have heq : (∫⁻ w : E l, ballTent l A' 0 R w)
      = ∫⁻ w : E l, ENNReal.ofReal (((volume (Metric.ball (0 : E l) R)).toReal)⁻¹
          * (1 + Metric.infDist w (Metric.ball (0 : E l) R) / R) ^ (-A')
          * (max 1 ((0 : ℝ) - 1 * ‖w‖ / R)) ^ (-(A' / 2))) := by
    refine lintegral_congr fun w => ?_
    rw [ballTent_eq_ofReal l A' 0 hR w, hmax w, Real.one_rpow, mul_one]
  rw [hrhs, mul_one] at h
  rw [heq]
  exact h

lemma measurable_ballTent (l : ℕ) (A : ℝ) (c : E l) (R : ℝ) : Measurable (ballTent l A c R) := by
  unfold ballTent
  measurability

/-! ## 3. Removal of the `H`-ball average (step 7 of the plan) -/

/-- **The canonical tent of a plate is comparable under arbitrary shifts**, at the price of the
growth factor `(1 + ρ)^{gaugeExp k}`; this is the reverse of `platePhi_shift_le_of_gauge`. -/
lemma platePhi_shift_ge_of_gauge {k : ℕ} (hk : 1 ≤ k) (δ c : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {x h : E k} (hh : gauge k hk (plateGaugeLin k δ c h) ≤ ρ) :
    platePhi k hk δ c x
      ≤ ENNReal.ofReal ((1 + ρ) ^ gaugeExp k) * platePhi k hk δ c (x + h) := by
  have h1 : platePhi k hk δ c x
      = ENNReal.ofReal (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x) := rfl
  have h2 : platePhi k hk δ c (x + h)
      = ENNReal.ofReal (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) (x + h)) := rfl
  rw [h1, h2]
  have hApos : (0:ℝ) < gaugeExp k := lt_of_le_of_lt (by positivity) (gaugeExp_gt hk)
  have hle := phiPlate_shift_ge k hk δ c (gaugeExp k) (gaugeAmp k hk) hApos hρ
    (gaugeAmp_pos k hk).le (x := x) (h := h) hh
  calc ENNReal.ofReal (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x)
      ≤ ENNReal.ofReal ((1 + ρ) ^ gaugeExp k
          * phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) (x + h)) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal ((1 + ρ) ^ gaugeExp k)
          * ENNReal.ofReal (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) (x + h)) :=
        ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)

/-- **The `H`-ball average can be removed.**  Let `W t = ∫⁻ z, C2 z · ΦI (z − t)` be the
`(z,t)`-fused weight of Lemma 3.8 and suppose that `C2` grows at most like
`(1 + C₀ ‖w‖/r)^{A}` under the shifts by the `H`-ball of radius `r`:
`C2 (z − Ψ w) ≤ (1 + C₀ ‖w‖/r)^A · C2 z`.  Then averaging a function against the
`L¹`-normalised ball tent of that ball costs only the weighted mass of the tent:

  `∫⁻ t, W t · (Φ_{B_H} ∗_H H)(t) ≤ C · ∫⁻ t, W t · H t`.

The growth is compensated exactly because the tent exponent `A'` is *larger* than the plate
exponent `A` (`hgrowth`); this is the formal counterpart of the paper's choice
`A₁ = A + k - 2` (see `Measure/Integral/ballTent_growth_lintegral_le` in the commons).
The shift `z ↦ z − Ψ w` lands on `C2`, which alone is comparable on the `H`-ball; the level-`m`
plate inside `W` never is. -/
theorem lintegral_ballTent_shift_le {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) {A A' C₀ Cg : ℝ} (hA : 0 < A)
    (hC₀ : 0 ≤ C₀) (hCg : 0 ≤ Cg)
    (hgrowth : ∀ r : ℝ, 0 < r →
      (∫⁻ w : E l, ballTent l A' 0 r w * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A))
        ≤ ENNReal.ofReal Cg) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (C2 ΦI H : E k → ℝ≥0∞), Measurable C2 → Measurable ΦI →
      Measurable H → ∀ (r : ℝ), 0 < r →
      (∀ (z : E k) (w : E l), C2 (z - projEmbedLin k l (torsionVec k l hlk ξ') w)
          ≤ ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * C2 z) →
      (∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t))
          * (∫⁻ w : E l, ballTent l A' 0 r w
              * H (t + projEmbedLin k l (torsionVec k l hlk ξ') w)))
        ≤ ENNReal.ofReal C * ∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t)) * H t := by
  refine ⟨Cg, hCg, ?_⟩
  intro C2 ΦI H hC2 hΦI hH r hr hshift
  set P : E l →ₗ[ℝ] E k := projEmbedLin k l (torsionVec k l hlk ξ') with hP
  set W : E k → ℝ≥0∞ := fun t => ∫⁻ z : E k, C2 z * ΦI (z - t) with hW
  have hWmeas : Measurable W := by
    rw [hW]
    refine Measurable.lintegral_prod_right (ν := (volume : Measure (E k))) ?_
    show Measurable (fun p : E k × E k => C2 p.2 * ΦI (p.2 - p.1))
    exact (hC2.comp measurable_snd).mul (hΦI.comp (measurable_snd.sub measurable_fst))
  have hPmeas : Measurable P := P.continuous_of_finiteDimensional.measurable
  -- (1) the weighted shift bound on `W`
  have hWshift : ∀ (t : E k) (w : E l),
      W (t - P w) ≤ ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * W t := by
    intro t w
    have key : W (t - P w) = ∫⁻ z : E k, C2 (z - P w) * ΦI (z - t) := by
      rw [hW]
      have h2 : (∫⁻ z : E k, (fun z : E k => C2 (z - P w) * ΦI (z - t)) (z + P w))
          = ∫⁻ z : E k, (fun z : E k => C2 (z - P w) * ΦI (z - t)) z :=
        lintegral_add_right_eq_self (fun z : E k => C2 (z - P w) * ΦI (z - t)) (P w)
      rw [← h2]
      refine lintegral_congr fun z => ?_
      show C2 z * ΦI (z - (t - P w)) = C2 (z + P w - P w) * ΦI (z + P w - t)
      rw [show z + P w - P w = z from by abel,
        show z + P w - t = z - (t - P w) from by abel]
    calc W (t - P w) = ∫⁻ z : E k, C2 (z - P w) * ΦI (z - t) := key
      _ ≤ ∫⁻ z : E k, (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * C2 z) * ΦI (z - t) :=
          lintegral_mono fun z => mul_le_mul' (hshift z w) le_rfl
      _ = ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * W t := by
          rw [hW]
          rw [show (fun z : E k => (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * C2 z) * ΦI (z - t))
              = fun z : E k => ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A)
                * (C2 z * ΦI (z - t)) from by funext z; ring]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- (2) pull `W t` inside, Tonelli, substitute `t ↦ t - Ψw`
  have hstep1 : (∫⁻ t : E k, W t * (∫⁻ w : E l, ballTent l A' 0 r w * H (t + P w)))
      = ∫⁻ t : E k, ∫⁻ w : E l, W t * ballTent l A' 0 r w * H (t + P w) := by
    refine lintegral_congr fun t => ?_
    rw [show (fun w : E l => W t * ballTent l A' 0 r w * H (t + P w))
        = fun w : E l => W t * (ballTent l A' 0 r w * H (t + P w)) from by funext w; ring]
    exact (lintegral_const_mul (W t) ((measurable_ballTent l A' 0 r).mul
      (hH.comp (measurable_const.add (hPmeas.comp measurable_id))))).symm
  have hstep2 : (∫⁻ t : E k, ∫⁻ w : E l, W t * ballTent l A' 0 r w * H (t + P w))
      = ∫⁻ w : E l, ∫⁻ t : E k, W t * ballTent l A' 0 r w * H (t + P w) := by
    refine lintegral_lintegral_swap ?_
    have h1 : Measurable (fun p : E k × E l =>
        W p.1 * ballTent l A' 0 r p.2 * H (p.1 + P p.2)) :=
      ((hWmeas.comp measurable_fst).mul ((measurable_ballTent l A' 0 r).comp measurable_snd)).mul
        (hH.comp (measurable_fst.add (hPmeas.comp measurable_snd)))
    exact h1.aemeasurable
  have hstep3 : ∀ w : E l,
      (∫⁻ t : E k, W t * ballTent l A' 0 r w * H (t + P w))
        = ballTent l A' 0 r w * ∫⁻ t : E k, W (t - P w) * H t := by
    intro w
    have h1 : (∫⁻ t : E k, W t * ballTent l A' 0 r w * H (t + P w))
        = ∫⁻ t : E k, ballTent l A' 0 r w * (W t * H (t + P w)) := by
      refine lintegral_congr fun t => ?_
      rw [show W t * ballTent l A' 0 r w * H (t + P w)
          = ballTent l A' 0 r w * (W t * H (t + P w)) from by ring]
    have hmeas : Measurable (fun a : E k => W a * H (a + P w)) :=
      hWmeas.mul (hH.comp (measurable_id.add measurable_const))
    have h2 : (∫⁻ t : E k, ballTent l A' 0 r w * (W t * H (t + P w)))
        = ballTent l A' 0 r w * ∫⁻ t : E k, W t * H (t + P w) :=
      lintegral_const_mul (ballTent l A' 0 r w) hmeas
    rw [h1, h2]
    congr 1
    have h3 : (∫⁻ t : E k, (fun t : E k => W (t - P w) * H t) (t + P w))
        = ∫⁻ t : E k, (fun t : E k => W (t - P w) * H t) t :=
      lintegral_add_right_eq_self (fun t : E k => W (t - P w) * H t) (P w)
    rw [← h3]
    refine lintegral_congr fun t => ?_
    show W t * H (t + P w) = W (t + P w - P w) * H (t + P w)
    rw [add_sub_cancel_right]
  -- (3) the weighted shift bound plus the growth hypothesis
  have hstep4 : (∫⁻ w : E l, ballTent l A' 0 r w * ∫⁻ t : E k, W (t - P w) * H t)
      ≤ ∫⁻ w : E l, ballTent l A' 0 r w
          * (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * ∫⁻ t : E k, W t * H t) := by
    refine lintegral_mono fun w => mul_le_mul' le_rfl ?_
    have h2 : (∫⁻ t : E k, W (t - P w) * H t)
        ≤ ∫⁻ t : E k, (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * W t) * H t :=
      lintegral_mono fun t => mul_le_mul' (hWshift t w) le_rfl
    have h3 : (∫⁻ t : E k, (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * W t) * H t)
        = ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * ∫⁻ t : E k, W t * H t := by
      rw [show (fun t : E k => (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * W t) * H t)
          = fun t : E k => ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * (W t * H t) from by
        funext t; ring]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    exact h2.trans (le_of_eq h3)
  have hstep5 : (∫⁻ w : E l, ballTent l A' 0 r w
        * (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * ∫⁻ t : E k, W t * H t))
      ≤ ENNReal.ofReal Cg * ∫⁻ t : E k, W t * H t := by
    rw [show (fun w : E l => ballTent l A' 0 r w
          * (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * ∫⁻ t : E k, W t * H t))
        = fun w : E l => (ballTent l A' 0 r w
          * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A)) * ∫⁻ t : E k, W t * H t from by
      funext w; ring]
    have hmeas : Measurable (fun w : E l => ballTent l A' 0 r w
        * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A)) :=
      (measurable_ballTent l A' 0 r).mul (by measurability)
    have h2 : (∫⁻ w : E l, (ballTent l A' 0 r w
          * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A)) * ∫⁻ t : E k, W t * H t)
        = (∫⁻ w : E l, ballTent l A' 0 r w
            * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A)) * ∫⁻ t : E k, W t * H t :=
      lintegral_mul_const _ hmeas
    rw [h2]
    exact mul_le_mul' (hgrowth r hr) le_rfl
  rw [hstep1, hstep2]
  refine le_trans (le_of_eq (lintegral_congr fun w => hstep3 w)) ?_
  exact le_trans hstep4 hstep5

/-! ## 4. The rearrangements of the `(z,t)` double integral -/

/-- Reflection in the second variable:  `∫⁻ t, B t · F (z − t) = ∫⁻ t, B (z − t) · F t`. -/
lemma lintegral_sub_left_refl {k : ℕ} (B F : E k → ℝ≥0∞) (z : E k) :
    (∫⁻ t, B t * F (z - t)) = ∫⁻ t, B (z - t) * F t := by
  rw [← MeasureTheory.lintegral_sub_left_eq_self (fun t : E k => B t * F (z - t)) z]
  refine lintegral_congr fun t => ?_
  show B (z - t) * F (z - (z - t)) = B (z - t) * F t
  rw [show z - (z - t) = t from by abel]

/-- **Reflection in the second variable followed by Tonelli:**

  `∫⁻ z, A z · (∫⁻ t, B t · F (z − t)) = ∫⁻ t, (∫⁻ z, A z · B (z − t)) · F t`.

This is the fusion of the `(z,t)`-double integral of Lemma 3.8 into the weight `W` of step 7. -/
theorem lintegral_swap_refl {k : ℕ} {A B F : E k → ℝ≥0∞} (hA : Measurable A)
    (hB : Measurable B) (hF : Measurable F) :
    (∫⁻ z, A z * (∫⁻ t, B t * F (z - t)))
      = ∫⁻ t, (∫⁻ z, A z * B (z - t)) * F t := by
  have h1 : (∫⁻ z, A z * (∫⁻ t, B t * F (z - t)))
      = ∫⁻ z, A z * (∫⁻ t, B (z - t) * F t) := by
    refine lintegral_congr fun z => ?_
    rw [lintegral_sub_left_refl B F z]
  rw [h1]
  have h2 : (∫⁻ z, A z * (∫⁻ t, B (z - t) * F t))
      = ∫⁻ z, ∫⁻ t, A z * (B (z - t) * F t) := by
    refine lintegral_congr fun z => ?_
    have hmeas : Measurable (fun t : E k => B (z - t) * F t) := by fun_prop
    exact (lintegral_const_mul (A z) hmeas).symm
  rw [h2]
  have h3 : (∫⁻ z, ∫⁻ t, A z * (B (z - t) * F t))
      = ∫⁻ t, ∫⁻ z, A z * (B (z - t) * F t) := by
    refine lintegral_lintegral_swap ?_
    have h : Measurable (fun p : E k × E k => A p.1 * (B (p.1 - p.2) * F p.2)) :=
      (hA.comp measurable_fst).mul (((hB.comp (measurable_fst.sub measurable_snd)).mul
        (hF.comp measurable_snd)))
    exact h.aemeasurable
  rw [h3]
  refine lintegral_congr fun t => ?_
  rw [show (fun z : E k => A z * (B (z - t) * F t))
      = fun z : E k => (A z * B (z - t)) * F t from by funext z; ring]
  have hmeas : Measurable (fun z : E k => A z * B (z - t)) := by fun_prop
  exact lintegral_mul_const (F t) hmeas

/-- **The final identification:** the `(z,t)`-fused weight of Lemma 3.8 against the `r`-th power
of a function is the `z`-integral of `C2` against the convolved power. -/
theorem lintegral_W_mul_eq {k : ℕ} (C2 : E k → ℝ≥0∞) (G : E k → ℂ) (ΦI : E k → ℝ≥0∞)
    (hC2 : Measurable C2) (hG : Measurable G) (hΦI : Measurable ΦI) (r : ℝ) :
    (∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t)) * (((‖G t‖₊ : ℝ≥0∞) ^ r)))
      = ∫⁻ z : E k, C2 z * convPow k r G ΦI z := by
  have hH : Measurable (fun t : E k => ((‖G t‖₊ : ℝ≥0∞) ^ r)) :=
    (hG.nnnorm.coe_nnreal_ennreal).pow_const r
  have h1 : (∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t)) * (((‖G t‖₊ : ℝ≥0∞) ^ r)))
      = ∫⁻ t : E k, ∫⁻ z : E k, (C2 z * ΦI (z - t)) * (((‖G t‖₊ : ℝ≥0∞) ^ r)) := by
    refine lintegral_congr fun t => ?_
    have hmeas : Measurable (fun z : E k => C2 z * ΦI (z - t)) := by fun_prop
    exact (lintegral_mul_const (((‖G t‖₊ : ℝ≥0∞) ^ r)) hmeas).symm
  rw [h1]
  have h2 : (∫⁻ t : E k, ∫⁻ z : E k, (C2 z * ΦI (z - t)) * (((‖G t‖₊ : ℝ≥0∞) ^ r)))
      = ∫⁻ z : E k, ∫⁻ t : E k, (C2 z * ΦI (z - t)) * (((‖G t‖₊ : ℝ≥0∞) ^ r)) := by
    refine lintegral_lintegral_swap ?_
    have h : Measurable (fun p : E k × E k =>
        (C2 p.2 * ΦI (p.2 - p.1)) * (((‖G p.1‖₊ : ℝ≥0∞) ^ r))) :=
      ((hC2.comp measurable_snd).mul (hΦI.comp (measurable_snd.sub measurable_fst))).mul
        ((hG.comp measurable_fst).nnnorm.coe_nnreal_ennreal |>.pow_const r)
    exact h.aemeasurable
  rw [h2]
  refine lintegral_congr fun z => ?_
  rw [show (fun t : E k => (C2 z * ΦI (z - t)) * (((‖G t‖₊ : ℝ≥0∞) ^ r)))
      = fun t : E k => C2 z * (ΦI (z - t) * (((‖G t‖₊ : ℝ≥0∞) ^ r))) from by funext t; ring]
  have hmeas : Measurable (fun t : E k => ΦI (z - t) * (((‖G t‖₊ : ℝ≥0∞) ^ r))) := by fun_prop
  rw [lintegral_const_mul (C2 z) hmeas]
  congr 1
  rw [convPow_eq_lintegral_sub]
  exact lintegral_congr fun t => mul_comm _ _

/-! ## 3b. The `H`-ball removal with the growth hypothesis discharged -/

/-- **The `H`-ball average can be removed (unconditional form)**: the growth hypothesis of
`lintegral_ballTent_shift_le` is discharged by the commons
`Commons.Measure.Integral.ballTent_growth_lintegral_le_C0` whenever the tent exponent `A'`
exceeds the plate exponent `A` by more than the dimension `l` (cf. GLYZ's `A₁ = A + k − 2`). -/
theorem lintegral_ballTent_shift_le' {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) {A A' C₀ : ℝ} (hA : 0 < A) (hC₀ : 0 ≤ C₀)
    (hA' : A + (l : ℝ) < A') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (C2 ΦI H : E k → ℝ≥0∞), Measurable C2 → Measurable ΦI →
      Measurable H → ∀ (r : ℝ), 0 < r →
      (∀ (z : E k) (w : E l), C2 (z - projEmbedLin k l (torsionVec k l hlk ξ') w)
          ≤ ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * C2 z) →
      (∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t))
          * (∫⁻ w : E l, ballTent l A' 0 r w
              * H (t + projEmbedLin k l (torsionVec k l hlk ξ') w)))
        ≤ ENNReal.ofReal C * ∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t)) * H t := by
  obtain ⟨Cg, hCg0, hCg⟩ := Commons.Measure.Integral.ballTent_growth_lintegral_le_C0
    (n := l) (A := A') (B := A) hA.le hA' C₀ hC₀
  refine lintegral_ballTent_shift_le hk hl hlk hξ' hA hC₀ hCg0 (fun r hr => ?_)
  have h1 : (∫⁻ w : E l, ballTent l A' 0 r w * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A))
      = ∫⁻ w : E l, (ENNReal.ofReal (volume (Metric.ball (0 : E l) r)).toReal)⁻¹
          * ENNReal.ofReal ((1 + Metric.infDist w (Metric.ball (0 : E l) r) / r) ^ (-A'))
          * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) := by
    refine lintegral_congr fun w => ?_
    rw [ballTent_apply]
  rw [h1]
  exact hCg r hr

end Submission.Vinogradov
