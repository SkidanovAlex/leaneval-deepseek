import Mathlib
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_q_strong_p_top
import Submission.Work.BourgainPlan.Maximal.lintegral_rpow_enorm_eq_layercake
import Submission.Work.BourgainPlan.Maximal.two_weak_truncation_bound
import Submission.Work.BourgainPlan.Maximal.key_lintegral_upper
import Submission.Work.BourgainPlan.Maximal.theta_mul_eq
import Submission.Work.BourgainPlan.Maximal.two_strong_interp_arith

open MeasureTheory Measure Filter Set
open scoped ENNReal

namespace Work.BourgainPlan.Maximal

/-- **Chebyshev–Markov.**  A strong `L^r` bound with constant `K` for an `ℝ≥0∞`-valued operator
implies the weak `(r,r)` bound with the same constant. -/
private lemma weak_of_strong
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    {T : (α → ℂ) → (β → ENNReal)}
    (hmeas : ∀ f : α → ℂ, AEMeasurable (T f) ν)
    {r K : ℝ} (hr : 0 < r) (hK : 0 < K)
    (hbd : ∀ f : α → ℂ, eLpNorm (T f) (ENNReal.ofReal r) ν
      ≤ ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal r) μ) :
    ∀ (f : α → ℂ) (lam : ℝ), 0 < lam →
      ν {x : β | ENNReal.ofReal lam < T f x}
        ≤ ENNReal.ofReal (K / lam) ^ r * (eLpNorm f (ENNReal.ofReal r) μ) ^ r := by
  intro f lam hlam
  have hcheb := mul_meas_ge_le_pow_eLpNorm' (μ := ν)
    (p := ENNReal.ofReal r) (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
    (f := T f) (ENNReal.ofReal lam)
  have hcheb' : ENNReal.ofReal lam ^ r * ν {x : β | ENNReal.ofReal lam ≤ T f x}
      ≤ (eLpNorm (T f) (ENNReal.ofReal r) ν) ^ r := by
    simpa only [ENNReal.toReal_ofReal hr.le, enorm_eq_self] using hcheb
  have hstep : ENNReal.ofReal lam ^ r * ν {x : β | ENNReal.ofReal lam < T f x}
      ≤ ENNReal.ofReal K ^ r * (eLpNorm f (ENNReal.ofReal r) μ) ^ r := by
    have hmeas_le : ν {x : β | ENNReal.ofReal lam < T f x}
        ≤ ν {x : β | ENNReal.ofReal lam ≤ T f x} := by
      apply measure_mono
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      exact le_of_lt hx
    have h1 : ENNReal.ofReal lam ^ r * ν {x : β | ENNReal.ofReal lam < T f x}
        ≤ ENNReal.ofReal lam ^ r * ν {x : β | ENNReal.ofReal lam ≤ T f x} :=
      mul_le_mul_right hmeas_le _
    refine h1.trans (hcheb'.trans ?_)
    calc (eLpNorm (T f) (ENNReal.ofReal r) ν) ^ r
        ≤ (ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal r) μ) ^ r :=
          ENNReal.rpow_le_rpow (hbd f) hr.le
      _ = ENNReal.ofReal K ^ r * (eLpNorm f (ENNReal.ofReal r) μ) ^ r :=
          ENNReal.mul_rpow_of_nonneg _ _ hr.le
  have hc0 : ENNReal.ofReal lam ^ r ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hlam) ENNReal.ofReal_ne_top).ne'
  have hctop : ENNReal.ofReal lam ^ r ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hr.le ENNReal.ofReal_ne_top).ne
  have hconst : (ENNReal.ofReal lam ^ r)⁻¹ * ENNReal.ofReal K ^ r
      = ENNReal.ofReal (K / lam) ^ r := by
    rw [ENNReal.ofReal_rpow_of_nonneg hlam.le hr.le,
      ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hlam r),
      ENNReal.ofReal_rpow_of_nonneg hK.le hr.le,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (lam ^ r)⁻¹),
      ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ K / lam) hr.le,
      show (lam ^ r)⁻¹ * K ^ r = (K / lam) ^ r from by
        rw [Real.div_rpow hK.le hlam.le r, div_eq_mul_inv, mul_comm]]
  calc ν {x : β | ENNReal.ofReal lam < T f x}
      = (ENNReal.ofReal lam ^ r)⁻¹
          * (ENNReal.ofReal lam ^ r * ν {x : β | ENNReal.ofReal lam < T f x}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ ≤ (ENNReal.ofReal lam ^ r)⁻¹
          * (ENNReal.ofReal K ^ r * (eLpNorm f (ENNReal.ofReal r) μ) ^ r) :=
        mul_le_mul_right hstep _
    _ = ((ENNReal.ofReal lam ^ r)⁻¹ * ENNReal.ofReal K ^ r)
          * (eLpNorm f (ENNReal.ofReal r) μ) ^ r := by rw [mul_assoc]
    _ = ENNReal.ofReal (K / lam) ^ r * (eLpNorm f (ENNReal.ofReal r) μ) ^ r := by rw [hconst]

/-- Pointwise `ℝ≥0∞` algebra: for `t > 0`, `0 ≤ A` and `0 ≤ q`,
`ofReal (2A/t)^q * ofReal (t^(p-1)) = ofReal ((2A)^q) * ofReal (t^(p-1-q))`. -/
private lemma key_algebra {A t p q : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q) (ht : 0 < t) :
    ENNReal.ofReal (2 * A / t) ^ q * ENNReal.ofReal (t ^ (p - 1))
      = ENNReal.ofReal ((2 * A) ^ q) * ENNReal.ofReal (t ^ (p - 1 - q)) := by
  have h2A : (0:ℝ) ≤ 2 * A := by linarith
  have h2At : (0:ℝ) ≤ 2 * A / t := div_nonneg h2A ht.le
  have ht0 : (0:ℝ) ≤ t := ht.le
  rw [ENNReal.ofReal_rpow_of_nonneg h2At hq,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg h2At q),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg h2A q)]
  congr 1
  have h1 : (2 * A / t) ^ q = (2 * A) ^ q * t ^ (-q) := by
    rw [Real.div_rpow h2A ht0 q, div_eq_mul_inv, ← Real.rpow_neg ht0 q]
  rw [h1, mul_assoc, ← Real.rpow_add ht (-q) (p - 1)]
  congr 1
  ring

/-- **Marcinkiewicz interpolation for subadditive operators, two finite strong endpoints.**  This is the tool used to pass from the `ℓ²` bound (6.24) of the major-arc model to the `ℓᵖ` bounds (6.20) in KMSZ arXiv:2606.12663 §6.3 ("interpolating (6.21) with (6.24)"), applied to the *sublinear* operator `f ↦ V^ρ_ℤ(T_N f : N ∈ D)` (the `ρ`-variation of the model family, which is subadditive and positively homogeneous but not additive, so neither Riesz–Thorin nor `marcinkiewicz_weak_q_strong_p_top` applies directly).

If `T` is subadditive and positively homogeneous, is bounded from `L^q` to `L^q` with constant `Kq` and from `L^{p₀}` to `L^{p₀}` with constant `Kp`, with `1 ≤ q < p < p₀ < ∞`, then `T` is bounded from `L^p` to `L^p` with the log-convex constant `C·Kq^θ·Kp^{1-θ}` where `1/p = θ/q + (1-θ)/p₀`.

(The corpus's sibling lemmas `marcinkiewicz_weak_q_strong_p_top` and `marcinkiewicz_weak_q_strong_p_top_explicit` handle the case of a *strong-∞* endpoint and require additivity; this statement is the two-finite-endpoint, subadditive version.  The standard proof is the Marcinkiewicz truncation argument: strong at the endpoints gives weak at the endpoints by Chebyshev, and the level-set decomposition `f = f·1_{|f|>λ} + f·1_{|f|≤λ}` with `hsub` gives the strong bound at the interpolated exponent.) -/
theorem marcinkiewicz_subadditive_two_strong
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : MeasureTheory.Measure α) [MeasureTheory.SFinite μ]
    (ν : MeasureTheory.Measure β)
    {q p₀ : ℝ} (hq : 1 ≤ q) (hqp₀ : q < p₀)
    (T : (α → ℂ) → (β → ENNReal))
    (hsub : ∀ f g : α → ℂ, ∀ y : β, T (f + g) y ≤ T f y + T g y)
    (hhom : ∀ (c : ℂ) (f : α → ℂ), T (c • f) = fun y => ‖c‖ₑ * T f y)
    (hmeas : ∀ f : α → ℂ, AEMeasurable (T f) ν)
    {Kq Kp : ℝ} (hKq : 0 < Kq) (hKp : 0 < Kp)
    (hqbd : ∀ f : α → ℂ, MeasureTheory.eLpNorm (T f) (ENNReal.ofReal q) ν
      ≤ ENNReal.ofReal Kq * MeasureTheory.eLpNorm f (ENNReal.ofReal q) μ)
    (hpbd : ∀ f : α → ℂ, MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p₀) ν
      ≤ ENNReal.ofReal Kp * MeasureTheory.eLpNorm f (ENNReal.ofReal p₀) μ)
    {p θ : ℝ} (hp : q < p) (hpp : p < p₀) (hθ : p⁻¹ = θ * q⁻¹ + (1 - θ) * p₀⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : α → ℂ, Measurable f → MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) ν
      ≤ ENNReal.ofReal (C * Kq ^ θ * Kp ^ (1 - θ))
        * MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp0 : 0 < p := by linarith
  have hp0' : 0 < p₀ := by linarith
  have hpq : 0 < p - q := by linarith
  have hpp' : 0 < p₀ - p := by linarith
  have hqp' : 0 < p₀ - q := by linarith
  have hweakq := weak_of_strong (T := T) hmeas hq0 hKq hqbd
  have hweakp := weak_of_strong (T := T) hmeas hp0' hKp hpbd
  obtain ⟨hθp, hθp'⟩ := theta_mul_eq hq hp hpp hθ
  set A : ℝ := (2 * Kq) ^ q / (p - q) with hAdef
  set B : ℝ := (2 * Kp) ^ p₀ / (p₀ - p) with hBdef
  have hA : 0 < A := by rw [hAdef]; positivity
  have hB : 0 < B := by rw [hBdef]; positivity
  set σ : ℝ := (A / B) ^ (1 / (p₀ - q)) with hσdef
  have hσ : 0 < σ := by rw [hσdef]; positivity
  set K₀ : ℝ := p * 2 ^ (p + 1) * (1 / (p - q) + 1 / (p₀ - p)) with hK₀def
  have hK₀ : 0 < K₀ := by rw [hK₀def]; positivity
  have harith : p * (A * σ ^ (-(p - q)) + B * σ ^ (p₀ - p))
      ≤ K₀ * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p) := by
    rw [hK₀def]
    exact two_strong_interp_arith (A := A) (B := B) (σ := σ) hq hp hpp hθp hθp' hKq hKp
      hAdef.symm hBdef.symm hσdef.symm
  have hAσBσ : A * σ ^ (-(p - q)) + B * σ ^ (p₀ - p)
      ≤ (K₀ / p) * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p) := by
    rw [show (K₀ / p) * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)
        = (K₀ * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)) / p by ring]
    exact (le_div_iff₀ hp0).mpr (by rw [mul_comm]; exact harith)
  refine ⟨K₀ ^ (1 / p), by positivity, ?_⟩
  intro f hf
  set M : ENNReal := ∫⁻ x, ‖f x‖ₑ ^ p ∂μ with hMdef
  set Jq : ℝ → ENNReal := fun t => ∫⁻ x, Set.indicator {x : α | σ * t < ‖f x‖}
      (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x ∂μ with hJqdef
  set Jp : ℝ → ENNReal := fun t => ∫⁻ x, Set.indicator {x : α | ‖f x‖ ≤ σ * t}
      (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x ∂μ with hJpdef
  have hTLp : (eLpNorm (T f) (ENNReal.ofReal p) ν) ^ p = ∫⁻ y, (T f y) ^ p ∂ν := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p)
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top (hmeas f).aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le]
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
    apply lintegral_congr; intro y; rw [enorm_eq_self]
  have hfLp : (eLpNorm f (ENNReal.ofReal p) μ) ^ p = M := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p)
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le]
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  have hlay : ∫⁻ y, (T f y) ^ p ∂ν
      = ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0:ℝ),
          ν {x : β | ENNReal.ofReal t < T f x} * ENNReal.ofReal (t ^ (p - 1)) :=
    lintegral_rpow_enorm_eq_layercake (ν := ν) (p := p) hp0 (hmeas f)
  have htrunc : (∫⁻ t in Set.Ioi (0:ℝ),
        ν {x : β | ENNReal.ofReal t < T f x} * ENNReal.ofReal (t ^ (p - 1)))
      ≤ ∫⁻ t in Set.Ioi (0:ℝ),
          (ENNReal.ofReal (2 * Kq / t) ^ q * Jq t
            + ENNReal.ofReal (2 * Kp / t) ^ p₀ * Jp t) * ENNReal.ofReal (t ^ (p - 1)) := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_le_mul_left
      (two_weak_truncation_bound (μ := μ) (ν := ν) T hsub hq0 hp0' hweakq hweakp f hf.aestronglyMeasurable ht hσ) _
  have hJp_mono : Monotone Jp := by
    intro s t hst
    rw [hJpdef]
    apply lintegral_mono
    intro x
    by_cases h : ‖f x‖ ≤ σ * s
    · rw [Set.indicator_of_mem (show x ∈ {x : α | ‖f x‖ ≤ σ * s} from h),
          Set.indicator_of_mem (show x ∈ {x : α | ‖f x‖ ≤ σ * t} from
            le_trans h (mul_le_mul_of_nonneg_left hst hσ.le))]
    · rw [Set.indicator_of_notMem (show x ∉ {x : α | ‖f x‖ ≤ σ * s} from h)]
      exact bot_le
  have hJp_meas : Measurable Jp := hJp_mono.measurable
  have hΨp_aem : AEMeasurable
      (fun t : ℝ => ENNReal.ofReal (2 * Kp / t) ^ p₀ * Jp t * ENNReal.ofReal (t ^ (p - 1)))
      (volume.restrict (Set.Ioi 0)) :=
    (((ENNReal.continuous_rpow_const (y := p₀)).measurable.comp
        (ENNReal.measurable_ofReal.comp (measurable_const.div measurable_id))).mul
        hJp_meas).aemeasurable.mul
      ((ContinuousOn.aemeasurable
        (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx)))
        measurableSet_Ioi).ennreal_ofReal)
  have hsplit : (∫⁻ t in Set.Ioi (0:ℝ),
        (ENNReal.ofReal (2 * Kq / t) ^ q * Jq t
          + ENNReal.ofReal (2 * Kp / t) ^ p₀ * Jp t) * ENNReal.ofReal (t ^ (p - 1)))
      = (∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal (2 * Kq / t) ^ q * Jq t * ENNReal.ofReal (t ^ (p - 1)))
        + (∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal (2 * Kp / t) ^ p₀ * Jp t * ENNReal.ofReal (t ^ (p - 1))) := by
    rw [show (∫⁻ t in Set.Ioi (0:ℝ),
          (ENNReal.ofReal (2 * Kq / t) ^ q * Jq t
            + ENNReal.ofReal (2 * Kp / t) ^ p₀ * Jp t) * ENNReal.ofReal (t ^ (p - 1)))
        = ∫⁻ t in Set.Ioi (0:ℝ),
          (ENNReal.ofReal (2 * Kq / t) ^ q * Jq t * ENNReal.ofReal (t ^ (p - 1))
            + ENNReal.ofReal (2 * Kp / t) ^ p₀ * Jp t * ENNReal.ofReal (t ^ (p - 1))) from by
          apply lintegral_congr; intro t; ring]
    exact lintegral_add_right' _ hΨp_aem
  have halgq : (∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (2 * Kq / t) ^ q * Jq t * ENNReal.ofReal (t ^ (p - 1)))
      = ∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal ((2 * Kq) ^ q) * (ENNReal.ofReal (t ^ (p - 1 - q)) * Jq t) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [show ENNReal.ofReal (2 * Kq / t) ^ q * Jq t * ENNReal.ofReal (t ^ (p - 1))
        = (ENNReal.ofReal (2 * Kq / t) ^ q * ENNReal.ofReal (t ^ (p - 1))) * Jq t by ring,
      key_algebra hKq.le hq0.le ht]
    ring
  have hpullq : (∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal ((2 * Kq) ^ q) * (ENNReal.ofReal (t ^ (p - 1 - q)) * Jq t))
      = ENNReal.ofReal ((2 * Kq) ^ q) * ∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal (t ^ (p - 1 - q)) * Jq t :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hJqkey : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1 - q)) * Jq t)
      = ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1 - q)) *
          (∫⁻ x, Set.indicator
            {x : α | ENNReal.ofReal (t / (2 * (1 / (2 * σ)))) < ENNReal.ofReal (‖f x‖)}
            (fun x => ENNReal.ofReal (‖f x‖) ^ q) x ∂μ) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hinner : Jq t = ∫⁻ x, Set.indicator
            {x : α | ENNReal.ofReal (t / (2 * (1 / (2 * σ)))) < ENNReal.ofReal (‖f x‖)}
            (fun x => ENNReal.ofReal (‖f x‖) ^ q) x ∂μ := by
      show (∫⁻ x, Set.indicator {x : α | σ * t < ‖f x‖}
          (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x ∂μ) = _
      apply lintegral_congr
      intro x
      rw [show {x : α | σ * t < ‖f x‖}
          = {x : α | ENNReal.ofReal (t / (2 * (1 / (2 * σ)))) < ENNReal.ofReal (‖f x‖)} from by
        ext x
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
          show t / (2 * (1 / (2 * σ))) = σ * t by field_simp]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt (mul_pos hσ ht))).symm]
      have hrw : ∀ y : α, ENNReal.ofReal (‖f y‖ ^ q) = ENNReal.ofReal ‖f y‖ ^ q :=
        fun y => (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f y)) hq0.le).symm
      simp only [hrw]
    rw [hinner]
  have hkeyq := Commons.Analysis.MeasureTheory.key_lintegral (μ := μ) (v := fun x => ‖f x‖)
    hf.norm (fun x => norm_nonneg _) (c := 1 / (2 * σ)) (by positivity) (q := q) (r := p - 1 - q)
    hq0.le (by linarith)
  have hcq : (2 * (1 / (2 * σ))) ^ (p - 1 - q + 1) / (p - 1 - q + 1)
      = σ ^ (-(p - q)) / (p - q) := by
    rw [show (2:ℝ) * (1 / (2 * σ)) = σ⁻¹ by field_simp,
      show p - 1 - q + 1 = p - q by ring,
      Real.inv_rpow hσ.le, Real.rpow_neg hσ.le]
  have hkeyq' : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1 - q)) *
          (∫⁻ x, Set.indicator
            {x : α | ENNReal.ofReal (t / (2 * (1 / (2 * σ)))) < ENNReal.ofReal (‖f x‖)}
            (fun x => ENNReal.ofReal (‖f x‖) ^ q) x ∂μ))
      = ENNReal.ofReal (σ ^ (-(p - q)) / (p - q)) * M := by
    rw [hkeyq, hcq]
    congr 1
    rw [show q + (p - 1 - q) + 1 = p by ring, hMdef]
    apply lintegral_congr
    intro x
    rw [← ofReal_norm]
  have hAQ : (2 * Kq) ^ q * (σ ^ (-(p - q)) / (p - q)) = A * σ ^ (-(p - q)) := by
    rw [hAdef]; ring
  have hQ : (∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (2 * Kq / t) ^ q * Jq t * ENNReal.ofReal (t ^ (p - 1)))
      = ENNReal.ofReal (A * σ ^ (-(p - q))) * M := by
    rw [halgq, hpullq, hJqkey, hkeyq']
    rw [show ENNReal.ofReal ((2 * Kq) ^ q) * (ENNReal.ofReal (σ ^ (-(p - q)) / (p - q)) * M)
        = (ENNReal.ofReal ((2 * Kq) ^ q) * ENNReal.ofReal (σ ^ (-(p - q)) / (p - q))) * M from by
          ring,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Kq) ^ q), hAQ]
  have halgp : (∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (2 * Kp / t) ^ p₀ * Jp t * ENNReal.ofReal (t ^ (p - 1)))
      = ∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal ((2 * Kp) ^ p₀) * (ENNReal.ofReal (t ^ (p - 1 - p₀)) * Jp t) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [show ENNReal.ofReal (2 * Kp / t) ^ p₀ * Jp t * ENNReal.ofReal (t ^ (p - 1))
        = (ENNReal.ofReal (2 * Kp / t) ^ p₀ * ENNReal.ofReal (t ^ (p - 1))) * Jp t by ring,
      key_algebra hKp.le hp0'.le ht]
    ring
  have hpullp : (∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal ((2 * Kp) ^ p₀) * (ENNReal.ofReal (t ^ (p - 1 - p₀)) * Jp t))
      = ENNReal.ofReal ((2 * Kp) ^ p₀) * ∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal (t ^ (p - 1 - p₀)) * Jp t :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hJpkey : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1 - p₀)) * Jp t)
      = ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1 - p₀)) *
          (∫⁻ x, Set.indicator
            {x : α | ENNReal.ofReal (‖f x‖) ≤ ENNReal.ofReal (t / (2 * (1 / (2 * σ))))}
            (fun x => ENNReal.ofReal (‖f x‖) ^ p₀) x ∂μ) := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hinner : Jp t = ∫⁻ x, Set.indicator
            {x : α | ENNReal.ofReal (‖f x‖) ≤ ENNReal.ofReal (t / (2 * (1 / (2 * σ))))}
            (fun x => ENNReal.ofReal (‖f x‖) ^ p₀) x ∂μ := by
      show (∫⁻ x, Set.indicator {x : α | ‖f x‖ ≤ σ * t}
          (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x ∂μ) = _
      apply lintegral_congr
      intro x
      rw [show {x : α | ‖f x‖ ≤ σ * t}
          = {x : α | ENNReal.ofReal (‖f x‖) ≤ ENNReal.ofReal (t / (2 * (1 / (2 * σ))))} from by
        ext x
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
          show t / (2 * (1 / (2 * σ))) = σ * t by field_simp]
        exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt (mul_pos hσ ht))).symm]
      have hrw : ∀ y : α, ENNReal.ofReal (‖f y‖ ^ p₀) = ENNReal.ofReal ‖f y‖ ^ p₀ :=
        fun y => (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f y)) hp0'.le).symm
      simp only [hrw]
    rw [hinner]
  have hkeyp := key_lintegral_upper (μ := μ) (v := fun x => ‖f x‖)
    hf.norm (fun x => norm_nonneg _) (c := 1 / (2 * σ)) (by positivity) (q := p₀) (r := p - 1 - p₀)
    hp0' (by linarith) (by linarith)
  have hcp : (2 * (1 / (2 * σ))) ^ (p - 1 - p₀ + 1) / (-(p - 1 - p₀ + 1))
      = σ ^ (p₀ - p) / (p₀ - p) := by
    rw [show (2:ℝ) * (1 / (2 * σ)) = σ⁻¹ by field_simp,
      show p - 1 - p₀ + 1 = p - p₀ by ring,
      show -(p - p₀) = p₀ - p by ring,
      Real.inv_rpow hσ.le,
      show σ ^ (p₀ - p) = σ ^ (-(p - p₀)) by
        rw [show p₀ - p = -(p - p₀) by ring],
      Real.rpow_neg hσ.le]
  have hkeyp' : (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 1 - p₀)) *
          (∫⁻ x, Set.indicator
            {x : α | ENNReal.ofReal (‖f x‖) ≤ ENNReal.ofReal (t / (2 * (1 / (2 * σ))))}
            (fun x => ENNReal.ofReal (‖f x‖) ^ p₀) x ∂μ))
      = ENNReal.ofReal (σ ^ (p₀ - p) / (p₀ - p)) * M := by
    rw [hkeyp, hcp]
    congr 1
    rw [show p₀ + (p - 1 - p₀) + 1 = p by ring, hMdef]
    apply lintegral_congr
    intro x
    rw [← ofReal_norm]
  have hBP : (2 * Kp) ^ p₀ * (σ ^ (p₀ - p) / (p₀ - p)) = B * σ ^ (p₀ - p) := by
    rw [hBdef]; ring
  have hP : (∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (2 * Kp / t) ^ p₀ * Jp t * ENNReal.ofReal (t ^ (p - 1)))
      = ENNReal.ofReal (B * σ ^ (p₀ - p)) * M := by
    rw [halgp, hpullp, hJpkey, hkeyp']
    rw [show ENNReal.ofReal ((2 * Kp) ^ p₀) * (ENNReal.ofReal (σ ^ (p₀ - p) / (p₀ - p)) * M)
        = (ENNReal.ofReal ((2 * Kp) ^ p₀) * ENNReal.ofReal (σ ^ (p₀ - p) / (p₀ - p))) * M from by
          ring,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Kp) ^ p₀), hBP]
  have htwo : (∫⁻ t in Set.Ioi (0:ℝ),
        (ENNReal.ofReal (2 * Kq / t) ^ q * Jq t
          + ENNReal.ofReal (2 * Kp / t) ^ p₀ * Jp t) * ENNReal.ofReal (t ^ (p - 1)))
      = (ENNReal.ofReal (A * σ ^ (-(p - q))) + ENNReal.ofReal (B * σ ^ (p₀ - p))) * M := by
    rw [hsplit, hQ, hP]
    ring
  have harg1 : p * ((K₀ / p) * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p))
      = K₀ * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p) := by
    field_simp
  have hpeat : ENNReal.ofReal p
        * (ENNReal.ofReal ((K₀ / p) * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)) * M)
      = ENNReal.ofReal (K₀ * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)) * M := by
    rw [show ENNReal.ofReal p
          * (ENNReal.ofReal ((K₀ / p) * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)) * M)
        = (ENNReal.ofReal p
            * ENNReal.ofReal ((K₀ / p) * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p))) * M from by ring,
      ← ENNReal.ofReal_mul hp0.le, harg1]
  have hbound : (eLpNorm (T f) (ENNReal.ofReal p) ν) ^ p
      ≤ ENNReal.ofReal (K₀ * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)) * M := by
    rw [hTLp, hlay]
    calc ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ),
            ν {x : β | ENNReal.ofReal t < T f x} * ENNReal.ofReal (t ^ (p - 1)))
        ≤ ENNReal.ofReal p * (∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (2 * Kq / t) ^ q * Jq t
              + ENNReal.ofReal (2 * Kp / t) ^ p₀ * Jp t) * ENNReal.ofReal (t ^ (p - 1))) :=
          mul_le_mul_right htrunc _
      _ = ENNReal.ofReal p * ((ENNReal.ofReal (A * σ ^ (-(p - q)))
            + ENNReal.ofReal (B * σ ^ (p₀ - p))) * M) := by rw [htwo]
      _ ≤ ENNReal.ofReal p
            * (ENNReal.ofReal ((K₀ / p) * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)) * M) := by
          refine mul_le_mul_right ?_ (ENNReal.ofReal p)
          refine mul_le_mul_left ?_ M
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal hAσBσ
      _ = ENNReal.ofReal (K₀ * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)) * M := hpeat
  have hId : (K₀ ^ (1 / p) * Kq ^ θ * Kp ^ (1 - θ)) ^ p
      = K₀ * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p) := by
    rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hK₀.le _) (Real.rpow_nonneg hKq.le _))
          (Real.rpow_nonneg hKp.le _),
        Real.mul_rpow (Real.rpow_nonneg hK₀.le _) (Real.rpow_nonneg hKq.le _),
        ← Real.rpow_mul hK₀.le, ← Real.rpow_mul hKq.le, ← Real.rpow_mul hKp.le,
        show (1 / p) * p = 1 by field_simp, Real.rpow_one]
  have hroot : (eLpNorm (T f) (ENNReal.ofReal p) ν) ^ p
      ≤ (ENNReal.ofReal (K₀ ^ (1 / p) * Kq ^ θ * Kp ^ (1 - θ))
          * eLpNorm f (ENNReal.ofReal p) μ) ^ p := by
    calc (eLpNorm (T f) (ENNReal.ofReal p) ν) ^ p
        ≤ ENNReal.ofReal (K₀ * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)) * M := hbound
      _ = ENNReal.ofReal (K₀ * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p))
            * (eLpNorm f (ENNReal.ofReal p) μ) ^ p := by rw [← hfLp]
      _ = (ENNReal.ofReal (K₀ ^ (1 / p) * Kq ^ θ * Kp ^ (1 - θ))
            * eLpNorm f (ENNReal.ofReal p) μ) ^ p := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
              ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, hId]
  exact (ENNReal.rpow_le_rpow_iff hp0).mp hroot

end Work.BourgainPlan.Maximal
