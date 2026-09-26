import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepLoopChamfer_locallyIntegrable

/-!
# Smoothness and periodicity of the smoothed sweep family

`sweepFam r D lam δ₁ δ₂ σ t` is defined as a double *interval* integral of the (merely
piecewise continuous) chamfered sweep loop `sweepLoopChamfer` against the smooth bump
`sweepBump`:

`sweepFam σ t = ∫ v in (-1)..1, sweepBump v • ∫ u in (-1)..1, sweepBump u • Φ (σ - δ₂ v) (t - δ₁ u)`

with `Φ = fun p => sweepLoopChamfer r D lam p.1 p.2`.  Both integrations are convolutions with
a smooth compactly supported kernel, so both variables are smoothed: the family is jointly
`C^∞`, its `t`-slices are `C^∞`, and it is `period`-periodic in `t`.

The bridge is `sweepKernel_convolution_eq`: after the change of variables
`x = σ - δ₂ v`, `y = t - δ₁ u` (the substitution `intervalIntegral.integral_comp_sub_mul`), the
double interval integral is the convolution of `Φ` with the smooth compactly supported kernel
`sweepKernel δ₁ δ₂ z = (sweepBump (z.1/δ₂)/|δ₂|) * (sweepBump (z.2/δ₁)/|δ₁|)`; smoothness then
follows from `HasCompactSupport.contDiff_convolution_right`.

## Main results

* `Work.Drive.sweepKernel_convolution_eq` — the double interval integral is a convolution.
* `Work.Drive.sweepFam_contDiff_periodic` — the target statement.
-/

noncomputable section

set_option maxHeartbeats 300000

namespace Work.Drive

open MeasureTheory

open LeanEval.KnotTheory.Quadrisecant

/-- The smooth, compactly supported convolution kernel of the sweep family; the `δ`s are inverted
so that the substitution `x = σ - δ₂ v`, `y = t - δ₁ u` turns the double interval integral
`∫∫ sweepBump v · sweepBump u · Φ (σ - δ₂ v) (t - δ₁ u)` into the convolution with this
kernel. -/
def sweepKernel (δ₁ δ₂ : ℝ) (z : ℝ × ℝ) : ℝ :=
  (sweepBump (z.1 / δ₂) / |δ₂|) * (sweepBump (z.2 / δ₁) / |δ₁|)

lemma sweepKernel_sub (δ₁ δ₂ s t y₁ y₂ : ℝ) :
    sweepKernel δ₁ δ₂ ((s, t) - (y₁, y₂)) =
      (sweepBump ((s - y₁) / δ₂) / |δ₂|) * (sweepBump ((t - y₂) / δ₁) / |δ₁|) := rfl

lemma continuous_sweepBump : Continuous sweepBump := by
  unfold sweepBump
  exact (Real.smoothTransition.continuous.comp (continuous_const.add continuous_id)).mul
    (Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id))

/-- The bump vanishes outside `(-1,1)`. -/
lemma sweepBump_eq_zero_of_one_le_abs {u : ℝ} (h : 1 ≤ |u|) : sweepBump u = 0 := by
  rw [le_abs] at h
  rcases h with h | h
  · simp [sweepBump, Real.smoothTransition.zero_of_nonpos (by linarith : (1 - u : ℝ) ≤ 0)]
  · simp [sweepBump, Real.smoothTransition.zero_of_nonpos (by linarith : (1 + u : ℝ) ≤ 0)]

lemma mem_Icc_of_abs_le {x a b : ℝ} (h : |x - a| ≤ b) : x ∈ Set.Icc (a - b) (a + b) := by
  rw [Set.mem_Icc]
  have := abs_le.mp h
  constructor <;> linarith

/-- The change of variables `y = t - δ u` on an interval integral, written with `|δ|` so that no
case distinction on the sign of `δ` is needed. -/
lemma integral_Icc_eq_abs_mul_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → E) {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    ∫ y in (t - |δ|)..(t + |δ|), h y = |δ| • ∫ u in (-1 : ℝ)..1, h (t - δ * u) := by
  have hsub : ∫ u in (-1 : ℝ)..1, h (t - δ * u) = δ⁻¹ • ∫ y in (t - δ)..(t + δ), h y := by
    have := intervalIntegral.integral_comp_sub_mul h hδ t (a := (-1 : ℝ)) (b := 1)
    simpa using this
  rw [hsub, smul_smul]
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · have e1 : t - |δ| = t + δ := by rw [abs_of_neg hneg]; ring
    have e2 : t + |δ| = t - δ := by rw [abs_of_neg hneg]; ring
    rw [e1, e2, intervalIntegral.integral_symm, abs_of_neg hneg,
      show -δ * δ⁻¹ = (-1 : ℝ) by field_simp, neg_one_smul]
  · have h1 : δ * δ⁻¹ = (1 : ℝ) := by field_simp
    rw [abs_of_pos hpos, h1, one_smul]

/-- An integral over `ℝ` of a function supported in `[t-|δ|, t+|δ|]` is the corresponding
interval integral. -/
lemma integral_eq_integral_interval_of_support {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {δ : ℝ} (h : ℝ → E) (t : ℝ)
    (hzero : ∀ y, y ∉ Set.Icc (t - |δ|) (t + |δ|) → h y = 0) :
    ∫ y, h y = ∫ y in (t - |δ|)..(t + |δ|), h y := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero (μ := volume)]
  rw [intervalIntegral.integral_of_le (by have := abs_nonneg δ; linarith)]
  rw [integral_Icc_eq_integral_Ioc]

lemma abs_mul_div_abs_self {δ x : ℝ} (hδ : δ ≠ 0) : |δ| * (x / |δ|) = x := by
  have h : |δ| ≠ 0 := abs_ne_zero.mpr hδ
  field_simp

lemma bump_self_div {δ x : ℝ} (hδ : δ ≠ 0) : sweepBump (δ * x / δ) = sweepBump x := by
  rw [mul_div_cancel_left₀ _ hδ]

lemma contDiff_sweepBump : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sweepBump := by
  unfold sweepBump
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

lemma contDiff_sweepKernel (δ₁ δ₂ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sweepKernel δ₁ δ₂) := by
  unfold sweepKernel
  exact ((contDiff_sweepBump.comp (contDiff_fst.div_const δ₂)).div_const |δ₂|).mul
    ((contDiff_sweepBump.comp (contDiff_snd.div_const δ₁)).div_const |δ₁|)

lemma hasCompactSupport_sweepKernel {δ₁ δ₂ : ℝ} (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) :
    HasCompactSupport (sweepKernel δ₁ δ₂) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-|δ₂|) |δ₂| ×ˢ Set.Icc (-|δ₁|) |δ₁|)
    (isCompact_Icc.prod isCompact_Icc) ?_
  intro z hz
  rw [Function.mem_support] at hz
  have hb1 : sweepBump (z.1 / δ₂) ≠ 0 := by
    intro h0
    exact hz (by rw [sweepKernel, h0, zero_div, zero_mul])
  have hb2 : sweepBump (z.2 / δ₁) ≠ 0 := by
    intro h0
    exact hz (by rw [sweepKernel, h0, zero_div, mul_zero])
  have hle1 : |z.1 - 0| ≤ |δ₂| := by
    have h1 : |z.1 / δ₂| < 1 := lt_of_not_ge fun h => hb1 (sweepBump_eq_zero_of_one_le_abs h)
    rw [abs_div, div_lt_one (abs_pos.mpr hδ₂)] at h1
    simpa using h1.le
  have hle2 : |z.2 - 0| ≤ |δ₁| := by
    have h1 : |z.2 / δ₁| < 1 := lt_of_not_ge fun h => hb2 (sweepBump_eq_zero_of_one_le_abs h)
    rw [abs_div, div_lt_one (abs_pos.mpr hδ₁)] at h1
    simpa using h1.le
  rw [Set.mem_prod]
  exact ⟨by simpa using mem_Icc_of_abs_le hle1, by simpa using mem_Icc_of_abs_le hle2⟩

/-- **The double interval integral of the sweep is the convolution with `sweepKernel`.**

For any locally integrable `f` (in the application, the chamfered sweep loop), substituting
`x = s - δ₂ v` in the outer and `y = t - δ₁ u` in the inner interval integral turns the double
interval integral into the convolution of `f` with the smooth compactly supported kernel
`sweepKernel δ₁ δ₂`. -/
theorem sweepKernel_convolution_eq (f : ℝ × ℝ → Space) (hf : LocallyIntegrable f volume)
    {δ₁ δ₂ : ℝ} (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) (s t : ℝ) :
    (∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ ((s, t) - y) • f y)
      = ∫ v in (-1)..1, sweepBump v •
          (∫ u in (-1)..1, sweepBump u • f (s - δ₂ * v, t - δ₁ * u)) := by
  have hK : Continuous (sweepKernel δ₁ δ₂) := by
    unfold sweepKernel
    exact ((continuous_sweepBump.comp (continuous_fst.div_const δ₂)).div_const |δ₂|).mul
      ((continuous_sweepBump.comp (continuous_snd.div_const δ₁)).div_const |δ₁|)
  have hcont : Continuous (fun y : ℝ × ℝ => sweepKernel δ₁ δ₂ ((s, t) - y)) :=
    hK.comp (continuous_const.sub continuous_id)
  have hsupp : Function.support (fun y : ℝ × ℝ => sweepKernel δ₁ δ₂ ((s, t) - y)) ⊆
      Set.Icc (s - |δ₂|) (s + |δ₂|) ×ˢ Set.Icc (t - |δ₁|) (t + |δ₁|) := by
    intro y hy
    rw [Function.mem_support] at hy
    have hb1 : sweepBump ((s - y.1) / δ₂) ≠ 0 := by
      intro h0
      exact hy (by rw [sweepKernel_sub, h0, zero_div, zero_mul])
    have hb2 : sweepBump ((t - y.2) / δ₁) ≠ 0 := by
      intro h0
      exact hy (by rw [sweepKernel_sub, h0, zero_div, mul_zero])
    have hle1 : |y.1 - s| ≤ |δ₂| := by
      have h1 : |(s - y.1) / δ₂| < 1 := lt_of_not_ge fun h => hb1 (sweepBump_eq_zero_of_one_le_abs h)
      rw [abs_div, div_lt_one (abs_pos.mpr hδ₂)] at h1
      rw [abs_sub_comm]; exact h1.le
    have hle2 : |y.2 - t| ≤ |δ₁| := by
      have h1 : |(t - y.2) / δ₁| < 1 := lt_of_not_ge fun h => hb2 (sweepBump_eq_zero_of_one_le_abs h)
      rw [abs_div, div_lt_one (abs_pos.mpr hδ₁)] at h1
      rw [abs_sub_comm]; exact h1.le
    rw [Set.mem_prod]
    exact ⟨mem_Icc_of_abs_le hle1, mem_Icc_of_abs_le hle2⟩
  have hcs : HasCompactSupport (fun y : ℝ × ℝ => sweepKernel δ₁ δ₂ ((s, t) - y)) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc) hsupp
  have hint : Integrable (fun y : ℝ × ℝ => sweepKernel δ₁ δ₂ ((s, t) - y) • f y) volume :=
    hf.integrable_smul_left_of_hasCompactSupport hcont hcs
  change (∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ ((s, t) - y) • f y ∂(volume.prod volume)) = _
  rw [integral_prod (fun y : ℝ × ℝ => sweepKernel δ₁ δ₂ ((s, t) - y) • f y) hint]
  simp only [sweepKernel_sub]
  have hinner : ∀ y₁ : ℝ,
      (∫ y₂ : ℝ, ((sweepBump ((s - y₁) / δ₂) / |δ₂|) *
          (sweepBump ((t - y₂) / δ₁) / |δ₁|)) • f (y₁, y₂))
        = (sweepBump ((s - y₁) / δ₂) / |δ₂|) •
            (∫ u in (-1)..1, sweepBump u • f (y₁, t - δ₁ * u)) := by
    intro y₁
    simp_rw [mul_smul]
    rw [MeasureTheory.integral_smul]
    congr 1
    rw [integral_eq_integral_interval_of_support (δ := δ₁)
      (fun y₂ => (sweepBump ((t - y₂) / δ₁) / |δ₁|) • f (y₁, y₂)) t ?_]
    · rw [integral_Icc_eq_abs_mul_integral
        (fun y₂ => (sweepBump ((t - y₂) / δ₁) / |δ₁|) • f (y₁, y₂)) hδ₁ t]
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [smul_smul, show t - (t - δ₁ * u) = δ₁ * u by ring, bump_self_div hδ₁,
        abs_mul_div_abs_self hδ₁]
    · intro y₂ hy₂
      have hb : sweepBump ((t - y₂) / δ₁) = 0 := by
        apply sweepBump_eq_zero_of_one_le_abs
        by_contra hcon
        have h1 : |(t - y₂) / δ₁| < 1 := lt_of_not_ge hcon
        rw [abs_div, div_lt_one (abs_pos.mpr hδ₁)] at h1
        exact hy₂ (mem_Icc_of_abs_le (by rw [abs_sub_comm]; exact h1.le))
      rw [hb, zero_div, zero_smul]
  simp_rw [hinner]
  rw [integral_eq_integral_interval_of_support (δ := δ₂)
    (fun y₁ => (sweepBump ((s - y₁) / δ₂) / |δ₂|) •
      (∫ u in (-1)..1, sweepBump u • f (y₁, t - δ₁ * u))) s ?_]
  · rw [integral_Icc_eq_abs_mul_integral
      (fun y₁ => (sweepBump ((s - y₁) / δ₂) / |δ₂|) •
        (∫ u in (-1)..1, sweepBump u • f (y₁, t - δ₁ * u))) hδ₂ s]
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    rw [smul_smul, show s - (s - δ₂ * v) = δ₂ * v by ring, bump_self_div hδ₂,
      abs_mul_div_abs_self hδ₂]
  · intro y₁ hy₁
    have hb : sweepBump ((s - y₁) / δ₂) = 0 := by
      apply sweepBump_eq_zero_of_one_le_abs
      by_contra hcon
      have h1 : |(s - y₁) / δ₂| < 1 := lt_of_not_ge hcon
      rw [abs_div, div_lt_one (abs_pos.mpr hδ₂)] at h1
      exact hy₁ (mem_Icc_of_abs_le (by rw [abs_sub_comm]; exact h1.le))
    rw [hb, zero_div, zero_smul]

/-- `1 ≤ ∞` in `WithTop ℕ∞`, stated separately so that `ContDiff.of_le` can be applied
without unfolding `ContDiff` in a large context. -/
lemma one_le_coe_top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp

theorem sweepFam_contDiff_periodic {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : Continuous r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ : ℝ) (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ p.1 p.2) ∧
    (∀ σ t : ℝ, Work.Drive.sweepFam r D lam δ₁ δ₂ σ
        (t + LeanEval.KnotTheory.Quadrisecant.period)
      = Work.Drive.sweepFam r D lam δ₁ δ₂ σ t) ∧
    (∀ σ : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ t)) := by
  have hΦ : LocallyIntegrable
      (fun p : ℝ × ℝ => Work.Drive.sweepLoopChamfer r D lam p.1 p.2) volume :=
    Work.Drive.sweepLoopChamfer_locallyIntegrable hr D lam
  -- `period`-periodicity in the loop parameter
  have hper : ∀ σ t : ℝ,
      sweepFam r D lam δ₁ δ₂ σ (t + period) = sweepFam r D lam δ₁ δ₂ σ t := by
    have hper_chamfer : ∀ s t : ℝ,
        sweepLoopChamfer r D lam s (t + period) = sweepLoopChamfer r D lam s t := by
      intro s t
      simp only [sweepLoopChamfer, sweepParam_add_period]
    have hper_smooth : ∀ σ t : ℝ,
        sweepSmoothT r D lam δ₁ σ (t + period) = sweepSmoothT r D lam δ₁ σ t := by
      intro σ t
      simp only [sweepSmoothT]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      congr 1
      rw [show t + period - δ₁ * u = (t - δ₁ * u) + period by ring, hper_chamfer]
    intro σ t
    simp only [sweepFam]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only
    congr 1
    exact hper_smooth (σ - δ₂ * v) t
  -- the family is the convolution of the raw loop with the smooth kernel `sweepKernel`
  have hconv : ∀ p : ℝ × ℝ, sweepFam r D lam δ₁ δ₂ p.1 p.2
      = ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ (p - y) •
          (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 p.2) y := by
    intro p
    rw [sweepKernel_convolution_eq (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 p.2) hΦ
      hδ₁ hδ₂ p.1 p.2]
    rfl
  have hmain : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ (p - y) •
        (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 p.2) y) := by
    have h := (hasCompactSupport_sweepKernel hδ₁ hδ₂).contDiff_convolution_right
      (μ := volume) ((ContinuousLinearMap.lsmul ℝ ℝ).flip : Space →L[ℝ] ℝ →L[ℝ] Space) hΦ
      (contDiff_sweepKernel δ₁ δ₂)
    have hfun : (MeasureTheory.convolution (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 p.2)
          (sweepKernel δ₁ δ₂) ((ContinuousLinearMap.lsmul ℝ ℝ).flip : Space →L[ℝ] ℝ →L[ℝ] Space)
          MeasureTheory.volume)
        = (fun p : ℝ × ℝ => ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ (p - y) •
            (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 p.2) y) := by
      funext p
      rw [MeasureTheory.convolution_def]
      simp only [ContinuousLinearMap.lsmul_flip_apply, ContinuousLinearMap.toSpanSingleton_apply]
    rw [hfun] at h
    exact h
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => sweepFam r D lam δ₁ δ₂ p.1 p.2) := by
    have hfun : (fun p : ℝ × ℝ => sweepFam r D lam δ₁ δ₂ p.1 p.2)
        = (fun p : ℝ × ℝ => ∫ y : ℝ × ℝ, sweepKernel δ₁ δ₂ (p - y) •
            (fun p : ℝ × ℝ => sweepLoopChamfer r D lam p.1 p.2) y) := funext hconv
    simpa only [hfun] using hmain
  refine ⟨hF.of_le one_le_coe_top, hper, fun σ => ?_⟩
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    ((fun p : ℝ × ℝ => sweepFam r D lam δ₁ δ₂ p.1 p.2) ∘ fun t : ℝ => (σ, t))
  exact hF.comp (contDiff_prodMk_right σ)

end Work.Drive
