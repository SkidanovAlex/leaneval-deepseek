import Mathlib
import Submission.Work.BourgainPlan.Maximal.ennRealMarcinkiewiczL1L2
import Submission.Work.BourgainPlan.Maximal.two_weak_truncation_bound

open MeasureTheory Set
open scoped ENNReal

namespace Work.BourgainPlan.Maximal

/-- For `r > 0`, `(eLpNorm f (ofReal r) μ) ^ r` is the integral of `‖f‖ ^ r`. -/
private lemma eLpNorm_rpow_eq_lintegral_enorm
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (f : α → ℂ) {r : ℝ} (hr : 0 < r) (hf : MeasureTheory.AEStronglyMeasurable f μ) :
    (MeasureTheory.eLpNorm f (ENNReal.ofReal r) μ) ^ r
      = ∫⁻ x, ‖f x‖ₑ ^ r ∂μ := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal r)
      (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hr.le]
  rw [← ENNReal.rpow_mul, show (1 / r) * r = 1 by field_simp, ENNReal.rpow_one]

/-- For `r > 0` and any set `A`, `(eLpNorm (A.indicator f) (ofReal r) μ) ^ r` is the integral of
`‖f‖ ^ r` over `A`, provided `A.indicator f` is a.e. strongly measurable. -/
private lemma eLpNorm_indicator_rpow_eq
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (f : α → ℂ) (A : Set α) {r : ℝ} (hr : 0 < r)
    (hA : MeasureTheory.AEStronglyMeasurable (A.indicator f) μ) :
    (MeasureTheory.eLpNorm (A.indicator f) (ENNReal.ofReal r) μ) ^ r
      = ∫⁻ x, A.indicator (fun x => ENNReal.ofReal (‖f x‖ ^ r)) x ∂μ := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal r)
      (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top hA, ENNReal.toReal_ofReal hr.le]
  rw [← ENNReal.rpow_mul, show (1 / r) * r = 1 by field_simp, ENNReal.rpow_one]
  refine MeasureTheory.lintegral_congr fun x => ?_
  rw [enorm_indicator_eq_indicator_enorm]
  rw [show (A.indicator (fun a => ‖f a‖ₑ) x) ^ r
        = A.indicator (fun a => ‖f a‖ₑ ^ r) x from by
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
          ENNReal.zero_rpow_of_pos hr]]
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hr.le]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- On the set where `‖f‖ > c` (with `r < s`), the `r`-th power of `‖f‖` is controlled by
`c ^ (r - s)` times the `s`-th power of `‖f‖`. -/
private lemma lintegral_indicator_rpow_high_le
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (f : α → ℂ) {r s c : ℝ} (hr : 0 < r) (hrs : r < s) (hc : 0 < c) :
    ∫⁻ x, Set.indicator {x : α | c < ‖f x‖} (fun x => ENNReal.ofReal (‖f x‖ ^ r)) x ∂μ
      ≤ ENNReal.ofReal (c ^ (r - s)) * ∫⁻ x, ‖f x‖ₑ ^ s ∂μ := by
  have hs : 0 < s := lt_trans hr hrs
  have hpt : ∀ x, Set.indicator {x : α | c < ‖f x‖}
        (fun x => ENNReal.ofReal (‖f x‖ ^ r)) x
      ≤ ENNReal.ofReal (c ^ (r - s)) * ‖f x‖ₑ ^ s := by
    intro x
    by_cases hx : c < ‖f x‖
    · have hx' : x ∈ {x : α | c < ‖f x‖} := hx
      have hfx : 0 < ‖f x‖ := lt_trans hc hx
      have hlt : ‖f x‖ ^ (r - s) < c ^ (r - s) :=
        Real.rpow_lt_rpow_of_neg hc hx (by linarith)
      have hsplit : ‖f x‖ ^ r = ‖f x‖ ^ (r - s) * ‖f x‖ ^ s := by
        rw [← Real.rpow_add hfx, show r - s + s = r by ring]
      have hle : ‖f x‖ ^ r ≤ c ^ (r - s) * ‖f x‖ ^ s := by
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right hlt.le (Real.rpow_nonneg (norm_nonneg _) s)
      rw [Set.indicator_of_mem hx' (fun x => ENNReal.ofReal (‖f x‖ ^ r))]
      calc ENNReal.ofReal (‖f x‖ ^ r)
          ≤ ENNReal.ofReal (c ^ (r - s) * ‖f x‖ ^ s) := ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal (c ^ (r - s)) * ENNReal.ofReal (‖f x‖ ^ s) :=
            ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)
        _ = ENNReal.ofReal (c ^ (r - s)) * ‖f x‖ₑ ^ s := by
            rw [← ofReal_norm (f x), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs.le]
    · have hx' : x ∉ {x : α | c < ‖f x‖} := hx
      rw [Set.indicator_of_notMem hx' (fun x => ENNReal.ofReal (‖f x‖ ^ r))]
      exact bot_le
  calc ∫⁻ x, Set.indicator {x : α | c < ‖f x‖}
          (fun x => ENNReal.ofReal (‖f x‖ ^ r)) x ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (c ^ (r - s)) * ‖f x‖ₑ ^ s ∂μ :=
        MeasureTheory.lintegral_mono hpt
    _ = ENNReal.ofReal (c ^ (r - s)) * ∫⁻ x, ‖f x‖ₑ ^ s ∂μ :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- On the complement of the set where `‖f‖ > c` (with `s < r`), the `r`-th power of `‖f‖` is
controlled by `c ^ (r - s)` times the `s`-th power of `‖f‖`. -/
private lemma lintegral_indicator_rpow_low_le
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    (f : α → ℂ) {r s c : ℝ} (hs : 0 < s) (hsr : s < r) (hc : 0 < c) :
    ∫⁻ x, Set.indicator {x : α | c < ‖f x‖}ᶜ
        (fun x => ENNReal.ofReal (‖f x‖ ^ r)) x ∂μ
      ≤ ENNReal.ofReal (c ^ (r - s)) * ∫⁻ x, ‖f x‖ₑ ^ s ∂μ := by
  have hr : 0 < r := lt_trans hs hsr
  have hpt : ∀ x, Set.indicator {x : α | c < ‖f x‖}ᶜ
        (fun x => ENNReal.ofReal (‖f x‖ ^ r)) x
      ≤ ENNReal.ofReal (c ^ (r - s)) * ‖f x‖ₑ ^ s := by
    intro x
    by_cases hx : x ∈ {x : α | c < ‖f x‖}ᶜ
    · have hle0 : ‖f x‖ ≤ c := not_lt.mp (by simpa using hx)
      have hle : ‖f x‖ ^ r ≤ c ^ (r - s) * ‖f x‖ ^ s := by
        by_cases h0 : ‖f x‖ = 0
        · rw [h0, Real.zero_rpow hr.ne']
          exact mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (le_refl 0) s)
        · have hfx : 0 < ‖f x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
          have hsplit : ‖f x‖ ^ r = ‖f x‖ ^ (r - s) * ‖f x‖ ^ s := by
            rw [← Real.rpow_add hfx, show r - s + s = r by ring]
          rw [hsplit]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (norm_nonneg _) hle0 (by linarith))
            (Real.rpow_nonneg (norm_nonneg _) s)
      rw [Set.indicator_of_mem hx (fun x => ENNReal.ofReal (‖f x‖ ^ r))]
      calc ENNReal.ofReal (‖f x‖ ^ r)
          ≤ ENNReal.ofReal (c ^ (r - s) * ‖f x‖ ^ s) := ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal (c ^ (r - s)) * ENNReal.ofReal (‖f x‖ ^ s) :=
            ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)
        _ = ENNReal.ofReal (c ^ (r - s)) * ‖f x‖ₑ ^ s := by
            rw [← ofReal_norm (f x), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs.le]
    · have hx' : x ∉ {x : α | c < ‖f x‖}ᶜ := hx
      rw [Set.indicator_of_notMem hx' (fun x => ENNReal.ofReal (‖f x‖ ^ r))]
      exact bot_le
  calc ∫⁻ x, Set.indicator {x : α | c < ‖f x‖}ᶜ
          (fun x => ENNReal.ofReal (‖f x‖ ^ r)) x ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (c ^ (r - s)) * ‖f x‖ₑ ^ s ∂μ :=
        MeasureTheory.lintegral_mono hpt
    _ = ENNReal.ofReal (c ^ (r - s)) * ∫⁻ x, ‖f x‖ₑ ^ s ∂μ :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The upper truncation `f · 1_{c < ‖f‖}` of an `L^s` function lies in `L^r` for `r < s`
(and `c > 0`). -/
private lemma memLp_indicator_high
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {r s c : ℝ} (hr : 0 < r) (hrs : r < s) (hc : 0 < c) {f : α → ℂ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal s) μ) :
    MeasureTheory.MemLp (Set.indicator {x : α | c < ‖f x‖} f) (ENNReal.ofReal r) μ := by
  have hs : 0 < s := lt_trans hr hrs
  have hsfin : ∫⁻ x, ‖f x‖ₑ ^ s ∂μ < ⊤ := by
    rw [← eLpNorm_rpow_eq_lintegral_enorm (μ := μ) f hs hf.aestronglyMeasurable]
    exact ENNReal.rpow_lt_top_of_nonneg hs.le (ne_of_lt hf.eLpNorm_lt_top)
  have hnull : MeasureTheory.NullMeasurableSet {x : α | c < ‖f x‖} μ :=
    nullMeasurableSet_lt (f := fun _ : α => c) (g := fun x => ‖f x‖)
      aemeasurable_const hf.aestronglyMeasurable.norm.aemeasurable
  rw [MeasureTheory.memLp_iff]
  · have hlt : (MeasureTheory.eLpNorm (Set.indicator {x : α | c < ‖f x‖} f)
        (ENNReal.ofReal r) μ) ^ r < ⊤ := by
      rw [eLpNorm_indicator_rpow_eq f {x : α | c < ‖f x‖} hr
        (hf.aestronglyMeasurable.indicator₀ hnull)]
      exact lt_of_le_of_lt (lintegral_indicator_rpow_high_le (μ := μ) f hr hrs hc)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsfin)
    exact (ENNReal.rpow_lt_top_iff_of_pos hr).mp hlt

/-- The lower truncation `f · 1_{‖f‖ ≤ c}` of an `L^s` function lies in `L^r` for `s < r`
(and `c > 0`). -/
private lemma memLp_indicator_low
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {r s c : ℝ} (hs : 0 < s) (hsr : s < r) (hc : 0 < c) {f : α → ℂ}
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal s) μ) :
    MeasureTheory.MemLp (Set.indicator {x : α | c < ‖f x‖}ᶜ f) (ENNReal.ofReal r) μ := by
  have hr : 0 < r := lt_trans hs hsr
  have hsfin : ∫⁻ x, ‖f x‖ₑ ^ s ∂μ < ⊤ := by
    rw [← eLpNorm_rpow_eq_lintegral_enorm (μ := μ) f hs hf.aestronglyMeasurable]
    exact ENNReal.rpow_lt_top_of_nonneg hs.le (ne_of_lt hf.eLpNorm_lt_top)
  have hnull : MeasureTheory.NullMeasurableSet {x : α | c < ‖f x‖}ᶜ μ :=
    (nullMeasurableSet_lt (f := fun _ : α => c) (g := fun x => ‖f x‖)
      aemeasurable_const hf.aestronglyMeasurable.norm.aemeasurable).compl
  rw [MeasureTheory.memLp_iff]
  · have hlt : (MeasureTheory.eLpNorm (Set.indicator {x : α | c < ‖f x‖}ᶜ f)
        (ENNReal.ofReal r) μ) ^ r < ⊤ := by
      rw [eLpNorm_indicator_rpow_eq f {x : α | c < ‖f x‖}ᶜ hr
        (hf.aestronglyMeasurable.indicator₀ hnull)]
      exact lt_of_le_of_lt (lintegral_indicator_rpow_low_le (μ := μ) f hs hsr hc)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsfin)
    exact (ENNReal.rpow_lt_top_iff_of_pos hr).mp hlt

/-- **Chebyshev–Markov.**  A strong `L^r` bound with constant `K` implies the weak `(r,r)` bound
with the same constant, for input functions that are additionally known to be `L^p` (which is
what is needed to obtain the a.e.-measurability of the output from a hypothesis that only
provides it on `L^p` inputs). -/
private lemma weak_of_strong_memLp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    {T : (α → ℂ) → (β → ENNReal)}
    {r p : ℝ} (hr : 0 < r)
    (hmeas : ∀ f : α → ℂ, MeasureTheory.MemLp f (ENNReal.ofReal p) μ →
      AEMeasurable (T f) ν)
    {K : ℝ} (hK : 0 < K)
    (hbd : ∀ f : α → ℂ, MeasureTheory.MemLp f (ENNReal.ofReal r) μ →
      MeasureTheory.eLpNorm (T f) (ENNReal.ofReal r) ν
        ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm f (ENNReal.ofReal r) μ) :
    ∀ (f : α → ℂ), MeasureTheory.MemLp f (ENNReal.ofReal r) μ →
      MeasureTheory.MemLp f (ENNReal.ofReal p) μ → ∀ lam : ℝ, 0 < lam →
      ν {x : β | ENNReal.ofReal lam < T f x}
        ≤ ENNReal.ofReal (K / lam) ^ r
            * (MeasureTheory.eLpNorm f (ENNReal.ofReal r) μ) ^ r := by
  intro f hfr hfp lam hlam
  have hcheb := MeasureTheory.mul_meas_ge_le_pow_eLpNorm' (μ := ν)
    (p := ENNReal.ofReal r) (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
    (f := T f) (ENNReal.ofReal lam)
  have hcheb' : ENNReal.ofReal lam ^ r * ν {x : β | ENNReal.ofReal lam ≤ T f x}
      ≤ (MeasureTheory.eLpNorm (T f) (ENNReal.ofReal r) ν) ^ r := by
    simpa only [ENNReal.toReal_ofReal hr.le, enorm_eq_self] using hcheb
  have hstep : ENNReal.ofReal lam ^ r * ν {x : β | ENNReal.ofReal lam < T f x}
      ≤ ENNReal.ofReal K ^ r * (MeasureTheory.eLpNorm f (ENNReal.ofReal r) μ) ^ r := by
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
    calc (MeasureTheory.eLpNorm (T f) (ENNReal.ofReal r) ν) ^ r
        ≤ (ENNReal.ofReal K * MeasureTheory.eLpNorm f (ENNReal.ofReal r) μ) ^ r :=
          ENNReal.rpow_le_rpow (hbd f hfr) hr.le
      _ = ENNReal.ofReal K ^ r * (MeasureTheory.eLpNorm f (ENNReal.ofReal r) μ) ^ r :=
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
          * (ENNReal.ofReal K ^ r * (MeasureTheory.eLpNorm f (ENNReal.ofReal r) μ) ^ r) :=
        mul_le_mul_right hstep _
    _ = ((ENNReal.ofReal lam ^ r)⁻¹ * ENNReal.ofReal K ^ r)
          * (MeasureTheory.eLpNorm f (ENNReal.ofReal r) μ) ^ r := by rw [mul_assoc]
    _ = ENNReal.ofReal (K / lam) ^ r
          * (MeasureTheory.eLpNorm f (ENNReal.ofReal r) μ) ^ r := by rw [hconst]

/-- Marcinkiewicz truncation bound for a subadditive operator, with all operator hypotheses
required only on `MemLp` inputs.  Same conclusion as
`Work.BourgainPlan.Maximal.two_weak_truncation_bound`, but the strong `L^q`/`L^{p₀}` bounds
(hence, by Chebyshev–Markov, the weak `(q,q)`/`(p₀,p₀)` bounds) and the a.e.-measurability of
`T f` are available only for `MemLp` inputs; the subadditivity is moreover required only on
*pairs of* `L^p` functions.  The truncations `hi = f·1_{σλ < ‖f‖}` and `lo = f·1_{‖f‖ ≤ σλ}` of an
`L^p` function are again `L^p` (dominated by `‖f‖`), `hi` lies in `L^q` and `lo` in `L^{p₀}`
(hence `T hi`, `T lo` are a.e.-measurable), so all hypotheses apply to them. -/
theorem two_weak_truncation_bound_memLp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    (T : (α → ℂ) → (β → ENNReal))
    {q p₀ p A B : ℝ} (hq : 0 < q) (hp₀ : 0 < p₀) (hqp : q < p) (hpp : p < p₀)
    (hA : 0 < A) (hB : 0 < B)
    (hsub : ∀ f h : α → ℂ, MeasureTheory.MemLp f (ENNReal.ofReal p) μ →
      MeasureTheory.MemLp h (ENNReal.ofReal p) μ → ∀ x : β, T (f + h) x ≤ T f x + T h x)
    (hmeas : ∀ f : α → ℂ, MeasureTheory.MemLp f (ENNReal.ofReal p) μ →
      AEMeasurable (T f) ν)
    (hqbd : ∀ f : α → ℂ, MeasureTheory.MemLp f (ENNReal.ofReal q) μ →
      MeasureTheory.eLpNorm (T f) (ENNReal.ofReal q) ν
        ≤ ENNReal.ofReal A * MeasureTheory.eLpNorm f (ENNReal.ofReal q) μ)
    (hpbd : ∀ f : α → ℂ, MeasureTheory.MemLp f (ENNReal.ofReal p₀) μ →
      MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p₀) ν
        ≤ ENNReal.ofReal B * MeasureTheory.eLpNorm f (ENNReal.ofReal p₀) μ)
    (f : α → ℂ) (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) μ)
    {lam σ : ℝ} (hlam : 0 < lam) (hσ : 0 < σ) :
    ν {x : β | ENNReal.ofReal lam < T f x}
      ≤ ENNReal.ofReal (2 * A / lam) ^ q *
          MeasureTheory.lintegral μ
            (fun x => Set.indicator {x : α | σ * lam < ‖f x‖}
              (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x)
        + ENNReal.ofReal (2 * B / lam) ^ p₀ *
          MeasureTheory.lintegral μ
            (fun x => Set.indicator {x : α | ‖f x‖ ≤ σ * lam}
              (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x) := by
  have hp : 0 < p := lt_trans hq hqp
  have hc : 0 < σ * lam := mul_pos hσ hlam
  set S : Set α := {x : α | σ * lam < ‖f x‖} with hS
  have hSnull : NullMeasurableSet S μ := by
    rw [hS]
    exact nullMeasurableSet_lt (f := fun _ : α => σ * lam) (g := fun x => ‖f x‖)
      aemeasurable_const hf.aestronglyMeasurable.norm.aemeasurable
  set S' : Set α := {x : α | ‖f x‖ ≤ σ * lam} with hS'
  have hSc : S' = Sᶜ := by
    rw [hS', hS]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    exact not_lt.symm
  have hS'null : NullMeasurableSet S' μ := by rw [hSc]; exact hSnull.compl
  set hi : α → ℂ := S.indicator f with hhi
  set lo : α → ℂ := S'.indicator f with hlo
  have hsum : hi + lo = f := by
    rw [hhi, hlo, hSc]
    exact Commons.Analysis.MeasureTheory.banach_indicator_add_compl f
  have hhi_p : MeasureTheory.MemLp hi (ENNReal.ofReal p) μ := by
    rw [hhi]
    exact memLp_indicator_of_nullMeasurableSet hf hSnull
  have hlo_p : MeasureTheory.MemLp lo (ENNReal.ofReal p) μ := by
    rw [hlo]
    exact memLp_indicator_of_nullMeasurableSet hf hS'null
  have hhi_q : MeasureTheory.MemLp hi (ENNReal.ofReal q) μ := by
    rw [hhi, hS]
    exact memLp_indicator_high (r := q) (s := p) (c := σ * lam) hq hqp hc hf
  have hlo_p0 : MeasureTheory.MemLp lo (ENNReal.ofReal p₀) μ := by
    rw [hlo, hSc, hS]
    exact memLp_indicator_low (r := p₀) (s := p) (c := σ * lam) hp hpp hc hf
  have hweakq := weak_of_strong_memLp (T := T) (r := q) (p := p) hq hmeas hA hqbd
  have hweakp := weak_of_strong_memLp (T := T) (r := p₀) (p := p) hp₀ hmeas hB hpbd
  have hHeq : (MeasureTheory.eLpNorm hi (ENNReal.ofReal q) μ) ^ q
      = ∫⁻ x, Set.indicator S (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x ∂μ := by
    rw [hhi]
    exact eLpNorm_indicator_rpow_eq f S hq hhi_p.aestronglyMeasurable
  have hGeq : (MeasureTheory.eLpNorm lo (ENNReal.ofReal p₀) μ) ^ p₀
      = ∫⁻ x, Set.indicator S' (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x ∂μ := by
    rw [hlo]
    exact eLpNorm_indicator_rpow_eq f S' hp₀ hlo_p.aestronglyMeasurable
  have termh : ν {x : β | ENNReal.ofReal (lam / 2) < T hi x}
      ≤ ENNReal.ofReal (2 * A / lam) ^ q *
          ∫⁻ x, Set.indicator S (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x ∂μ := by
    calc ν {x : β | ENNReal.ofReal (lam / 2) < T hi x}
        ≤ ENNReal.ofReal (A / (lam / 2)) ^ q
            * (MeasureTheory.eLpNorm hi (ENNReal.ofReal q) μ) ^ q :=
          hweakq hi hhi_q hhi_p (lam / 2) (by linarith)
      _ = ENNReal.ofReal (2 * A / lam) ^ q
            * (MeasureTheory.eLpNorm hi (ENNReal.ofReal q) μ) ^ q := by
          rw [show A / (lam / 2) = 2 * A / lam by field_simp]
      _ = ENNReal.ofReal (2 * A / lam) ^ q *
            ∫⁻ x, Set.indicator S (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x ∂μ := by
          rw [hHeq]
  have termp : ν {x : β | ENNReal.ofReal (lam / 2) < T lo x}
      ≤ ENNReal.ofReal (2 * B / lam) ^ p₀ *
          ∫⁻ x, Set.indicator S' (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x ∂μ := by
    calc ν {x : β | ENNReal.ofReal (lam / 2) < T lo x}
        ≤ ENNReal.ofReal (B / (lam / 2)) ^ p₀
            * (MeasureTheory.eLpNorm lo (ENNReal.ofReal p₀) μ) ^ p₀ :=
          hweakp lo hlo_p0 hlo_p (lam / 2) (by linarith)
      _ = ENNReal.ofReal (2 * B / lam) ^ p₀
            * (MeasureTheory.eLpNorm lo (ENNReal.ofReal p₀) μ) ^ p₀ := by
          rw [show B / (lam / 2) = 2 * B / lam by field_simp]
      _ = ENNReal.ofReal (2 * B / lam) ^ p₀ *
            ∫⁻ x, Set.indicator S' (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x ∂μ := by
          rw [hGeq]
  have hsubset : {x : β | ENNReal.ofReal lam < T f x} ⊆
      {x : β | ENNReal.ofReal (lam / 2) < T hi x} ∪
        {x : β | ENNReal.ofReal (lam / 2) < T lo x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
    by_contra hcon
    rw [not_or] at hcon
    have hsum' : T f x ≤ T hi x + T lo x := by
      have h1 := hsub hi lo hhi_p hlo_p x
      rwa [hsum] at h1
    have hle : T f x ≤ ENNReal.ofReal (lam / 2) + ENNReal.ofReal (lam / 2) :=
      hsum'.trans (add_le_add (not_lt.mp hcon.1) (not_lt.mp hcon.2))
    rw [← ENNReal.ofReal_add (by linarith) (by linarith),
      show lam / 2 + lam / 2 = lam by ring] at hle
    exact absurd hle (not_le.mpr hx)
  calc ν {x : β | ENNReal.ofReal lam < T f x}
      ≤ ν ({x : β | ENNReal.ofReal (lam / 2) < T hi x} ∪
            {x : β | ENNReal.ofReal (lam / 2) < T lo x}) := measure_mono hsubset
    _ ≤ ν {x : β | ENNReal.ofReal (lam / 2) < T hi x} +
          ν {x : β | ENNReal.ofReal (lam / 2) < T lo x} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * A / lam) ^ q *
          ∫⁻ x, Set.indicator S (fun x => ENNReal.ofReal (‖f x‖ ^ q)) x ∂μ
        + ENNReal.ofReal (2 * B / lam) ^ p₀ *
          ∫⁻ x, Set.indicator S' (fun x => ENNReal.ofReal (‖f x‖ ^ p₀)) x ∂μ :=
        add_le_add termh termp

end Work.BourgainPlan.Maximal
