import Mathlib
import Submission.Commons.Analysis.Abel.continuousOn_abel_K
import Submission.Commons.Analysis.Abel.volterra_double_integral

/-!
# A bound for the derivative of an Abel transform

Let `g : ℝ → ℝ` be `η`-Lipschitz on `[c, b₀]` and vanish above `b₀` (`b₀ ≤ 1`).  This file
bounds the derivative of its Abel transform

`F u = ∫_v u..1, g v / √(v - u)`

on `[d, 1]` (where `c < d ≤ b₀`) by `10 * √(b₀ - c + 1) * η`.

The proof goes through the substitution `v = u + (b₀-u) t²`, which turns the Abel transform into
its "normalised" form

`F u = 2 * √(b₀-u) * abelR g b₀ u`,  `abelR g b u = ∫_t 0..1, g (u + (b-u) t²)`,

whose first factor is smooth and whose second factor `abelR g b₀` is Lipschitz on `[c, b₀]`
**without any differentiability assumption on `g`**: pointwise Lipschitzness of `g` gives
`|abelR g b u - abelR g b s| ≤ (2/3) η |u - s|` and the estimate `|abelR g b u| ≤ (2/3) η (b - u)`.
The elementary inequality `(√x - √y) * y ≤ (x - y) * √x` (for `0 ≤ y ≤ x`) then controls the
product `2√(b-u) * abelR g b u`, giving the Lipschitz bound `|F u - F s| ≤ (8/3) η √(b-c) |u-s|`
on `[c, ∞)`.  Feeding it to `norm_fderiv_le_of_lipschitzOn` bounds `deriv F s` (this covers the
non-differentiable case as well, since `fderiv` is then `0`).
-/

open scoped Interval Topology
open Set Filter MeasureTheory

namespace Work.OddVolterra.Existence

noncomputable section

/-- The Abel transform `u ↦ ∫_u^1 g v / √(v - u) dv`. -/
def abelF (g : ℝ → ℝ) (u : ℝ) : ℝ := ∫ v in u..(1 : ℝ), g v / Real.sqrt (v - u)

/-- The normalised Abel transform `u ↦ ∫_0^1 g (u + (b-u) t²) dt`. -/
def abelR (g : ℝ → ℝ) (b u : ℝ) : ℝ := ∫ t in (0 : ℝ)..(1 : ℝ), g (u + (b - u) * t ^ 2)

private lemma integral_one_sub_sq : ∫ t in (0 : ℝ)..(1 : ℝ), (1 - t ^ 2) = 2 / 3 := by
  have h1 : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume (0:ℝ) 1 := intervalIntegrable_const
  have h2 : IntervalIntegrable (fun t : ℝ => t^2) volume (0:ℝ) 1 :=
    (continuous_id.pow 2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun t : ℝ => t ^ 2) h1 h2]
  simp
  norm_num

private lemma mapsTo_of_mem_Icc {c b pu : ℝ} (hpu : pu ∈ Set.Icc c b) :
    MapsTo (fun t : ℝ => pu + (b - pu) * t ^ 2) (Set.uIcc (0:ℝ) 1) (Set.Icc c b) := by
  intro t ht
  have h01 : ((0:ℝ) ≤ 1) := by norm_num
  rw [Set.uIcc_of_le h01] at ht
  have hb : 0 ≤ b - pu := sub_nonneg.mpr hpu.2
  have hsq1 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  constructor
  · have : 0 ≤ (b - pu) * t ^ 2 := mul_nonneg hb (sq_nonneg t)
    linarith [hpu.1]
  · have : (b - pu) * t ^ 2 ≤ (b - pu) * 1 := mul_le_mul_of_nonneg_left hsq1 hb
    linarith

/-- `abelR g b` is `(2/3)η`-Lipschitz on `[c, b]` as soon as `g` is `η`-Lipschitz there.
No differentiability of `g` is used: the estimate is the pointwise Lipschitz bound integrated
against `1 - t²`. -/
lemma abelR_sub_le {c b η : ℝ} {g : ℝ → ℝ}
    (hgcont : ContinuousOn g (Set.Icc c b))
    (hlip : ∀ u ∈ Set.Icc c b, ∀ v ∈ Set.Icc c b, |g u - g v| ≤ η * |u - v|)
    {pu ps : ℝ} (hpu : pu ∈ Set.Icc c b) (hps : ps ∈ Set.Icc c b) :
    |abelR g b pu - abelR g b ps| ≤ (2/3) * η * |pu - ps| := by
  have h01 : ((0:ℝ) ≤ 1) := by norm_num
  have hcontu : ContinuousOn (fun t : ℝ => g (pu + (b - pu) * t ^ 2)) (Set.uIcc (0:ℝ) 1) :=
    hgcont.comp (by fun_prop) (mapsTo_of_mem_Icc hpu)
  have hconts : ContinuousOn (fun t : ℝ => g (ps + (b - ps) * t ^ 2)) (Set.uIcc (0:ℝ) 1) :=
    hgcont.comp (by fun_prop) (mapsTo_of_mem_Icc hps)
  have hintu : IntervalIntegrable (fun t : ℝ => g (pu + (b - pu) * t ^ 2)) volume (0:ℝ) 1 :=
    hcontu.intervalIntegrable
  have hints : IntervalIntegrable (fun t : ℝ => g (ps + (b - ps) * t ^ 2)) volume (0:ℝ) 1 :=
    hconts.intervalIntegrable
  have hsub : abelR g b pu - abelR g b ps =
      ∫ t in (0:ℝ)..1, (g (pu + (b - pu) * t ^ 2) - g (ps + (b - ps) * t ^ 2)) := by
    rw [abelR, abelR, ← intervalIntegral.integral_sub hintu hints]
  have hneg : IntervalIntegrable
      (fun t : ℝ => |g (pu + (b - pu) * t ^ 2) - g (ps + (b - ps) * t ^ 2)|) volume (0:ℝ) 1 :=
    (hcontu.sub hconts).abs.intervalIntegrable
  have hboundint : IntervalIntegrable (fun t : ℝ => η * |pu - ps| * (1 - t ^ 2)) volume (0:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  calc |abelR g b pu - abelR g b ps|
      = |∫ t in (0:ℝ)..1, (g (pu + (b - pu) * t ^ 2) - g (ps + (b - ps) * t ^ 2))| := by
        rw [hsub]
    _ ≤ ∫ t in (0:ℝ)..1, |g (pu + (b - pu) * t ^ 2) - g (ps + (b - ps) * t ^ 2)| :=
        intervalIntegral.abs_integral_le_integral_abs h01
    _ ≤ ∫ t in (0:ℝ)..1, η * |pu - ps| * (1 - t ^ 2) := by
        refine intervalIntegral.integral_mono_on h01 hneg hboundint (fun t ht => ?_)
        have htu : pu + (b - pu) * t ^ 2 ∈ Set.Icc c b :=
          mapsTo_of_mem_Icc hpu (by rw [Set.uIcc_of_le h01]; exact ht)
        have hts : ps + (b - ps) * t ^ 2 ∈ Set.Icc c b :=
          mapsTo_of_mem_Icc hps (by rw [Set.uIcc_of_le h01]; exact ht)
        have hdiff : (pu + (b - pu) * t ^ 2) - (ps + (b - ps) * t ^ 2) = (pu - ps) * (1 - t ^ 2) := by
          ring
        have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
        calc |g (pu + (b - pu) * t ^ 2) - g (ps + (b - ps) * t ^ 2)|
            ≤ η * |(pu + (b - pu) * t ^ 2) - (ps + (b - ps) * t ^ 2)| := hlip _ htu _ hts
          _ = η * |pu - ps| * (1 - t ^ 2) := by
              rw [hdiff, abs_mul, abs_of_nonneg h0]; ring
    _ = (2/3) * η * |pu - ps| := by
        rw [intervalIntegral.integral_const_mul, integral_one_sub_sq]
        ring

/-- If `g` is `η`-Lipschitz on `[c,b]` and vanishes at `b`, then
`|abelR g b u| ≤ (2/3) η (b - u)` for `u ∈ [c,b]`. -/
lemma abelR_abs_le {c b η : ℝ} {g : ℝ → ℝ} (hzero : ∀ v : ℝ, b ≤ v → g v = 0)
    (hgcont : ContinuousOn g (Set.Icc c b))
    (hlip : ∀ u ∈ Set.Icc c b, ∀ v ∈ Set.Icc c b, |g u - g v| ≤ η * |u - v|)
    {pu : ℝ} (hpu : pu ∈ Set.Icc c b) :
    |abelR g b pu| ≤ (2/3) * η * (b - pu) := by
  have h01 : ((0:ℝ) ≤ 1) := by norm_num
  have hcontu : ContinuousOn (fun t : ℝ => g (pu + (b - pu) * t ^ 2)) (Set.uIcc (0:ℝ) 1) :=
    hgcont.comp (by fun_prop) (mapsTo_of_mem_Icc hpu)
  have hintu : IntervalIntegrable (fun t : ℝ => g (pu + (b - pu) * t ^ 2)) volume (0:ℝ) 1 :=
    hcontu.intervalIntegrable
  have hneg : IntervalIntegrable
      (fun t : ℝ => |g (pu + (b - pu) * t ^ 2)|) volume (0:ℝ) 1 :=
    hcontu.abs.intervalIntegrable
  have hboundint : IntervalIntegrable (fun t : ℝ => η * (b - pu) * (1 - t ^ 2)) volume (0:ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  calc |abelR g b pu| = |∫ t in (0:ℝ)..1, g (pu + (b - pu) * t ^ 2)| := by rw [abelR]
    _ ≤ ∫ t in (0:ℝ)..1, |g (pu + (b - pu) * t ^ 2)| :=
        intervalIntegral.abs_integral_le_integral_abs h01
    _ ≤ ∫ t in (0:ℝ)..1, η * (b - pu) * (1 - t ^ 2) := by
        refine intervalIntegral.integral_mono_on h01 hneg hboundint (fun t ht => ?_)
        have ht' : t ∈ Set.Icc (0:ℝ) 1 := ht
        have htu : pu + (b - pu) * t ^ 2 ∈ Set.Icc c b := mapsTo_of_mem_Icc hpu (by rw [Set.uIcc_of_le h01]; exact ht')
        have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht'.1, ht'.2]
        have hbdiff : (pu + (b - pu) * t ^ 2) - b = -(b - pu) * (1 - t ^ 2) := by ring
        calc |g (pu + (b - pu) * t ^ 2)|
            = |g (pu + (b - pu) * t ^ 2) - g b| := by rw [hzero b le_rfl, sub_zero]
          _ ≤ η * |(pu + (b - pu) * t ^ 2) - b| := hlip _ htu _ ⟨hpu.1.trans hpu.2, le_rfl⟩
          _ = η * (b - pu) * (1 - t ^ 2) := by
              rw [hbdiff, abs_mul, abs_neg, abs_of_nonneg h0, abs_of_nonneg (sub_nonneg.mpr hpu.2)]
              ring
    _ = (2/3) * η * (b - pu) := by
        rw [intervalIntegral.integral_const_mul, integral_one_sub_sq]
        ring

/-- The Abel transform of a function vanishing above `b` is zero to the right of `b`. -/
lemma abelF_eq_zero_of_le {b : ℝ} (hb1 : b ≤ 1) {g : ℝ → ℝ}
    (hzero : ∀ v : ℝ, b ≤ v → g v = 0) {pu : ℝ} (hpu : b ≤ pu) : abelF g pu = 0 := by
  rw [abelF]
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0:ℝ)) (fun v hv => ?_)]
  · simp
  have hv1 : b ≤ v := by
    rcases le_total pu 1 with h | h
    · rw [Set.uIcc_of_le h] at hv; exact le_trans hpu hv.1
    · rw [Set.uIcc_of_ge h] at hv; exact le_trans hb1 hv.1
  rw [hzero v hv1]
  simp

/-- The substitution `v = u + (b-u) t²` expressing the Abel transform of a function vanishing
above `b` through its normalised form: `abelF g u = 2√(b-u) * abelR g b u` for `u ≤ b`. -/
lemma abelF_eq_abelR {c b : ℝ} (hb1 : b ≤ 1) {g : ℝ → ℝ}
    (hzero : ∀ v : ℝ, b ≤ v → g v = 0)
    (hgcont : ContinuousOn g (Set.Icc c b)) {pu : ℝ} (hpu : pu ∈ Set.Icc c b) :
    abelF g pu = 2 * Real.sqrt (b - pu) * abelR g b pu := by
  rcases lt_or_eq_of_le hpu.2 with hlt | heq
  · have hgcont' : ContinuousOn g (Set.uIcc pu b) := by
      rw [Set.uIcc_of_le hlt.le]
      exact hgcont.mono (fun v hv => ⟨hpu.1.trans hv.1, hv.2⟩)
    have hbase : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - pu))⁻¹) volume pu b :=
      Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub hlt
    have h1' : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - pu))⁻¹ • g v) volume pu b :=
      hbase.smul_continuousOn hgcont'
    have h1 : IntervalIntegrable (fun v : ℝ => g v / Real.sqrt (v - pu)) volume pu b :=
      h1'.congr (fun v _ => by simp [div_eq_mul_inv, mul_comm])
    have hvanish : Set.EqOn (fun _ : ℝ => (0:ℝ)) (fun v : ℝ => g v / Real.sqrt (v - pu))
        (Set.uIoc b 1) := by
      intro v hv
      rw [Set.uIoc_of_le hb1] at hv
      change (0:ℝ) = g v / Real.sqrt (v - pu)
      rw [hzero v hv.1.le]
      simp
    have h2 : IntervalIntegrable (fun v : ℝ => g v / Real.sqrt (v - pu)) volume b 1 :=
      IntervalIntegrable.congr hvanish intervalIntegrable_const
    have hsplit : (∫ v in pu..(1:ℝ), g v / Real.sqrt (v - pu))
        = (∫ v in pu..b, g v / Real.sqrt (v - pu)) + (∫ v in b..1, g v / Real.sqrt (v - pu)) :=
      (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
    have htail : (∫ v in b..1, g v / Real.sqrt (v - pu)) = 0 := by
      have hc : (∫ v in b..1, g v / Real.sqrt (v - pu)) = ∫ v in b..1, (0 : ℝ) :=
        intervalIntegral.integral_congr (fun v hv => by
          rw [Set.uIcc_of_le hb1] at hv
          rw [hzero v hv.1]
          simp)
      rw [hc, intervalIntegral.integral_zero]
    have hsub := Commons.Analysis.Abel.intervalIntegral_abel_subst (E := ℝ) (x := pu) (b := b)
      hlt.le (fun _ σ => g σ)
    have hcongr : (∫ v in pu..b, (Real.sqrt (v - pu))⁻¹ • g v)
        = ∫ v in pu..b, g v / Real.sqrt (v - pu) :=
      intervalIntegral.integral_congr (fun v _ => by simp [div_eq_mul_inv, mul_comm])
    calc abelF g pu = ∫ v in pu..(1:ℝ), g v / Real.sqrt (v - pu) := rfl
      _ = (∫ v in pu..b, g v / Real.sqrt (v - pu)) + (∫ v in b..1, g v / Real.sqrt (v - pu)) := hsplit
      _ = ∫ v in pu..b, g v / Real.sqrt (v - pu) := by rw [htail, add_zero]
      _ = ∫ v in pu..b, (Real.sqrt (v - pu))⁻¹ • g v := hcongr.symm
      _ = 2 * Real.sqrt (b - pu) * abelR g b pu := by
          rw [hsub]
          simp [abelR, smul_eq_mul]
  · rw [heq, abelF_eq_zero_of_le hb1 hzero le_rfl]
    simp

private lemma abelF_lip_ordered {c b η : ℝ} (_hcb : c ≤ b) (hb1 : b ≤ 1) (hη : 0 ≤ η)
    {g : ℝ → ℝ} (hzero : ∀ v : ℝ, b ≤ v → g v = 0)
    (hgcont : ContinuousOn g (Set.Icc c b))
    (hlip : ∀ u ∈ Set.Icc c b, ∀ v ∈ Set.Icc c b, |g u - g v| ≤ η * |u - v|)
    {u s : ℝ} (hu : c ≤ u) (hs : c ≤ s) (hle : u ≤ s) :
    |abelF g u - abelF g s| ≤ (8/3) * η * Real.sqrt (b - c) * |u - s| := by
  have hS0 : 0 ≤ Real.sqrt (b - c) := Real.sqrt_nonneg _
  have habs : |u - s| = s - u := by
    rw [abs_of_nonpos (show u - s ≤ 0 by linarith)]
    ring
  have hsu0 : 0 ≤ s - u := sub_nonneg.mpr hle
  rcases lt_or_ge b u with hbu | hbu
  · have hbs : b ≤ s := le_trans hbu.le hle
    rw [abelF_eq_zero_of_le hb1 hzero hbu.le, abelF_eq_zero_of_le hb1 hzero hbs, sub_zero, abs_zero]
    positivity
  · by_cases hbs : b ≤ s
    · -- mixed case `u < b ≤ s`
      have huI : u ∈ Set.Icc c b := ⟨hu, hbu⟩
      have hRu := abelR_abs_le hzero hgcont hlip huI
      have hA0 : 0 ≤ Real.sqrt (b - u) := Real.sqrt_nonneg _
      have hA_le : Real.sqrt (b - u) ≤ Real.sqrt (b - c) := Real.sqrt_le_sqrt (by linarith)
      have hbu_le : b - u ≤ s - u := by linarith
      have hbu0 : 0 ≤ b - u := by linarith
      have hfac : 0 ≤ (4/3) * η * (b - u) := by positivity
      rw [abelF_eq_abelR hb1 hzero hgcont huI, abelF_eq_zero_of_le hb1 hzero hbs, sub_zero, habs]
      calc |2 * Real.sqrt (b - u) * abelR g b u|
          = 2 * Real.sqrt (b - u) * |abelR g b u| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hA0]
        _ ≤ 2 * Real.sqrt (b - u) * ((2/3) * η * (b - u)) :=
            mul_le_mul_of_nonneg_left hRu (by positivity)
        _ = (4/3) * η * (b - u) * Real.sqrt (b - u) := by ring
        _ ≤ (4/3) * η * (b - u) * Real.sqrt (b - c) :=
            mul_le_mul_of_nonneg_left hA_le hfac
        _ ≤ (4/3) * η * (s - u) * Real.sqrt (b - c) :=
            mul_le_mul_of_nonneg_right (by nlinarith [hη, hbu_le]) hS0
        _ ≤ (8/3) * η * Real.sqrt (b - c) * (s - u) := by
            have hprod : 0 ≤ η * Real.sqrt (b - c) * (s - u) :=
              mul_nonneg (mul_nonneg hη hS0) hsu0
            nlinarith [hprod]
    · -- case `u ≤ s < b`
      push Not at hbs
      have huI : u ∈ Set.Icc c b := ⟨hu, hbu⟩
      have hsI : s ∈ Set.Icc c b := ⟨hs, hbs.le⟩
      rw [abelF_eq_abelR hb1 hzero hgcont huI, abelF_eq_abelR hb1 hzero hgcont hsI]
      set A := Real.sqrt (b - u) with hAdef
      set B := Real.sqrt (b - s) with hBdef
      set Ru := abelR g b u with hRudef
      set Rs := abelR g b s with hRsdef
      have hA0 : 0 ≤ A := by rw [hAdef]; exact Real.sqrt_nonneg _
      have hB0 : 0 ≤ B := by rw [hBdef]; exact Real.sqrt_nonneg _
      have hBA : B ≤ A := by
        rw [hAdef, hBdef]; exact Real.sqrt_le_sqrt (by linarith)
      have hA2 : A ^ 2 = b - u := by rw [hAdef]; exact Real.sq_sqrt (by linarith [hbu])
      have hB2 : B ^ 2 = b - s := by rw [hBdef]; exact Real.sq_sqrt (by linarith [hbs.le])
      have hA_le : A ≤ Real.sqrt (b - c) := by
        rw [hAdef]; exact Real.sqrt_le_sqrt (by linarith)
      have hRu : |Ru - Rs| ≤ (2/3) * η * (s - u) := by
        have h := abelR_sub_le hgcont hlip huI hsI
        rw [abs_of_nonpos (show u - s ≤ 0 by linarith)] at h
        simpa [hRudef, hRsdef] using h
      have hRs : |Rs| ≤ (2/3) * η * (b - s) := by
        have h := abelR_abs_le hzero hgcont hlip hsI
        simpa [hRsdef] using h
      have hkey : (A - B) * (b - s) ≤ (s - u) * A := by
        have hstep : (A - B) * B ^ 2 ≤ (A ^ 2 - B ^ 2) * A := by
          have h1 : 0 ≤ A - B := by linarith
          have h3 : 0 ≤ A ^ 2 + A * B - B ^ 2 := by nlinarith [hA0, hB0, hBA]
          have h4 : 0 ≤ (A - B) * (A ^ 2 + A * B - B ^ 2) := mul_nonneg h1 h3
          nlinarith [h4]
        have hsub : A ^ 2 - B ^ 2 = s - u := by rw [hA2, hB2]; ring
        rw [hsub, hB2] at hstep
        exact hstep
      have hsplit1 : |A * Ru - B * Rs| ≤ A * |Ru - Rs| + (A - B) * |Rs| := by
        have h : A * Ru - B * Rs = A * (Ru - Rs) + (A - B) * Rs := by ring
        rw [h]
        refine le_trans (abs_add_le _ _) (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg (sub_nonneg.mpr hBA)]
      rw [habs]
      calc |2 * A * Ru - 2 * B * Rs| = 2 * |A * Ru - B * Rs| := by
            rw [show 2 * A * Ru - 2 * B * Rs = 2 * (A * Ru - B * Rs) by ring, abs_mul,
              abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        _ ≤ 2 * (A * |Ru - Rs| + (A - B) * |Rs|) :=
            mul_le_mul_of_nonneg_left hsplit1 (by norm_num)
        _ ≤ 2 * ((2/3) * η * (s - u) * Real.sqrt (b - c) +
              (2/3) * η * (s - u) * Real.sqrt (b - c)) := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
            · calc A * |Ru - Rs| ≤ A * ((2/3) * η * (s - u)) :=
                    mul_le_mul_of_nonneg_left hRu hA0
                _ = (2/3) * η * (s - u) * A := by ring
                _ ≤ (2/3) * η * (s - u) * Real.sqrt (b - c) :=
                    mul_le_mul_of_nonneg_left hA_le (by nlinarith [hη, hsu0])
            · calc (A - B) * |Rs| ≤ (A - B) * ((2/3) * η * (b - s)) :=
                    mul_le_mul_of_nonneg_left hRs (sub_nonneg.mpr hBA)
                _ = (2/3) * η * ((A - B) * (b - s)) := by ring
                _ ≤ (2/3) * η * ((s - u) * A) :=
                    mul_le_mul_of_nonneg_left hkey (by nlinarith [hη])
                _ = (2/3) * η * (s - u) * A := by ring
                _ ≤ (2/3) * η * (s - u) * Real.sqrt (b - c) :=
                    mul_le_mul_of_nonneg_left hA_le (by nlinarith [hη, hsu0])
        _ ≤ (8/3) * η * Real.sqrt (b - c) * (s - u) := by
            have hprod : 0 ≤ η * Real.sqrt (b - c) * (s - u) :=
              mul_nonneg (mul_nonneg hη hS0) hsu0
            nlinarith [hprod]

/-- The Abel transform of an `η`-Lipschitz function vanishing above `b` is Lipschitz with
constant `10 * √(b - c + 1) * η` on `[c, ∞)`. -/
lemma abelF_lipschitz {c b η : ℝ} (hcb : c ≤ b) (hb1 : b ≤ 1) (hη : 0 ≤ η)
    {g : ℝ → ℝ} (hzero : ∀ v : ℝ, b ≤ v → g v = 0)
    (hgcont : ContinuousOn g (Set.Icc c b))
    (hlip : ∀ u ∈ Set.Icc c b, ∀ v ∈ Set.Icc c b, |g u - g v| ≤ η * |u - v|) :
    ∀ u ∈ Set.Ici c, ∀ s ∈ Set.Ici c,
      |abelF g u - abelF g s| ≤ 10 * Real.sqrt (b - c + 1) * η * |u - s| := by
  intro u hu s hs
  have hmid : |abelF g u - abelF g s| ≤ (8/3) * η * Real.sqrt (b - c) * |u - s| := by
    rcases le_total u s with h | h
    · exact abelF_lip_ordered hcb hb1 hη hzero hgcont hlip hu hs h
    · rw [abs_sub_comm (abelF g u) (abelF g s), abs_sub_comm u s]
      exact abelF_lip_ordered hcb hb1 hη hzero hgcont hlip hs hu h
  refine le_trans hmid ?_
  have hS0 : 0 ≤ Real.sqrt (b - c) := Real.sqrt_nonneg _
  have hS1 : Real.sqrt (b - c) ≤ Real.sqrt (b - c + 1) := Real.sqrt_le_sqrt (by linarith)
  have hstep1 : (8/3) * Real.sqrt (b - c) ≤ 10 * Real.sqrt (b - c + 1) := by
    nlinarith [hS1, hS0]
  have hstep2 : 0 ≤ η * |u - s| := mul_nonneg hη (abs_nonneg _)
  calc (8/3) * η * Real.sqrt (b - c) * |u - s|
      = ((8/3) * Real.sqrt (b - c)) * (η * |u - s|) := by ring
    _ ≤ (10 * Real.sqrt (b - c + 1)) * (η * |u - s|) :=
        mul_le_mul_of_nonneg_right hstep1 hstep2
    _ = 10 * Real.sqrt (b - c + 1) * η * |u - s| := by ring

theorem abel_deriv_bound {c d b₀ η : ℝ} (hcd : c < d) (hdb : d ≤ b₀) (hb₁ : b₀ ≤ 1)
    (hη : 0 ≤ η) {g : ℝ → ℝ} (hzero : ∀ v : ℝ, b₀ ≤ v → g v = 0)
    (hlip : ∀ u ∈ Set.Icc c b₀, ∀ v ∈ Set.Icc c b₀, |g u - g v| ≤ η * |u - v|) :
    ∀ s ∈ Set.Icc d 1,
      |deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), g v / Real.sqrt (v - u)) s|
        ≤ 10 * Real.sqrt (b₀ - c + 1) * η := by
  have hcb : c ≤ b₀ := le_trans hcd.le hdb
  have hlipOn : LipschitzOnWith (NNReal.mk η hη) g (Set.Icc c b₀) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq]
    exact hlip x hx y hy
  have hgcont : ContinuousOn g (Set.Icc c b₀) := hlipOn.continuousOn
  have hK0 : 0 ≤ 10 * Real.sqrt (b₀ - c + 1) * η := by
    have := Real.sqrt_nonneg (b₀ - c + 1); positivity
  intro s hs
  have hcs : c < s := lt_of_lt_of_le hcd hs.1
  have hs_nhds : Set.Ici c ∈ 𝓝 s := Ici_mem_nhds hcs
  have hlipF : LipschitzOnWith (NNReal.mk (10 * Real.sqrt (b₀ - c + 1) * η) hK0) (abelF g) (Set.Ici c) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq]
    exact abelF_lipschitz hcb hb₁ hη hzero hgcont hlip x hx y hy
  have hbound := norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) hs_nhds hlipF
  have hderiv : deriv (fun u : ℝ => ∫ v in u..(1 : ℝ), g v / Real.sqrt (v - u)) s
      = deriv (abelF g) s := rfl
  rw [hderiv]
  calc |deriv (abelF g) s| = ‖(fderiv ℝ (abelF g) s) 1‖ := by
        rw [fderiv_apply_one_eq_deriv, Real.norm_eq_abs]
    _ ≤ ‖fderiv ℝ (abelF g) s‖ * ‖(1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (abelF g) s‖ := by simp
    _ ≤ 10 * Real.sqrt (b₀ - c + 1) * η := by
        simpa using hbound


end

end Work.OddVolterra.Existence
