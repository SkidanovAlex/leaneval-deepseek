/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The one-dimensional tail bound `TailOneD`

The truncation `uTr N b u = phiTr N · Gc N b u` has the moving-integral tail

`tailE N b f t θ = e^{bt} ∫_t^{2N} e^{-bs} (deriv (chi N)) s · f s θ ds`

(see `Submission/Work/FTS/EllSol/ShiftFT/uTrAthree/Defs.lean`).  `TailOneD` is the estimate
of the square of that tail, averaged over `t ∈ [-(8192 N), 2 N]`, against the angular
`L²` norm of the `θ`-slice: the hypothesis is that the kernel `k = deriv (chi N)` obeys
`|k s| ≤ c / N` and vanishes for `|s| ≥ 2 N` (which is how `deriv (Trunc.chi N)` behaves).

The proof is the elementary Cauchy–Schwarz estimate with the sharp weight cancellation:

* the inner integral is over `s ∈ [t, 2N]`, where `e^{-b s} ≤ e^{-b t}` (as `b ≥ 0`), so the
  factor `e^{b t}` in front of it cancels exactly the exponential of `e^{-bs}`;
* since `|k s| ≤ c / N`, the remaining kernel is `≤ c/N` times the constant weight `1`, so
  `(e^{bt} ∫_t^{2N} ⋯)² ≤ (c/N)² · |[t,2N] ∩ [-2N,2N]| · ∫_{[-2N,2N]} g²` — this is
  Cauchy–Schwarz for the pairing `(k, g)` on the interval where `k` can be nonzero, in the
  form valid for *arbitrary* functions (no measurability is assumed, and the range of `t`
  below `-2N` is handled by the fact that the kernel vanishes there, i.e. by replacing `g`
  with `g · 1_{[-2N,2N]}` inside the `lintegral`).
* the length factors sum to `8194 N · 4 N / N² = 32776 < 40000`.

Since everything is stated with the outer (Lebesgue) integral `∫⁻` of `ℝ≥0∞`-valued
functions, *no* measurability or integrability hypothesis on `g` is needed: the pointwise
Cauchy–Schwarz on the interval integral is proved unconditionally (`ofReal_integral_sq_le`),
and the `lintegral` Cauchy–Schwarz `lintegral_sq_le` is proved for arbitrary `ℝ≥0∞`-valued
functions by reducing to measurable majorants
(`iSup_lintegral_measurable_le_eq_lintegral`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAthree

open MeasureTheory Set
open scoped Real Topology ENNReal

/-- `ENNReal.ofReal` of a nonnegative Bochner integral is at most the `lintegral` of the
`ofReal`s (for an arbitrary, possibly non-measurable, function). -/
private theorem ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h hf]
  · rw [MeasureTheory.integral_undef h]; simp

/-- The square of a Bochner integral is bounded by the square of the `lintegral` of the
absolute value of the integrand; valid for arbitrary functions. -/
private theorem ofReal_integral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : α → ℝ) :
    ENNReal.ofReal ((∫ x, F x ∂μ) ^ 2) ≤ (∫⁻ x, ENNReal.ofReal |F x| ∂μ) ^ 2 := by
  have h := abs_integral_le_integral_abs (μ := μ) (f := F)
  have h1 : ENNReal.ofReal |∫ x, F x ∂μ| ≤ ∫⁻ x, ENNReal.ofReal |F x| ∂μ := by
    refine le_trans (ENNReal.ofReal_le_ofReal h) ?_
    exact ofReal_integral_le_lintegral_ofReal (Filter.Eventually.of_forall fun x => abs_nonneg _)
  calc ENNReal.ofReal ((∫ x, F x ∂μ) ^ 2) = (ENNReal.ofReal |∫ x, F x ∂μ|) ^ 2 := by
        rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    _ ≤ (∫⁻ x, ENNReal.ofReal |F x| ∂μ) ^ 2 := pow_le_pow_left₀ (zero_le) h1 2

/-- Cauchy--Schwarz in `ℝ≥0∞`: `(∫⁻ f)² ≤ (∫⁻ f²) · μ univ`, for an arbitrary function `f`
(no measurability assumption). -/
private theorem lintegral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ≥0∞) :
    (∫⁻ x, f x ∂μ) ^ 2 ≤ (∫⁻ x, (f x) ^ 2 ∂μ) * μ univ := by
  have key : ∫⁻ x, f x ∂μ
      ≤ (∫⁻ x, (f x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (μ univ) ^ (1 / 2 : ℝ) := by
    rw [← MeasureTheory.iSup_lintegral_measurable_le_eq_lintegral f]
    refine iSup_le fun g => iSup_le fun hg => iSup_le fun hgf => ?_
    have hold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2)
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      (f := g) (g := fun _ : α => (1 : ℝ≥0∞)) hg.aemeasurable aemeasurable_const
    have hleft : (∫⁻ a, (g * fun _ : α => (1 : ℝ≥0∞)) a ∂μ) = ∫⁻ a, g a ∂μ := by
      refine lintegral_congr fun a => ?_
      simp
    have hg2 : (∫⁻ a, g a ^ (2 : ℝ) ∂μ) = ∫⁻ a, (g a) ^ 2 ∂μ := by
      refine lintegral_congr fun a => ?_
      rw [ENNReal.rpow_two]
    have hone : (∫⁻ a, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂μ) = μ univ := by
      rw [show (fun a : α => (1 : ℝ≥0∞) ^ (2 : ℝ)) = fun _ => 1 from
        funext fun a => ENNReal.one_rpow 2]
      rw [MeasureTheory.lintegral_one]
    rw [hleft, hg2, hone] at hold
    have hle : (∫⁻ a, (g a) ^ 2 ∂μ) ≤ ∫⁻ a, (f a) ^ 2 ∂μ :=
      lintegral_mono fun a => pow_le_pow_left₀ (zero_le) (hgf a) 2
    calc ∫⁻ a, g a ∂μ ≤ (∫⁻ a, (g a) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (μ univ) ^ (1 / 2 : ℝ) := hold
      _ ≤ (∫⁻ a, (f a) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (μ univ) ^ (1 / 2 : ℝ) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hle (by norm_num)) le_rfl
  calc (∫⁻ x, f x ∂μ) ^ 2
      ≤ ((∫⁻ x, (f x) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (μ univ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (zero_le) key 2
    _ = (∫⁻ x, (f x) ^ 2 ∂μ) * μ univ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

/-- The pointwise (in `t`) estimate underlying `TailOneD`: for every `t ≤ 2N`,

`ofReal ((e^{bt} ∫_t^{2N} e^{-bs} k s g s)²) ≤ ofReal (4 c² / N) · ∫⁻_{[-2N,2N]} ofReal (g²)`.

The constant `4c²/N` is `(c/N)² · (4N)`: `4N` is the length of `[-2N, 2N]`, the interval
carrying the support of `k`, and the exponential weights cancel because `b ≥ 0` and the
integration runs over `s ≥ t`. -/
private theorem tail_pointwise (N b c t : ℝ) (hN : 2 ≤ N) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (k g : ℝ → ℝ) (hk : ∀ s, |k s| ≤ c / N) (hk0 : ∀ s, 2 * N ≤ |s| → k s = 0)
    (ht : t ≤ 2 * N) :
    ENNReal.ofReal ((Real.exp (b * t) * ∫ s in t..(2 * N),
        Real.exp (-(b * s)) * k s * g s) ^ 2)
      ≤ ENNReal.ofReal (4 * c ^ 2 / N)
        * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal ((g s) ^ 2) := by
  have hNpos : 0 < N := by linarith
  have hNnn : 0 ≤ N := le_of_lt hNpos
  set F : ℝ → ℝ := fun s => Real.exp (-(b * s)) * k s * g s with hFdef
  set I₂ : Set ℝ := Set.Icc (-(2 * N)) (2 * N) with hI2def
  set M : ℝ≥0∞ := ∫⁻ s in I₂, ENNReal.ofReal ((g s) ^ 2) with hMdef
  have hI2meas : MeasurableSet I₂ := by rw [hI2def]; exact measurableSet_Icc
  have hSmeas : MeasurableSet (I₂ ∩ Set.Ici t) := hI2meas.inter measurableSet_Ici
  -- the kernel vanishes off `[-2N, 2N]`
  have hF0 : ∀ s, s ∉ I₂ → F s = 0 := by
    intro s hs
    have h2 : 2 * N ≤ |s| := by
      by_contra h
      rw [not_le] at h
      have hmem : s ∈ Set.Icc (-(2 * N)) (2 * N) := by
        rw [Set.mem_Icc]
        exact ⟨le_of_lt (abs_lt.mp h).1, le_of_lt (abs_lt.mp h).2⟩
      exact hs (by rw [hI2def]; exact hmem)
    rw [hFdef]
    simp only
    simp [hk0 s h2]
  have hu0 : ∀ s, s ∉ I₂ → ENNReal.ofReal |F s| = 0 := fun s hs => by
    rw [hF0 s hs]; simp
  have hAeq : (∫ s in t..(2 * N), F s) = ∫ s, F s ∂(volume.restrict (Set.Ioc t (2 * N))) := by
    rw [intervalIntegral.integral_of_le ht]
  -- Cauchy--Schwarz on the interval of integration
  have hA2 : ENNReal.ofReal ((∫ s, F s ∂(volume.restrict (Set.Ioc t (2 * N)))) ^ 2)
      ≤ (∫⁻ s, ENNReal.ofReal |F s| ∂(volume.restrict (Set.Ioc t (2 * N)))) ^ 2 :=
    ofReal_integral_sq_le F
  -- move the `lintegral` to the support `I₂ ∩ [t,∞)` of the integrand
  have hstep4 : (∫⁻ s, ENNReal.ofReal |F s| ∂(volume.restrict (Set.Ioc t (2 * N))))
      ≤ ∫⁻ s, ENNReal.ofReal |F s| ∂(volume.restrict (I₂ ∩ Set.Ici t)) := by
    rw [← MeasureTheory.lintegral_indicator measurableSet_Ioc (fun s => ENNReal.ofReal |F s|),
        ← MeasureTheory.lintegral_indicator hSmeas (fun s => ENNReal.ofReal |F s|)]
    refine lintegral_mono fun s => ?_
    by_cases hs : s ∈ Set.Ioc t (2 * N)
    · rw [Set.indicator_of_mem hs]
      by_cases hI : s ∈ I₂
      · rw [Set.indicator_of_mem (s := I₂ ∩ Set.Ici t) (f := fun s => ENNReal.ofReal |F s|)
              ⟨hI, le_of_lt hs.1⟩]
      · rw [Set.indicator_of_notMem (s := I₂ ∩ Set.Ici t) (fun h => hI h.1)]
        exact le_of_eq (hu0 s hI)
    · rw [Set.indicator_of_notMem hs]; exact zero_le
  have hvol : (volume.restrict (I₂ ∩ Set.Ici t)) univ ≤ ENNReal.ofReal (4 * N) := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    calc volume (I₂ ∩ Set.Ici t) ≤ volume I₂ := measure_mono Set.inter_subset_left
      _ = ENNReal.ofReal (4 * N) := by
          rw [hI2def, Real.volume_Icc]
          congr 1; ring
  have hcs : (∫⁻ s, ENNReal.ofReal |F s| ∂(volume.restrict (I₂ ∩ Set.Ici t))) ^ 2
      ≤ (∫⁻ s, (ENNReal.ofReal |F s|) ^ 2 ∂(volume.restrict (I₂ ∩ Set.Ici t)))
        * ENNReal.ofReal (4 * N) :=
    le_trans (lintegral_sq_le (f := fun s => ENNReal.ofReal |F s|)) (mul_le_mul' le_rfl hvol)
  -- pointwise bound on the support: the exponentials cancel
  have hpw : ∀ s ∈ I₂ ∩ Set.Ici t,
      (ENNReal.ofReal |F s|) ^ 2
        ≤ ENNReal.ofReal (Real.exp (-(b * t + b * t)) * (c / N) ^ 2)
          * ENNReal.ofReal ((g s) ^ 2) := by
    intro s hs
    have hst : t ≤ s := hs.2
    have hbt : b * t ≤ b * s := mul_le_mul_of_nonneg_left hst hb
    have h1 : (F s) ^ 2 ≤ Real.exp (-(b * t + b * t)) * (c / N) ^ 2 * (g s) ^ 2 := by
      have he : (Real.exp (-(b * s))) ^ 2 ≤ Real.exp (-(b * t + b * t)) := by
        rw [sq, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have hk2 : (k s) ^ 2 ≤ (c / N) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (div_nonneg hc hNnn)]
        exact hk s
      calc (F s) ^ 2 = (Real.exp (-(b * s))) ^ 2 * (k s) ^ 2 * (g s) ^ 2 := by
            rw [hFdef]; ring
        _ ≤ Real.exp (-(b * t + b * t)) * (c / N) ^ 2 * (g s) ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg (g s))
            exact mul_le_mul he hk2 (sq_nonneg (k s)) (Real.exp_nonneg _)
    rw [← ENNReal.ofReal_pow (abs_nonneg (F s)), sq_abs]
    refine le_trans (ENNReal.ofReal_le_ofReal h1) ?_
    exact le_of_eq (ENNReal.ofReal_mul
      (p := Real.exp (-(b * t + b * t)) * (c / N) ^ 2) (q := (g s) ^ 2) (by positivity))
  have hSle : (∫⁻ s, (ENNReal.ofReal |F s|) ^ 2 ∂(volume.restrict (I₂ ∩ Set.Ici t)))
      ≤ ENNReal.ofReal (Real.exp (-(b * t + b * t)) * (c / N) ^ 2) * M := by
    have hstep1 : (∫⁻ s, (ENNReal.ofReal |F s|) ^ 2 ∂(volume.restrict (I₂ ∩ Set.Ici t)))
        ≤ ∫⁻ s, ENNReal.ofReal (Real.exp (-(b * t + b * t)) * (c / N) ^ 2)
            * ENNReal.ofReal ((g s) ^ 2) ∂(volume.restrict (I₂ ∩ Set.Ici t)) := by
      rw [← MeasureTheory.lintegral_indicator hSmeas (fun s => (ENNReal.ofReal |F s|) ^ 2),
          ← MeasureTheory.lintegral_indicator hSmeas
            (fun s => ENNReal.ofReal (Real.exp (-(b * t + b * t)) * (c / N) ^ 2)
              * ENNReal.ofReal ((g s) ^ 2))]
      refine lintegral_mono fun s => ?_
      by_cases hs : s ∈ I₂ ∩ Set.Ici t
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
        exact hpw s hs
      · rw [Set.indicator_of_notMem hs]; exact zero_le
    refine le_trans hstep1 ?_
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul' le_rfl ?_
    rw [hMdef]
    exact lintegral_mono_set Set.inter_subset_left
  -- the elementary `ofReal` arithmetic
  have harith1 : (Real.exp (b * t)) ^ 2 * (Real.exp (-(b * t + b * t)) * (c / N) ^ 2)
      = (c / N) ^ 2 := by
    rw [sq, ← Real.exp_add, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have harith2 : (c / N) ^ 2 * (4 * N) = 4 * c ^ 2 / N := by
    field_simp
  have hconst1 : ENNReal.ofReal (Real.exp (b * t)) ^ 2
      * ENNReal.ofReal (Real.exp (-(b * t + b * t)) * (c / N) ^ 2)
      = ENNReal.ofReal ((c / N) ^ 2) := by
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← ENNReal.ofReal_mul (by positivity), harith1]
  have hconst2 : ENNReal.ofReal ((c / N) ^ 2) * ENNReal.ofReal (4 * N)
      = ENNReal.ofReal (4 * c ^ 2 / N) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _), harith2]
  have hfin : ENNReal.ofReal (Real.exp (b * t)) ^ 2
        * (ENNReal.ofReal (Real.exp (-(b * t + b * t)) * (c / N) ^ 2) * M
            * ENNReal.ofReal (4 * N))
      = ENNReal.ofReal (4 * c ^ 2 / N) * M := by
    rw [show ENNReal.ofReal (Real.exp (b * t)) ^ 2
          * (ENNReal.ofReal (Real.exp (-(b * t + b * t)) * (c / N) ^ 2) * M
            * ENNReal.ofReal (4 * N))
        = (ENNReal.ofReal (Real.exp (b * t)) ^ 2
            * ENNReal.ofReal (Real.exp (-(b * t + b * t)) * (c / N) ^ 2))
          * (M * ENNReal.ofReal (4 * N)) from by ac_rfl,
        hconst1]
    rw [show ENNReal.ofReal ((c / N) ^ 2) * (M * ENNReal.ofReal (4 * N))
        = (ENNReal.ofReal ((c / N) ^ 2) * ENNReal.ofReal (4 * N)) * M from by ac_rfl, hconst2]
  calc ENNReal.ofReal ((Real.exp (b * t) * ∫ s in t..(2 * N), F s) ^ 2)
      = ENNReal.ofReal (Real.exp (b * t)) ^ 2
          * ENNReal.ofReal ((∫ s, F s ∂(volume.restrict (Set.Ioc t (2 * N)))) ^ 2) := by
        rw [hAeq, mul_pow, ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_pow (Real.exp_nonneg _)]
    _ ≤ ENNReal.ofReal (Real.exp (b * t)) ^ 2
          * ((∫⁻ s, ENNReal.ofReal |F s| ∂(volume.restrict (I₂ ∩ Set.Ici t))) ^ 2) := by
        refine mul_le_mul' le_rfl (le_trans hA2 (pow_le_pow_left₀ (zero_le) hstep4 2))
    _ ≤ ENNReal.ofReal (Real.exp (b * t)) ^ 2
          * (ENNReal.ofReal (Real.exp (-(b * t + b * t)) * (c / N) ^ 2) * M
              * ENNReal.ofReal (4 * N)) := by
        refine mul_le_mul' le_rfl ?_
        calc (∫⁻ s, ENNReal.ofReal |F s| ∂(volume.restrict (I₂ ∩ Set.Ici t))) ^ 2
            ≤ (∫⁻ s, (ENNReal.ofReal |F s|) ^ 2 ∂(volume.restrict (I₂ ∩ Set.Ici t)))
              * ENNReal.ofReal (4 * N) := hcs
          _ ≤ (ENNReal.ofReal (Real.exp (-(b * t + b * t)) * (c / N) ^ 2) * M)
              * ENNReal.ofReal (4 * N) := mul_le_mul' hSle le_rfl
    _ = ENNReal.ofReal (4 * c ^ 2 / N)
          * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal ((g s) ^ 2) := by
        rw [hfin, hMdef, hI2def]

/-- The `t`-integral of the pointwise bound: `8194 N · 4 c² / N = 32776 c² ≤ 40000 c²`. -/
private theorem tail_main (N b c : ℝ) (hN : 2 ≤ N) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (k g : ℝ → ℝ) (hk : ∀ s, |k s| ≤ c / N) (hk0 : ∀ s, 2 * N ≤ |s| → k s = 0) :
    ∫⁻ t in Set.Icc (-(8192 * N)) (2 * N),
        ENNReal.ofReal ((Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * k s * g s) ^ 2)
      ≤ ENNReal.ofReal (40000 * c ^ 2)
        * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal ((g s) ^ 2) := by
  set M : ℝ≥0∞ := ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal ((g s) ^ 2) with hMdef
  have hSmeas : MeasurableSet (Set.Icc (-(8192 * N)) (2 * N)) := measurableSet_Icc
  have hpt : ∀ t ∈ Set.Icc (-(8192 * N)) (2 * N),
      ENNReal.ofReal ((Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * k s * g s) ^ 2) ≤ ENNReal.ofReal (4 * c ^ 2 / N) * M :=
    fun t ht => tail_pointwise N b c t hN hb hc k g hk hk0 ht.2
  have hC : ENNReal.ofReal (4 * c ^ 2 / N) * ENNReal.ofReal (8194 * N)
      ≤ ENNReal.ofReal (40000 * c ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 : 4 * c ^ 2 / N * (8194 * N) = 32776 * c ^ 2 := by
      field_simp
      ring
    rw [h0]
    nlinarith [sq_nonneg c, hN]
  calc ∫⁻ t in Set.Icc (-(8192 * N)) (2 * N),
        ENNReal.ofReal ((Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * k s * g s) ^ 2)
      ≤ ∫⁻ t in Set.Icc (-(8192 * N)) (2 * N), ENNReal.ofReal (4 * c ^ 2 / N) * M := by
        rw [← MeasureTheory.lintegral_indicator hSmeas (fun t => ENNReal.ofReal
              ((Real.exp (b * t) * ∫ s in t..(2 * N), Real.exp (-(b * s)) * k s * g s) ^ 2)),
            ← MeasureTheory.lintegral_indicator hSmeas
              (fun _ => ENNReal.ofReal (4 * c ^ 2 / N) * M)]
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ Set.Icc (-(8192 * N)) (2 * N)
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
          exact hpt t ht
        · rw [Set.indicator_of_notMem ht]; exact zero_le
    _ = ENNReal.ofReal (4 * c ^ 2 / N) * M * ENNReal.ofReal (8194 * N) := by
        rw [MeasureTheory.lintegral_const, Measure.restrict_apply MeasurableSet.univ,
          Set.univ_inter, Real.volume_Icc]
        congr 2
        ring
    _ ≤ ENNReal.ofReal (40000 * c ^ 2) * M := by
        rw [show ENNReal.ofReal (4 * c ^ 2 / N) * M * ENNReal.ofReal (8194 * N)
            = (ENNReal.ofReal (4 * c ^ 2 / N) * ENNReal.ofReal (8194 * N)) * M from by ac_rfl]
        exact mul_le_mul' hC le_rfl

theorem TailOneD (N b c : ℝ) (hN : 2 ≤ N) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (k : ℝ → ℝ) (hk : ∀ s, |k s| ≤ c / N) (hk0 : ∀ s, 2 * N ≤ |s| → k s = 0)
    (g : ℝ → ℝ) :
    ∫⁻ t in Set.Icc (-(8192 * N)) (2 * N),
        ENNReal.ofReal ((Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * k s * g s) ^ 2)
      ≤ ENNReal.ofReal (40000 * c ^ 2)
        * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal ((g s) ^ 2) :=
  tail_main N b c hN hb hc k g hk hk0

end Work.FTS.EllSol.ShiftFT.uTrAthree
