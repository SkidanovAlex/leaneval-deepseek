import Mathlib
import Submission.Work.OddVolterra.WinData.thetaM_close_box
import Submission.Work.OddVolterra.Window.TW2_thetaM_state_unif_of_kvec
import Submission.Work.OddVolterra.WinData.wide_defs
import Submission.Work.OddVolterra.WinData.wide_kvecM_data
import Submission.Work.OddVolterra.WinData.state_ball_bounds

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddVolterra

noncomputable section

/-!
# Uniform state bound and state-Lipschitz constant of the manifest `Θ`-datum on the wide window

`KernelExt.ThetaM n h s σ z` is bounded and state-Lipschitz in `z`, uniformly in the perturbation
`h` (`C^∞`, supported in `[1 - 2τ, 1 - τ]`, with `|h^{(k)}| ≤ 1/100` for `k ≤ n+2`), on the *wide*
square `s, σ ∈ [1/4, 19/20]` of the window construction and on the state ball of radius `9/20`
around `baseState σ`.

Rows `0`, `1` of `ThetaM` are `-z₂`, `-z₃`, so they contribute the bound `2` and the Lipschitz
constant `1`.  Rows `2`, `3` are the first-slot derivative of the Abel average `G2M`, which
`Work.OddExistence.Manifest.deriv_G2M_eq_integral_on_RcM` turns into the `π`-weighted integral of
`∂_a KvecM`; the strengthened wide data `KvecMDataW` supplies the componentwise bound `C` and
state-Lipschitz constant `M` of `∂_a KvecM`, and `∫_0^1 (√(τ(1-τ)))⁻¹ (1-τ) dτ = π`.
-/

/-- **The uniform `Θ`-datum on the wide window, from the wide `KvecM` data.** -/
theorem thetaM_data_wide_of_kvec (n : ℕ) (hn : 1 ≤ n) (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hkvec : KvecMDataW n M C) :
    ∃ M' B' : ℝ, 0 ≤ M' ∧ 0 ≤ B' ∧ ThetaMDataW n M' B' := by
  refine ⟨max 1 (Real.pi * M), max 2 (Real.pi * C),
    le_trans zero_le_one (le_max_left (1 : ℝ) (Real.pi * M)),
    le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left (2 : ℝ) (Real.pi * C)), ?_⟩
  intro h hh hsupp hsmall
  have hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (le_trans hk (by omega)) s
  -- positivity of the Abel denominator on the wide square
  have hpos : Work.OddExistence.KdenPosOn h (1 / 4) (19 / 20) := by
    intro u hu σ hσ t ht
    rw [Kden_eq_sqrt_krad]
    exact Real.sqrt_pos.mpr (krad_pos_of_pos hsupp hsm1 (A := 1 / 4) (by norm_num)
      (by linarith [hu.1]) (by linarith [hσ.1]) ht)
  -- the componentwise bounds and state-Lipschitz of `∂_a KvecM`, at radius `1/2`
  have hCpt : ∀ a ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ w ∈ Metric.closedBall (baseState σ) (9 / 20), ∀ j : Fin 2,
      ‖deriv (fun u : ℝ =>
        (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) a‖ ≤ C := by
    intro a ha σ hσ w hw j
    exact (hkvec h hh hsupp hsmall a ha σ hσ w
      (Metric.closedBall_subset_closedBall (by norm_num : (9 : ℝ) / 20 ≤ 1 / 2) hw) w
      (Metric.closedBall_subset_closedBall (by norm_num : (9 : ℝ) / 20 ≤ 1 / 2) hw)).2.2.2.2.1 j
  have hMpt : ∀ a ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ w ∈ Metric.closedBall (baseState σ) (9 / 20),
      ∀ w' ∈ Metric.closedBall (baseState σ) (9 / 20), ∀ j : Fin 2,
      ‖deriv (fun u : ℝ =>
          (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) a -
        deriv (fun u : ℝ =>
          (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j) a‖
        ≤ M * ‖w - w'‖ := by
    intro a ha σ hσ w hw w' hw' j
    exact (hkvec h hh hsupp hsmall a ha σ hσ w
      (Metric.closedBall_subset_closedBall (by norm_num : (9 : ℝ) / 20 ≤ 1 / 2) hw) w'
      (Metric.closedBall_subset_closedBall (by norm_num : (9 : ℝ) / 20 ≤ 1 / 2) hw')).2.2.2.2.2 j
  intro s hs σ hσ z hz
  -- the integral representation of the first-slot derivative of `G2M`
  have hform : ∀ (j : Fin 2) (w : St), w ∈ Metric.closedBall (baseState σ) (9 / 20) →
      deriv (fun u : ℝ => (KernelExt.G2M n h u σ (w 0) (w 1) (w 2) (w 3)) j) s =
        ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ => (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j)
            (s + τ * (σ - s))) := by
    intro j w hw
    have hraw := Work.OddExistence.Manifest.deriv_G2M_eq_integral_on_RcM (n := n) (h := h) hh
      (a := 1 / 4) (b := 19 / 20) (ρ := 9 / 20) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hpos j (s, (σ, w)) ⟨hs, hσ, hw⟩
    have hL : (fun u : ℝ => (Work.OddBridge.G2M n h u σ (w 0) (w 1) (w 2) (w 3)) j)
        = (fun u : ℝ => (KernelExt.G2M n h u σ (w 0) (w 1) (w 2) (w 3)) j) := by
      funext u
      exact congrFun
        (Work.OddExistence.Manifest.G2M_eq_KernelExt n hh u σ (w 0) (w 1) (w 2) (w 3)) j
    have hR : (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (Work.OddBridge.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))))
        = (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s)))) := by
      funext τ
      have hKe : (fun u : ℝ => (Work.OddBridge.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j)
          = (fun u : ℝ => (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) := by
        funext u
        exact congrFun
          (Work.OddExistence.Manifest.KvecM_eq_KernelExt n hh u σ (w 0) (w 1) (w 2) (w 3)) j
      rw [hKe]
    rw [hL, hR] at hraw
    exact hraw
  -- pointwise bound of the integrand
  have hptC : ∀ (j : Fin 2) (w : St), w ∈ Metric.closedBall (baseState σ) (9 / 20) →
      ∀ τ : ℝ, τ ∈ Set.Ioc (0 : ℝ) 1 →
        ‖(Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s)))‖
          ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := by
    intro j w hw τ hτ
    rcases eq_or_lt_of_le hτ.2 with h1 | h1
    · subst h1
      simp
    · have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hτ.1, le_of_lt h1⟩
      have hpt : s + τ * (σ - s) ∈ Set.Icc (1 / 4 : ℝ) (19 / 20) := by
        refine ⟨?_, ?_⟩ <;> nlinarith [hs.1, hs.2, hσ.1, hσ.2, hτIcc.1, hτIcc.2]
      have hb := hCpt _ hpt σ hσ w hw j
      have hw0 : (0 : ℝ) ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ :=
        inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hτle : (0 : ℝ) ≤ 1 - τ := by linarith [hτIcc.1]
      calc ‖(Real.sqrt (τ * (1 - τ)))⁻¹ *
            ((1 - τ) * deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s)))‖
          = (Real.sqrt (τ * (1 - τ)))⁻¹ *
            ((1 - τ) * ‖deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))‖) := by
            rw [norm_mul, norm_mul, Real.norm_of_nonneg hw0, Real.norm_of_nonneg hτle]
        _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * C) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hτle) hw0
        _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C :=
            mul_le_mul_of_nonneg_left (by nlinarith [hτIcc.1, hC]) hw0
  -- value bound for the components of the `G2M`-derivative
  have hA : ∀ (j : Fin 2) (w : St), w ∈ Metric.closedBall (baseState σ) (9 / 20) →
      ‖deriv (fun u : ℝ => (KernelExt.G2M n h u σ (w 0) (w 1) (w 2) (w 3)) j) s‖
        ≤ Real.pi * C := by
    intro j w hw
    rw [hform j w hw]
    calc ‖∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s)))‖
        ≤ ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * C :=
          intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
            (Filter.Eventually.of_forall (fun τ hτ => hptC j w hw τ hτ))
            (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const C)
      _ = (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹) * C := by
          rw [intervalIntegral.integral_mul_const]
      _ = Real.pi * C := by rw [Work.OddVolterra.Existence.abel_weight_integral]
  -- interval integrability of the integrand
  have hint : ∀ (j : Fin 2) (w : St), w ∈ Metric.closedBall (baseState σ) (9 / 20) →
      IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (fun u : ℝ =>
          (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))))
        volume (0 : ℝ) 1 := by
    intro j w hw
    refine (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const C).mono_fun' ?_ ?_
    · have hm : Measurable (fun τ : ℝ => deriv (fun u : ℝ =>
          (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))) :=
        (measurable_deriv (𝕜 := ℝ) (fun u : ℝ =>
          (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j)).comp
          (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
      have hw' : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
        ((Real.continuous_sqrt.measurable).comp
          (measurable_id.mul (measurable_const.sub measurable_id))).inv
      exact (hw'.mul ((measurable_const.sub measurable_id).mul hm)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
      exact hptC j w hw τ ⟨hτ.1, hτ.2⟩
  -- Lipschitz bound for the components of the `G2M`-derivative
  have hB : ∀ (j : Fin 2) (w : St), w ∈ Metric.closedBall (baseState σ) (9 / 20) →
      ∀ (w' : St), w' ∈ Metric.closedBall (baseState σ) (9 / 20) →
      ‖deriv (fun u : ℝ => (KernelExt.G2M n h u σ (w 0) (w 1) (w 2) (w 3)) j) s -
       deriv (fun u : ℝ => (KernelExt.G2M n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j) s‖
        ≤ Real.pi * M * ‖w - w'‖ := by
    intro j w hw w' hw'
    rw [hform j w hw, hform j w' hw',
      ← intervalIntegral.integral_sub (hint j w hw) (hint j w' hw')]
    have hseq : (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s)))
        - (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j) (s + τ * (σ - s))))
        = (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * (deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))
            - deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j)
              (s + τ * (σ - s))))) := by
      funext τ; ring
    rw [hseq]
    have hpoint : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioc (0 : ℝ) 1 →
        ‖(Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * (deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))
            - deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j)
              (s + τ * (σ - s))))‖
          ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * (M * ‖w - w'‖) := by
      filter_upwards with τ hτ
      rcases eq_or_lt_of_le hτ.2 with h1 | h1
      · subst h1; simp
      · have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hτ.1, le_of_lt h1⟩
        have hpt : s + τ * (σ - s) ∈ Set.Icc (1 / 4 : ℝ) (19 / 20) := by
          refine ⟨?_, ?_⟩ <;> nlinarith [hs.1, hs.2, hσ.1, hσ.2, hτIcc.1, hτIcc.2]
        have hb := hMpt _ hpt σ hσ w hw w' hw' j
        have hw0 : (0 : ℝ) ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ :=
          inv_nonneg.mpr (Real.sqrt_nonneg _)
        have hτle : (0 : ℝ) ≤ 1 - τ := by linarith [hτIcc.1]
        have hMnn : (0 : ℝ) ≤ M * ‖w - w'‖ := mul_nonneg hM (norm_nonneg _)
        calc ‖(Real.sqrt (τ * (1 - τ)))⁻¹ *
              ((1 - τ) * (deriv (fun u : ℝ =>
                  (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))
                - deriv (fun u : ℝ =>
                  (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j)
                  (s + τ * (σ - s))))‖
            = (Real.sqrt (τ * (1 - τ)))⁻¹ *
              ((1 - τ) * ‖deriv (fun u : ℝ =>
                  (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))
                - deriv (fun u : ℝ =>
                  (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j)
                  (s + τ * (σ - s))‖) := by
              rw [norm_mul, norm_mul, Real.norm_of_nonneg hw0, Real.norm_of_nonneg hτle]
          _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * (M * ‖w - w'‖)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hτle) hw0
          _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * (M * ‖w - w'‖) :=
              mul_le_mul_of_nonneg_left (by nlinarith [hτIcc.1, hMnn]) hw0
    calc ‖∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * (deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w 0) (w 1) (w 2) (w 3)) j) (s + τ * (σ - s))
            - deriv (fun u : ℝ =>
              (KernelExt.KvecM n h u σ (w' 0) (w' 1) (w' 2) (w' 3)) j)
              (s + τ * (σ - s))))‖
        ≤ ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * (M * ‖w - w'‖) :=
          intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
            hpoint
            (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const (M * ‖w - w'‖))
      _ = (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹) * (M * ‖w - w'‖) := by
          rw [intervalIntegral.integral_mul_const]
      _ = Real.pi * M * ‖w - w'‖ := by
          rw [Work.OddVolterra.Existence.abel_weight_integral]; ring
  -- the state ball data of the two points
  have hz3 : ∀ w ∈ Metric.closedBall (baseState σ) (9 / 20), ∀ i : Fin 4, |w i| ≤ 2 :=
    fun w hw i => (state_ball_bounds (a := 1 / 4) (b := 1) (ρ := 9 / 20) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (⟨hσ.1, by linarith [hσ.2]⟩ : σ ∈ Set.Icc (1 / 4 : ℝ) 1) hw).2.2 i
  -- assembly: the uniform bound
  constructor
  · rw [pi_norm_le_iff_of_nonneg
      (le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left (2 : ℝ) (Real.pi * C)))]
    intro i
    fin_cases i
    · have hthis : ‖(KernelExt.ThetaM n h s σ z) (0 : Fin 4)‖ ≤ max 2 (Real.pi * C) := by
        have hci : (KernelExt.ThetaM n h s σ z) (0 : Fin 4) = -z 2 := by
          simp [KernelExt.ThetaM]
        rw [hci, norm_neg, Real.norm_eq_abs]
        exact le_trans (hz3 z hz 2) (le_max_left _ _)
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z) (1 : Fin 4)‖ ≤ max 2 (Real.pi * C) := by
        have hci : (KernelExt.ThetaM n h s σ z) (1 : Fin 4) = -z 3 := by
          simp [KernelExt.ThetaM]
        rw [hci, norm_neg, Real.norm_eq_abs]
        exact le_trans (hz3 z hz 3) (le_max_left _ _)
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z) (2 : Fin 4)‖ ≤ max 2 (Real.pi * C) := by
        have hci : (KernelExt.ThetaM n h s σ z) (2 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s) := by
          simp [KernelExt.ThetaM]
        rw [hci, norm_neg]
        exact le_trans (hA 0 z hz) (le_max_right _ _)
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z) (3 : Fin 4)‖ ≤ max 2 (Real.pi * C) := by
        have hci : (KernelExt.ThetaM n h s σ z) (3 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s) := by
          simp [KernelExt.ThetaM]
        rw [hci, norm_neg]
        exact le_trans (hA 1 z hz) (le_max_right _ _)
      simpa using hthis
  -- assembly: the state-Lipschitz estimate
  · intro z' hz'
    rw [pi_norm_le_iff_of_nonneg
      (mul_nonneg (le_trans zero_le_one (le_max_left (1 : ℝ) (Real.pi * M))) (norm_nonneg _))]
    intro i
    have hzmem : (s, (σ, z)) ∈ Work.OddExistence.Manifest.RcM (1 / 4) (19 / 20) (9 / 20) :=
      ⟨hs, hσ, hz⟩
    fin_cases i
    · have hthis : ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n h s σ z') (0 : Fin 4)‖
          ≤ max 1 (Real.pi * M) * ‖z - z'‖ := by
        have hc : (KernelExt.ThetaM n h s σ z) (0 : Fin 4) = -z 2 := by
          simp [KernelExt.ThetaM]
        have hc' : (KernelExt.ThetaM n h s σ z') (0 : Fin 4) = -z' 2 := by
          simp [KernelExt.ThetaM]
        rw [Pi.sub_apply, hc, hc']
        have hcoord : |z 2 - z' 2| ≤ ‖z - z'‖ := by
          have h := dist_le_pi_dist z z' (2 : Fin 4)
          rwa [Real.dist_eq] at h
        rw [show -z 2 - -z' 2 = -(z 2 - z' 2) by ring, norm_neg, Real.norm_eq_abs]
        calc |z 2 - z' 2| ≤ ‖z - z'‖ := hcoord
          _ ≤ max 1 (Real.pi * M) * ‖z - z'‖ :=
              le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n h s σ z') (1 : Fin 4)‖
          ≤ max 1 (Real.pi * M) * ‖z - z'‖ := by
        have hc : (KernelExt.ThetaM n h s σ z) (1 : Fin 4) = -z 3 := by
          simp [KernelExt.ThetaM]
        have hc' : (KernelExt.ThetaM n h s σ z') (1 : Fin 4) = -z' 3 := by
          simp [KernelExt.ThetaM]
        rw [Pi.sub_apply, hc, hc']
        have hcoord : |z 3 - z' 3| ≤ ‖z - z'‖ := by
          have h := dist_le_pi_dist z z' (3 : Fin 4)
          rwa [Real.dist_eq] at h
        rw [show -z 3 - -z' 3 = -(z 3 - z' 3) by ring, norm_neg, Real.norm_eq_abs]
        calc |z 3 - z' 3| ≤ ‖z - z'‖ := hcoord
          _ ≤ max 1 (Real.pi * M) * ‖z - z'‖ :=
              le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n h s σ z') (2 : Fin 4)‖
          ≤ max 1 (Real.pi * M) * ‖z - z'‖ := by
        have hc : (KernelExt.ThetaM n h s σ z) (2 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s) := by
          simp [KernelExt.ThetaM]
        have hc' : (KernelExt.ThetaM n h s σ z') (2 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 0) s) := by
          simp [KernelExt.ThetaM]
        rw [Pi.sub_apply, hc, hc']
        rw [show -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s)
              - -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 0) s)
              = -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s
                  - deriv (fun u : ℝ =>
                      (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 0) s) by ring, norm_neg]
        calc ‖deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s
              - deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 0) s‖
            ≤ Real.pi * M * ‖z - z'‖ := hB 0 z hz z' hz'
          _ ≤ max 1 (Real.pi * M) * ‖z - z'‖ :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      simpa using hthis
    · have hthis : ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n h s σ z') (3 : Fin 4)‖
          ≤ max 1 (Real.pi * M) * ‖z - z'‖ := by
        have hc : (KernelExt.ThetaM n h s σ z) (3 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s) := by
          simp [KernelExt.ThetaM]
        have hc' : (KernelExt.ThetaM n h s σ z') (3 : Fin 4) =
            -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 1) s) := by
          simp [KernelExt.ThetaM]
        rw [Pi.sub_apply, hc, hc']
        rw [show -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s)
              - -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 1) s)
              = -(deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s
                  - deriv (fun u : ℝ =>
                      (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 1) s) by ring, norm_neg]
        calc ‖deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s
              - deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 1) s‖
            ≤ Real.pi * M * ‖z - z'‖ := hB 1 z hz z' hz'
          _ ≤ max 1 (Real.pi * M) * ‖z - z'‖ :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      simpa using hthis

/-- **The target**: the manifest odd `Θ`-datum is uniformly bounded and uniformly state-Lipschitz
on the wide window `[1/4, 19/20]²` and the state ball of radius `9/20`. -/
theorem thetaM_state_lipschitz_ext (n : ℕ) (hn : 1 ≤ n) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ ∀ (h : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) (19 / 20),
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (9 / 20),
        ‖Work.OddVolterra.KernelExt.ThetaM n h s σ z‖ ≤ B ∧
        ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (9 / 20),
          ‖Work.OddVolterra.KernelExt.ThetaM n h s σ z -
            Work.OddVolterra.KernelExt.ThetaM n h s σ z'‖ ≤ M * ‖z - z'‖ := by
  obtain ⟨M, C, hM, hC, hkvec⟩ := kvecM_data_wide n hn
  obtain ⟨M', B', hM', hB', hT⟩ := thetaM_data_wide_of_kvec n hn M C hM hC hkvec
  exact ⟨M', B', hM', hB', hT⟩

end

end Work.OddVolterra.WinData
