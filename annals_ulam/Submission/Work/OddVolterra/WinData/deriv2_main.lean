import Mathlib
import Submission.Work.OddVolterra.WinData.deriv2_diff

/-!
# Closeness of the slope-derivative of `𝚯M` on the extended box

This file proves the target statement `thetaM_deriv_close_ext` from the three clauses of the
second `u`-derivative estimate for the manifest Abel kernel `KvecM`:

* `thetaM_deriv_close_of_KvecM` — the reduction, taking those three clauses as a hypothesis.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.WinData

noncomputable section

open Work.OddVolterra Work.OddVolterra.KernelExt

set_option maxHeartbeats 1600000

/-- **Integrability of an Abel-weighted integrand** whose second factor is measurable and bounded
on `[0,1]`. -/
lemma intervalIntegrable_abel_weight_mul {F : ℝ → ℝ} {C : ℝ} (hFm : Measurable F)
    (hb : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖F τ‖ ≤ C) :
    IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * F τ)) volume (0 : ℝ) 1 := by
  have hw_int : IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) volume (0 : ℝ) 1 :=
    Commons.Geometry.Ulam.intervalIntegrable_abel_weight
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hwC : IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * C') volume (0:ℝ) 1 :=
    hw_int.mul_const C'
  refine hwC.mono_fun' ?_ ?_
  · have hw_meas : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
      (Work.OddVolterra.measurable_sqrt_real.comp
        (measurable_id.mul (measurable_const.sub measurable_id))).inv
    exact (hw_meas.mul (((measurable_const.sub measurable_id).pow_const 2).mul hFm)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
    have hτI : τ ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.mem_Ioc] at hτ
      exact ⟨le_of_lt hτ.1, hτ.2⟩
    have hw0 : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have h1τ : (0 : ℝ) ≤ 1 - τ := by linarith [hτI.2]
    have hbτ := hb τ hτI
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw0,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 - τ) ^ 2)]
    calc (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * ‖F τ‖)
        ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 * C') := by
          refine mul_le_mul_of_nonneg_left ?_ hw0
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (by norm_num)
          · nlinarith [hτI.1, hτI.2]
          · exact le_trans hbτ (le_max_left _ _)
      _ = (Real.sqrt (τ * (1 - τ)))⁻¹ * C' := by ring

/-- **The difference of two Abel-weighted integrals**, bounded pointwise. -/
lemma abs_integral_weighted_sub_le {F1 F2 : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (i1 : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * F1 τ)) volume (0:ℝ) 1)
    (i2 : IntervalIntegrable
      (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * F2 τ)) volume (0:ℝ) 1)
    (h : ∀ τ ∈ Set.Icc (0 : ℝ) 1, |F1 τ - F2 τ| ≤ C) :
    |(∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * F1 τ)) -
     (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * F2 τ))|
      ≤ Real.pi * C := by
  have hw_int : IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) volume (0 : ℝ) 1 :=
    Commons.Geometry.Ulam.intervalIntegrable_abel_weight
  have hw0 : ∀ τ : ℝ, 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ :=
    fun τ => inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [← intervalIntegral.integral_sub i1 i2]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs (by norm_num)) ?_
  have hpt : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |(Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * F1 τ) -
       (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * F2 τ)|
        ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * C := by
    intro τ hτ
    have hfac : (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * F1 τ) -
        (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * F2 τ)
        = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * (F1 τ - F2 τ)) := by ring
    rw [hfac, abs_mul, abs_mul, abs_of_nonneg (hw0 τ),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 - τ) ^ 2)]
    calc (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * |F1 τ - F2 τ|)
        ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h τ hτ) (by positivity)) (hw0 τ)
      _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 * C) := by
          refine mul_le_mul_of_nonneg_left ?_ (hw0 τ)
          refine mul_le_mul_of_nonneg_right ?_ hC
          nlinarith [hτ.1, hτ.2]
      _ = (Real.sqrt (τ * (1 - τ)))⁻¹ * C := by ring
  have hI1 : IntervalIntegrable (fun τ : ℝ =>
      |(Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * F1 τ) -
       (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 * F2 τ)|) volume (0:ℝ) 1 := (i1.sub i2).abs
  have hI2 : IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * C)
      volume (0 : ℝ) 1 := hw_int.mul_const C
  refine le_trans (intervalIntegral.integral_mono_on (by norm_num) hI1 hI2 hpt) (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const,
    Work.OddVolterra.Existence.abel_weight_integral]


/-- For `τ ∈ [0,1]` and `s ∈ [1/4,19/20]`, `σ ∈ [1/4,1]`, the point `s + τ(σ-s)` lies in
`[3/16,1]`. -/
lemma moving_mem_Icc {s σ τ : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20))
    (hσ : σ ∈ Set.Icc (1 / 4 : ℝ) 1) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    s + τ * (σ - s) ∈ Set.Icc (3 / 16 : ℝ) 1 := by
  have hpoint : s + τ * (σ - s) = (1 - τ) * s + τ * σ := by ring
  rw [hpoint]
  have h1 : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.2]
  have h2 : (0 : ℝ) ≤ τ := hτ.1
  constructor
  · have ha : (1 - τ) * (1 / 4) ≤ (1 - τ) * s :=
      mul_le_mul_of_nonneg_left (by linarith [hs.1]) h1
    have hb : τ * (1 / 4) ≤ τ * σ := mul_le_mul_of_nonneg_left (by linarith [hσ.1]) h2
    nlinarith [ha, hb]
  · have ha : (1 - τ) * s ≤ (1 - τ) * 1 := mul_le_mul_of_nonneg_left (by linarith [hs.2]) h1
    have hb : τ * σ ≤ τ * 1 := mul_le_mul_of_nonneg_left hσ.2 h2
    nlinarith [ha, hb]

/-- **The slope-derivative of `𝚯M` at `s`**, in components. -/
lemma deriv_ThetaM_components (n : ℕ) (h : ℝ → ℝ) (σ : ℝ) (z : St) (s : ℝ)
    (A : Fin 2 → ℝ)
    (hA : ∀ j : Fin 2, HasDerivAt (fun u : ℝ =>
      deriv (fun v : ℝ => (G2M n h v σ (z 0) (z 1) (z 2) (z 3)) j) u) (A j) s) :
    deriv (fun u : ℝ => ThetaM n h u σ z) s = ![0, 0, -(A 0), -(A 1)] := by
  rw [deriv_ThetaM_apply n h σ z s (hA 0).differentiableAt (hA 1).differentiableAt,
    (hA 0).deriv, (hA 1).deriv]

/-- **The target estimate, from the three clauses of the `KvecM` second-derivative estimate.** -/
theorem thetaM_deriv_close_of_KvecM (n : ℕ) (hn : 1 ≤ n)
    (hKv : ∃ C L : ℝ, 0 < C ∧ 0 < L ∧
      ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      ∀ u ∈ Set.Icc (3 / 16 : ℝ) 1, ∀ σ ∈ Set.Icc (1 / 4 : ℝ) 1,
      ∀ z : St, (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
      ∀ z' : St, (1 / 5 : ℝ) ≤ z' 0 → (1 / 5 : ℝ) ≤ z' 1 → (∀ i : Fin 4, |z' i| ≤ 2) →
      ∀ j : Fin 2,
      ‖deriv (deriv (fun u' : ℝ => (KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) j)) u‖ ≤ C ∧
      ‖deriv (deriv (fun u' : ℝ => (KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) j)) u -
       deriv (deriv (fun u' : ℝ => (KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) j)) u‖
        ≤ C * δ ∧
      ‖deriv (deriv (fun u' : ℝ => (KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) j)) u -
       deriv (deriv (fun u' : ℝ => (KvecM n h u' σ (z' 0) (z' 1) (z' 2) (z' 3)) j)) u‖
        ≤ L * ‖z - z'‖) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      ∀ s ∈ Set.Icc (1 / 4 : ℝ) (19 / 20), ∀ σ ∈ Set.Icc (1 / 4 : ℝ) 1,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (9 / 20),
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (9 / 20),
      (‖deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z) s -
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n 0 u σ z) s‖
            ≤ C * δ ∧
        ‖deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z) s -
          deriv (fun u : ℝ => Work.OddVolterra.KernelExt.ThetaM n h u σ z') s‖
            ≤ L * ‖z - z'‖) := by
  obtain ⟨Ck, Lk, hCk0, hLk0, hKv⟩ := hKv
  obtain ⟨C1, hC10, hC1⟩ := KvecM_est_ext n hn (a := 1 / 4) (by norm_num)
  refine ⟨Real.pi * Ck, Real.pi * Lk, by positivity, by positivity, ?_⟩
  intro h δ hh hδ0 hδ1 hjet hsupp s hs σ hσ z hz z' hz'
  obtain ⟨hz0, hz1, hzb⟩ := state_ball_bounds (a := 1 / 4) (b := 1) (ρ := 9 / 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hσ hz
  obtain ⟨hz'0, hz'1, hz'b⟩ := state_ball_bounds (a := 1 / 4) (b := 1) (ρ := 9 / 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hσ hz'
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆ Set.Icc (1 - 2 * tau) (1 - tau) := by
    intro x hx; simp at hx
  have hjet0 : ∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ δ := by
    intro k hk s
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split_ifs <;> simpa using hδ0.le
  have hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hjet k (by omega) s) hδ1
  have hsmall0 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ 1 / 100 := by
    intro k hk s
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split_ifs <;> norm_num
  -- ## the second derivative of `G2M` at `s`, for arbitrary admissible data
  have key : ∀ (g : ℝ → ℝ) (gg : ContDiff ℝ (⊤ : ℕ∞) g)
      (gsupp : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
      (gjet : ∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k g s| ≤ δ)
      (gsm : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k g s| ≤ 1 / 100)
      (v : St) (hv0 : (1 / 5 : ℝ) ≤ v 0) (hv1 : (1 / 5 : ℝ) ≤ v 1)
      (hvb : ∀ i : Fin 4, |v i| ≤ 2) (j : Fin 2),
      HasDerivAt (fun u : ℝ =>
          deriv (fun v' : ℝ => (G2M n g v' σ (v 0) (v 1) (v 2) (v 3)) j) u)
        (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 *
          deriv (deriv (fun a : ℝ => (KvecM n g a σ (v 0) (v 1) (v 2) (v 3)) j))
            (s + τ * (σ - s)))) s := by
    intro g gg gsupp gjet gsm v hv0 hv1 hvb j
    have hε : (0 : ℝ) < 1 / 100 := by norm_num
    have hCmax : 0 ≤ max C1 Ck := le_trans hC10.le (le_max_left _ _)
    have hmeas : Measurable (fun a : ℝ => (KvecM n g a σ (v 0) (v 1) (v 2) (v 3)) j) :=
      (measurable_pi_iff.mp (Work.OddExistence.Manifest.AW.measurable_KvecM n gg σ v)) j
    refine hasDerivAt_deriv_G2M v j hε hCmax hmeas ?_ ?_ ?_ ?_ ?_
    · intro x hx τ hτ
      have hp := moving_mem hs hσ hx ⟨hτ.1, hτ.2.le⟩
      have hval := (hC1 g δ gg hδ0 hδ1 (fun k hk s => gjet k (by omega) s) gsupp
        (x + τ * (σ - x)) (by linarith [hp.1]) (by linarith [hp.2]) σ hσ.1 hσ.2 v hv0 hv1 hvb j)
      exact le_trans hval.1 (le_max_left _ _)
    · intro x hx τ hτ
      have hp := moving_mem hs hσ hx ⟨hτ.1, hτ.2.le⟩
      exact (differentiableAt_KvecM_comp_and_deriv n gg gsupp gsm (by linarith [hσ.1])
        hp.1 hv0 hv1 j).1
    · intro x hx τ hτ
      have hp := moving_mem hs hσ hx ⟨hτ.1, hτ.2.le⟩
      have hval := (hC1 g δ gg hδ0 hδ1 (fun k hk s => gjet k (by omega) s) gsupp
        (x + τ * (σ - x)) (by linarith [hp.1]) (by linarith [hp.2]) σ hσ.1 hσ.2 v hv0 hv1 hvb j)
      exact le_trans hval.2.1 (le_max_left _ _)
    · intro x hx τ hτ
      have hp := moving_mem hs hσ hx ⟨hτ.1, hτ.2.le⟩
      exact (differentiableAt_KvecM_comp_and_deriv n gg gsupp gsm (by linarith [hσ.1])
        hp.1 hv0 hv1 j).2
    · intro x hx τ hτ
      have hp := moving_mem hs hσ hx hτ
      have hK := (hKv g δ gg hδ0 hδ1 gjet gsupp (x + τ * (σ - x)) hp σ hσ
        v hv0 hv1 hvb v hv0 hv1 hvb j).1
      rw [norm_mul]
      calc ‖1 - τ‖ * ‖deriv (deriv (fun a : ℝ =>
              (KvecM n g a σ (v 0) (v 1) (v 2) (v 3)) j)) (x + τ * (σ - x))‖
          ≤ 1 * Ck := by
            refine mul_le_mul ?_ hK (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
            rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hτ.2] : (0 : ℝ) ≤ 1 - τ)]
            linarith [hτ.1]
        _ ≤ max C1 Ck := by linarith [le_max_right C1 Ck]
  -- ## the three second-derivative computations
  set Ahz : Fin 2 → ℝ := fun j => ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
    ((1 - τ) ^ 2 * deriv (deriv (fun a : ℝ =>
      (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j)) (s + τ * (σ - s))) with hAhz
  set A0 : Fin 2 → ℝ := fun j => ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
    ((1 - τ) ^ 2 * deriv (deriv (fun a : ℝ =>
      (KvecM n 0 a σ (z 0) (z 1) (z 2) (z 3)) j)) (s + τ * (σ - s))) with hA0
  set Az' : Fin 2 → ℝ := fun j => ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
    ((1 - τ) ^ 2 * deriv (deriv (fun a : ℝ =>
      (KvecM n h a σ (z' 0) (z' 1) (z' 2) (z' 3)) j)) (s + τ * (σ - s))) with hAz'
  have hA1 : ∀ j : Fin 2, HasDerivAt (fun u : ℝ =>
      deriv (fun v' : ℝ => (G2M n h v' σ (z 0) (z 1) (z 2) (z 3)) j) u) (Ahz j) s := by
    intro j
    simpa only [hAhz] using key h hh hsupp hjet hsmall z hz0 hz1 hzb j
  have hA2 : ∀ j : Fin 2, HasDerivAt (fun u : ℝ =>
      deriv (fun v' : ℝ => (G2M n 0 v' σ (z 0) (z 1) (z 2) (z 3)) j) u) (A0 j) s := by
    intro j
    simpa only [hA0] using key 0 contDiff_const hsupp0 hjet0 hsmall0 z hz0 hz1 hzb j
  have hA3 : ∀ j : Fin 2, HasDerivAt (fun u : ℝ =>
      deriv (fun v' : ℝ => (G2M n h v' σ (z' 0) (z' 1) (z' 2) (z' 3)) j) u) (Az' j) s := by
    intro j
    simpa only [hAz'] using key h hh hsupp hjet hsmall z' hz'0 hz'1 hz'b j
  have hder1 : deriv (fun u : ℝ => ThetaM n h u σ z) s = ![0, 0, -(Ahz 0), -(Ahz 1)] :=
    deriv_ThetaM_components n h σ z s Ahz hA1
  have hder2 : deriv (fun u : ℝ => ThetaM n 0 u σ z) s = ![0, 0, -(A0 0), -(A0 1)] :=
    deriv_ThetaM_components n 0 σ z s A0 hA2
  have hder3 : deriv (fun u : ℝ => ThetaM n h u σ z') s = ![0, 0, -(Az' 0), -(Az' 1)] :=
    deriv_ThetaM_components n h σ z' s Az' hA3
  -- ## the pointwise bounds on the second derivatives
  have hpt1 : ∀ j : Fin 2, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j))
          (s + τ * (σ - s)) -
       deriv (deriv (fun a : ℝ => (KvecM n 0 a σ (z 0) (z 1) (z 2) (z 3)) j))
          (s + τ * (σ - s))| ≤ Ck * δ := by
    intro j τ hτ
    have hp := moving_mem_Icc hs hσ hτ
    have hK := (hKv h δ hh hδ0 hδ1 hjet hsupp (s + τ * (σ - s)) hp σ hσ
      z hz0 hz1 hzb z hz0 hz1 hzb j).2.1
    rw [Real.norm_eq_abs] at hK
    exact hK
  have hpt2 : ∀ j : Fin 2, ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j))
          (s + τ * (σ - s)) -
       deriv (deriv (fun a : ℝ => (KvecM n h a σ (z' 0) (z' 1) (z' 2) (z' 3)) j))
          (s + τ * (σ - s))| ≤ Lk * ‖z - z'‖ := by
    intro j τ hτ
    have hp := moving_mem_Icc hs hσ hτ
    have hK := (hKv h δ hh hδ0 hδ1 hjet hsupp (s + τ * (σ - s)) hp σ hσ
      z hz0 hz1 hzb z' hz'0 hz'1 hz'b j).2.2
    rw [Real.norm_eq_abs] at hK
    exact hK
  have hbdC : ∀ (g : ℝ → ℝ) (gg : ContDiff ℝ (⊤ : ℕ∞) g)
      (gjet : ∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k g s| ≤ δ)
      (gsupp : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
      (v : St) (hv0 : (1 / 5 : ℝ) ≤ v 0) (hv1 : (1 / 5 : ℝ) ≤ v 1)
      (hvb : ∀ i : Fin 4, |v i| ≤ 2) (j : Fin 2) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1),
      ‖deriv (deriv (fun a : ℝ => (KvecM n g a σ (v 0) (v 1) (v 2) (v 3)) j))
        (s + τ * (σ - s))‖ ≤ Ck := by
    intro g gg gjet gsupp v hv0 hv1 hvb j τ hτ
    have hp := moving_mem_Icc hs hσ hτ
    exact (hKv g δ gg hδ0 hδ1 gjet gsupp (s + τ * (σ - s)) hp σ hσ
      v hv0 hv1 hvb v hv0 hv1 hvb j).1
  have hint : ∀ (g : ℝ → ℝ) (gg : ContDiff ℝ (⊤ : ℕ∞) g)
      (gjet : ∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k g s| ≤ δ)
      (gsupp : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
      (v : St) (hv0 : (1 / 5 : ℝ) ≤ v 0) (hv1 : (1 / 5 : ℝ) ≤ v 1)
      (hvb : ∀ i : Fin 4, |v i| ≤ 2) (j : Fin 2),
      IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) ^ 2 *
        deriv (deriv (fun a : ℝ => (KvecM n g a σ (v 0) (v 1) (v 2) (v 3)) j))
          (s + τ * (σ - s)))) volume (0 : ℝ) 1 := by
    intro g gg gjet gsupp v hv0 hv1 hvb j
    refine intervalIntegrable_abel_weight_mul (C := Ck) ?_ ?_
    · exact (measurable_deriv (𝕜 := ℝ)
        (deriv (fun a : ℝ => (KvecM n g a σ (v 0) (v 1) (v 2) (v 3)) j))).comp (by fun_prop)
    · intro τ hτ
      exact hbdC g gg gjet gsupp v hv0 hv1 hvb j τ hτ
  -- ## the two difference bounds
  have hdiff1 : ∀ j : Fin 2, |Ahz j - A0 j| ≤ Real.pi * (Ck * δ) := by
    intro j
    have h := abs_integral_weighted_sub_le (F1 := fun τ : ℝ =>
        deriv (deriv (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j))
          (s + τ * (σ - s)))
      (F2 := fun τ : ℝ =>
        deriv (deriv (fun a : ℝ => (KvecM n 0 a σ (z 0) (z 1) (z 2) (z 3)) j))
          (s + τ * (σ - s)))
      (C := Ck * δ) (by positivity) (hint h hh hjet hsupp z hz0 hz1 hzb j)
        (hint 0 contDiff_const hjet0 hsupp0 z hz0 hz1 hzb j) (hpt1 j)
    simpa only [hAhz, hA0] using h
  have hdiff2 : ∀ j : Fin 2, |Ahz j - Az' j| ≤ Real.pi * (Lk * ‖z - z'‖) := by
    intro j
    have h := abs_integral_weighted_sub_le (F1 := fun τ : ℝ =>
        deriv (deriv (fun a : ℝ => (KvecM n h a σ (z 0) (z 1) (z 2) (z 3)) j))
          (s + τ * (σ - s)))
      (F2 := fun τ : ℝ =>
        deriv (deriv (fun a : ℝ => (KvecM n h a σ (z' 0) (z' 1) (z' 2) (z' 3)) j))
          (s + τ * (σ - s)))
      (C := Lk * ‖z - z'‖) (by positivity) (hint h hh hjet hsupp z hz0 hz1 hzb j)
        (hint h hh hjet hsupp z' hz'0 hz'1 hz'b j) (hpt2 j)
    simpa only [hAhz, hAz'] using h
  -- ## assemble
  constructor
  · rw [hder1, hder2, ← dist_eq_norm]
    rw [dist_pi_le_iff (by positivity : (0 : ℝ) ≤ Real.pi * Ck * δ)]
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp
    rcases hi with h | h | h | h <;> subst h
    · have hz0 : ((![0, 0, -(Ahz 0), -(Ahz 1)] : Fin 4 → ℝ) 0) = (0 : ℝ) := rfl
      have hz1 : ((![0, 0, -(A0 0), -(A0 1)] : Fin 4 → ℝ) 0) = (0 : ℝ) := rfl
      rw [Real.dist_eq, hz0, hz1, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg Real.pi_pos.le hCk0.le) hδ0.le
    · have hz0 : ((![0, 0, -(Ahz 0), -(Ahz 1)] : Fin 4 → ℝ) 1) = (0 : ℝ) := rfl
      have hz1 : ((![0, 0, -(A0 0), -(A0 1)] : Fin 4 → ℝ) 1) = (0 : ℝ) := rfl
      rw [Real.dist_eq, hz0, hz1, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg Real.pi_pos.le hCk0.le) hδ0.le
    · have hz0 : ((![0, 0, -(Ahz 0), -(Ahz 1)] : Fin 4 → ℝ) 2) = -(Ahz 0) := rfl
      have hz1 : ((![0, 0, -(A0 0), -(A0 1)] : Fin 4 → ℝ) 2) = -(A0 0) := rfl
      rw [Real.dist_eq, hz0, hz1]
      have hkey := hdiff1 0
      have he : -(Ahz 0) - -(A0 0) = -(Ahz 0 - A0 0) := by ring
      rw [he, abs_neg]
      calc |Ahz 0 - A0 0| ≤ Real.pi * (Ck * δ) := hkey
        _ = Real.pi * Ck * δ := by ring
    · have hz0 : ((![0, 0, -(Ahz 0), -(Ahz 1)] : Fin 4 → ℝ) 3) = -(Ahz 1) := rfl
      have hz1 : ((![0, 0, -(A0 0), -(A0 1)] : Fin 4 → ℝ) 3) = -(A0 1) := rfl
      rw [Real.dist_eq, hz0, hz1]
      have hkey := hdiff1 1
      have he : -(Ahz 1) - -(A0 1) = -(Ahz 1 - A0 1) := by ring
      rw [he, abs_neg]
      calc |Ahz 1 - A0 1| ≤ Real.pi * (Ck * δ) := hkey
        _ = Real.pi * Ck * δ := by ring
  · rw [hder1, hder3, ← dist_eq_norm]
    rw [dist_pi_le_iff (by positivity : (0 : ℝ) ≤ Real.pi * Lk * ‖z - z'‖)]
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp
    rcases hi with h | h | h | h <;> subst h
    · have hz0 : ((![0, 0, -(Ahz 0), -(Ahz 1)] : Fin 4 → ℝ) 0) = (0 : ℝ) := rfl
      have hz1 : ((![0, 0, -(Az' 0), -(Az' 1)] : Fin 4 → ℝ) 0) = (0 : ℝ) := rfl
      rw [Real.dist_eq, hz0, hz1, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg Real.pi_pos.le hLk0.le) (norm_nonneg _)
    · have hz0 : ((![0, 0, -(Ahz 0), -(Ahz 1)] : Fin 4 → ℝ) 1) = (0 : ℝ) := rfl
      have hz1 : ((![0, 0, -(Az' 0), -(Az' 1)] : Fin 4 → ℝ) 1) = (0 : ℝ) := rfl
      rw [Real.dist_eq, hz0, hz1, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg Real.pi_pos.le hLk0.le) (norm_nonneg _)
    · have hz0 : ((![0, 0, -(Ahz 0), -(Ahz 1)] : Fin 4 → ℝ) 2) = -(Ahz 0) := rfl
      have hz1 : ((![0, 0, -(Az' 0), -(Az' 1)] : Fin 4 → ℝ) 2) = -(Az' 0) := rfl
      rw [Real.dist_eq, hz0, hz1]
      have hkey := hdiff2 0
      have he : -(Ahz 0) - -(Az' 0) = -(Ahz 0 - Az' 0) := by ring
      rw [he, abs_neg]
      calc |Ahz 0 - Az' 0| ≤ Real.pi * (Lk * ‖z - z'‖) := hkey
        _ = Real.pi * Lk * ‖z - z'‖ := by ring
    · have hz0 : ((![0, 0, -(Ahz 0), -(Ahz 1)] : Fin 4 → ℝ) 3) = -(Ahz 1) := rfl
      have hz1 : ((![0, 0, -(Az' 0), -(Az' 1)] : Fin 4 → ℝ) 3) = -(Az' 1) := rfl
      rw [Real.dist_eq, hz0, hz1]
      have hkey := hdiff2 1
      have he : -(Ahz 1) - -(Az' 1) = -(Ahz 1 - Az' 1) := by ring
      rw [he, abs_neg]
      calc |Ahz 1 - Az' 1| ≤ Real.pi * (Lk * ‖z - z'‖) := hkey
        _ = Real.pi * Lk * ‖z - z'‖ := by ring

end

end Work.OddVolterra.WinData
