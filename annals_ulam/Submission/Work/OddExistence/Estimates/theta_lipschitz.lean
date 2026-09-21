import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Ball
import Submission.Work.OddVolterra.Existence.theta_lipschitz_state_ball
import Submission.Work.OddExistence.Estimates.theta_eq_of_le

/-!
# `Work.OddExistence.Estimates.theta_lipschitz`

The kernel `Θ` of the odd transition-slope system is Lipschitz in the state variable, uniformly
on the compact state region `{z | ‖z - baseState σ‖ ≤ ρ}` (`σ ∈ [s,1]`, `s ∈ [a,b]`, `ρ ≤ 1/2`).

Two ranges have to be treated separately.

* For `σ = s` the third and fourth rows of `Θ` vanish identically
  (`Work.OddVolterra.deriv_G2_apply_eq_zero_of_le`: the Abel average `G₂(·,σ,·)` vanishes to the
  right of `σ`, so its first-slot derivative at `s ≥ σ` is `0`), so `Θ n h s s z = ![-z₀,-z₁,0,0]`
  is `1`-Lipschitz.
* For `s < σ ≤ 1` the last two rows are the `u`-derivatives at `u = s` of the Abel average `G₂`,
  which `Work.OddVolterra.hasDerivAt_G2` writes as an Abel-weighted integral of `∂_a Kvec` along
  the moving point `s + τ(σ-s) ∈ [s,σ)`.  On that region the uniform state-ball data
  `Work.OddVolterra.Existence.kvec_state_data` gives both the boundedness of `Kvec` and of its
  `a`-derivative and the Lipschitz constant `Bs` of the latter in the state, and the Abel weight
  integrates to `π`; hence the derivative is `π · Bs`-Lipschitz.  (The condition `ρ ≤ 1/2` is used
  only through the box bounds `z 0, z 1 ≥ 1/5`, `|z i| ≤ 2` supplied by
  `Work.OddVolterra.Existence.state_ball_box`.)

The constant is `max 1 (π · Bs + 1) = π · Bs + 1`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddExistence.Estimates

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem theta_lipschitz (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc s 1,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) ρ,
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState σ) ρ,
      ‖Work.OddVolterra.Theta n h s σ z - Work.OddVolterra.Theta n h s σ z'‖ ≤ L * ‖z - z'‖ := by
  have hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (le_trans hk (by norm_num)) s
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hab1 : a ≤ 1 := le_trans hab hb
  obtain ⟨Cm, Bs, hCm, hBs, hval, hlip⟩ :=
    Work.OddVolterra.Existence.kvec_state_data n hn hh hsupp hsm1 ha hab1
  refine ⟨Real.pi * Bs + 1, by positivity, ?_⟩
  intro s hs σ hσ z hz z' hz'
  have hσ1 : σ ≤ 1 := hσ.2
  have hsa : a ≤ s := hs.1
  have hsb1 : s ≤ 1 := le_trans hs.2 hb
  have hσIcc : σ ∈ Set.Icc a 1 := ⟨le_trans hsa hσ.1, hσ1⟩
  have hbz : z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2) :=
    Metric.closedBall_subset_closedBall hρ1 hz
  have hbz' : z' ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2) :=
    Metric.closedBall_subset_closedBall hρ1 hz'
  obtain ⟨hz0, hz1, hzb⟩ :=
    Work.OddVolterra.Existence.state_ball_box ha hab1 σ hσIcc z hbz
  obtain ⟨hz'0, hz'1, hz'b⟩ :=
    Work.OddVolterra.Existence.state_ball_box ha hab1 σ hσIcc z' hbz'
  have hcoord : ∀ i : Fin 4, |z i - z' i| ≤ ‖z - z'‖ := by
    intro i
    have h := dist_le_pi_dist z z' i
    rwa [Real.dist_eq] at h
  have hL1 : (1 : ℝ) ≤ Real.pi * Bs + 1 := by
    have hpi := Real.pi_pos
    nlinarith [hBs, hpi]
  rcases eq_or_lt_of_le hσ.1 with heq | hlt
  · -- ## The range `σ = s`
    have hzero : ∀ w : Work.OddVolterra.St,
        Work.OddVolterra.Theta n h s σ w = ![- w 2, - w 3, (0 : ℝ), 0] := by
      intro w
      have hd0 := Work.OddVolterra.deriv_G2_apply_eq_zero_of_le hh1 n
        (s := s) (σ := σ) (le_of_eq heq.symm) (w 0) (w 1) (w 2) (w 3) (0 : Fin 2)
      have hd1 := Work.OddVolterra.deriv_G2_apply_eq_zero_of_le hh1 n
        (s := s) (σ := σ) (le_of_eq heq.symm) (w 0) (w 1) (w 2) (w 3) (1 : Fin 2)
      funext i
      fin_cases i <;> simp [Work.OddVolterra.Theta, hd0, hd1]
    rw [hzero z, hzero z']
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
    intro i
    fin_cases i
    · have h0 : |(-z 2) - (-z' 2)| ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := by
        rw [neg_sub_neg, abs_sub_comm]
        calc |z 2 - z' 2| ≤ ‖z - z'‖ := hcoord 2
          _ ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := le_mul_of_one_le_left (norm_nonneg _) hL1
      simpa [Real.norm_eq_abs] using h0
    · have h1 : |(-z 3) - (-z' 3)| ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := by
        rw [neg_sub_neg, abs_sub_comm]
        calc |z 3 - z' 3| ≤ ‖z - z'‖ := hcoord 3
          _ ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := le_mul_of_one_le_left (norm_nonneg _) hL1
      simpa [Real.norm_eq_abs] using h1
    · have hnn : (0 : ℝ) ≤ (Real.pi * Bs + 1) * ‖z - z'‖ :=
        mul_nonneg (by positivity) (norm_nonneg _)
      simpa using hnn
    · have hnn : (0 : ℝ) ≤ (Real.pi * Bs + 1) * ‖z - z'‖ :=
        mul_nonneg (by positivity) (norm_nonneg _)
      simpa using hnn
  · -- ## The range `s < σ`
    set δ : ℝ := min (a / 2) ((σ - s) / 2) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
    have hδa : δ ≤ a / 2 := min_le_left _ _
    have hδs : δ ≤ (σ - s) / 2 := min_le_right _ _
    -- membership of the moving point `x + τ(σ-x)` in the trapezium
    have hpt : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
        x + τ * (σ - x) ∈ Set.Ico (a / 2) σ := by
      intro x hx τ hτ
      have hxσ : x < σ := by linarith [hx.2, hδs, hlt]
      have hσx : 0 < σ - x := by linarith
      have hxa : a / 2 < x := by linarith [hx.1, hδa, hsa]
      refine ⟨?_, ?_⟩
      · have h1 : 0 ≤ τ * (σ - x) := mul_nonneg hτ.1 hσx.le
        linarith
      · have h1 : τ * (σ - x) < σ - x := mul_lt_of_lt_one_left hσx hτ.2
        linarith
    -- the three analytic inputs of `hasDerivAt_G2`, uniformly in the state
    have hdata : ∀ w : Work.OddVolterra.St, (1 / 5 : ℝ) ≤ w 0 → (1 / 5 : ℝ) ≤ w 1 →
        (∀ i : Fin 4, |w i| ≤ 2) →
        (∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
          0 < Work.OddVolterra.krad h σ (-(w 0)) (x + τ * (σ - x)) ∧
          0 < Work.OddVolterra.krad h σ (w 1) (x + τ * (σ - x))) ∧
        (∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
          ‖Work.OddVolterra.Kvec n h (x + τ * (σ - x)) σ (w 0) (w 1) (w 2) (w 3)‖ ≤ Cm) ∧
        (∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
          DifferentiableAt ℝ (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3)) (x + τ * (σ - x))) ∧
        (∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          ‖(1 - τ) • deriv (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3)) (x + τ * (σ - x))‖ ≤ Cm) := by
      intro w hw0 hw1 hwb
      have hposw : ∀ x ∈ Set.Ioo (s - δ) (s + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
          0 < Work.OddVolterra.krad h σ (-(w 0)) (x + τ * (σ - x)) ∧
          0 < Work.OddVolterra.krad h σ (w 1) (x + τ * (σ - x)) := by
        intro x hx τ hτ
        have ha' := hpt x hx τ hτ
        have ht1 : (1 / 5 : ℝ) ≤ |-(w 0)| := by
          rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ w 0)]
          exact hw0
        have ht2 : (1 / 5 : ℝ) ≤ |w 1| := by
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ w 1)]
          exact hw1
        exact ⟨Work.OddVolterra.Existence.krad_pos_state_region hsupp hsm1
            (by linarith : (0 : ℝ) < a / 2) ha'.1 (le_of_lt ha'.2) hσ1 ht1,
          Work.OddVolterra.Existence.krad_pos_state_region hsupp hsm1
            (by linarith : (0 : ℝ) < a / 2) ha'.1 (le_of_lt ha'.2) hσ1 ht2⟩
      refine ⟨hposw, ?_, ?_, ?_⟩
      · intro x hx τ hτ
        exact (hval σ hσIcc _ (hpt x hx τ hτ) w hw0 hw1 hwb).1
      · intro x hx τ hτ
        obtain ⟨hk1, hk2⟩ := hposw x hx τ hτ
        exact Work.OddVolterra.Existence.differentiableAt_Kvec n hn hh w (hpt x hx τ hτ).2 hk1 hk2
      · intro x hx τ hτ
        rcases eq_or_lt_of_le hτ.2 with h1 | h1
        · subst h1
          rw [sub_self, zero_smul, norm_zero]
          exact hCm.le
        · have hb := (hval σ hσIcc _
            (hpt x hx τ ⟨hτ.1, h1⟩) w hw0 hw1 hwb).2
          have hτle : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.1]
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτle]
          calc (1 - τ) * ‖deriv (fun u : ℝ =>
                  Work.OddVolterra.Kvec n h u σ (w 0) (w 1) (w 2) (w 3))
                  (x + τ * (σ - x))‖
              ≤ 1 * Cm := mul_le_mul (by linarith [hτ.1]) hb (norm_nonneg _) (by norm_num)
            _ = Cm := one_mul _
    obtain ⟨hposz, hbdKz, hdiffz, hbndz⟩ := hdata z hz0 hz1 hzb
    obtain ⟨hposz', hbdKz', hdiffz', hbndz'⟩ := hdata z' hz'0 hz'1 hz'b
    -- the Abel integral representation of the last two rows of `Θ`
    have hHz := Work.OddVolterra.hasDerivAt_G2 n hh hlt z hδpos hbdKz hdiffz hbndz
    have hHz' := Work.OddVolterra.hasDerivAt_G2 n hh hlt z' hδpos hbdKz' hdiffz' hbndz'
    have hIntz : IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))))
        volume (0 : ℝ) 1 := by
      refine (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm).mono_fun' ?_ ?_
      · have hm : Measurable (fun τ : ℝ => deriv (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) :=
          (measurable_deriv (𝕜 := ℝ) (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3))).comp
            (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
        have hw : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
          ((Real.continuous_sqrt.measurable).comp
            (measurable_id.mul (measurable_const.sub measurable_id))).inv
        exact (hw.smul ((measurable_const.sub measurable_id).smul hm)).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
        rcases eq_or_lt_of_le hτ.2 with h1 | h1
        · subst h1
          simp
        · have hτIco : τ ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt hτ.1, h1⟩
          have hb := (hval σ hσIcc _
            (hpt s ⟨sub_lt_self s hδpos, lt_add_of_pos_right s hδpos⟩ τ hτIco)
            z hz0 hz1 hzb).2
          have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
          have hτle : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.1]
          have hsm : ‖(1 - τ) • deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
              (s + τ * (σ - s))‖ ≤ Cm := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτle]
            calc (1 - τ) * ‖deriv (fun u : ℝ =>
                    Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
                    (s + τ * (σ - s))‖
                ≤ 1 * Cm := mul_le_mul (by linarith [hτ.1]) hb (norm_nonneg _) (by norm_num)
              _ = Cm := one_mul _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
          exact mul_le_mul_of_nonneg_left hsm hw
    have hIntz' : IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ •
        ((1 - τ) • deriv (fun u : ℝ =>
          Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) (s + τ * (σ - s))))
        volume (0 : ℝ) 1 := by
      refine (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const Cm).mono_fun' ?_ ?_
      · have hm : Measurable (fun τ : ℝ => deriv (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) (s + τ * (σ - s))) :=
          (measurable_deriv (𝕜 := ℝ) (fun u : ℝ =>
            Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3))).comp
            (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s))
        have hw : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
          ((Real.continuous_sqrt.measurable).comp
            (measurable_id.mul (measurable_const.sub measurable_id))).inv
        exact (hw.smul ((measurable_const.sub measurable_id).smul hm)).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
        rcases eq_or_lt_of_le hτ.2 with h1 | h1
        · subst h1
          simp
        · have hτIco : τ ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt hτ.1, h1⟩
          have hb := (hval σ hσIcc _
            (hpt s ⟨sub_lt_self s hδpos, lt_add_of_pos_right s hδpos⟩ τ hτIco)
            z' hz'0 hz'1 hz'b).2
          have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
          have hτle : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.1]
          have hsm : ‖(1 - τ) • deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3))
              (s + τ * (σ - s))‖ ≤ Cm := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτle]
            calc (1 - τ) * ‖deriv (fun u : ℝ =>
                    Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3))
                    (s + τ * (σ - s))‖
                ≤ 1 * Cm := mul_le_mul (by linarith [hτ.1]) hb (norm_nonneg _) (by norm_num)
              _ = Cm := one_mul _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
          exact mul_le_mul_of_nonneg_left hsm hw
    -- the Lipschitz bound for the vector-valued first-slot derivative of `G₂`
    have hvec : ‖deriv (fun u : ℝ => Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s
        - deriv (fun u : ℝ => Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) s‖
        ≤ Real.pi * Bs * ‖z - z'‖ := by
      rw [hHz.deriv, hHz'.deriv, ← intervalIntegral.integral_sub hIntz hIntz']
      have hpoint : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioc (0 : ℝ) 1 →
          ‖(Real.sqrt (τ * (1 - τ)))⁻¹ • ((1 - τ) • deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s)))
            - (Real.sqrt (τ * (1 - τ)))⁻¹ • ((1 - τ) • deriv (fun u : ℝ =>
              Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3))
              (s + τ * (σ - s)))‖
          ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * (Bs * ‖z - z'‖) := by
        filter_upwards with τ hτ
        rcases eq_or_lt_of_le hτ.2 with h1 | h1
        · subst h1
          simp
        · have hτIco : τ ∈ Set.Ico (0 : ℝ) 1 := ⟨le_of_lt hτ.1, h1⟩
          have ha' := hpt s ⟨sub_lt_self s hδpos, lt_add_of_pos_right s hδpos⟩ τ hτIco
          have hD := hlip σ hσIcc _ ha' z z' hz0 hz1 hzb hz'0 hz'1 hz'b
          have hseq : (Real.sqrt (τ * (1 - τ)))⁻¹ • ((1 - τ) • deriv (fun u : ℝ =>
                Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s)))
              - (Real.sqrt (τ * (1 - τ)))⁻¹ • ((1 - τ) • deriv (fun u : ℝ =>
                Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) (s + τ * (σ - s)))
              = (Real.sqrt (τ * (1 - τ)))⁻¹ • ((1 - τ) • (deriv (fun u : ℝ =>
                Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))
                - deriv (fun u : ℝ =>
                Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3))
                (s + τ * (σ - s)))) := by
            rw [← smul_sub, ← smul_sub]
          rw [hseq]
          have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
          have hτle : (0 : ℝ) ≤ 1 - τ := by linarith [hτ.1]
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hw, abs_of_nonneg hτle]
          calc (Real.sqrt (τ * (1 - τ)))⁻¹ *
                ((1 - τ) * ‖deriv (fun u : ℝ =>
                  Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))
                  - deriv (fun u : ℝ =>
                  Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3))
                  (s + τ * (σ - s))‖)
              ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * (Bs * ‖z - z'‖)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD hτle) hw
            _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 * (Bs * ‖z - z'‖)) := by
                refine mul_le_mul_of_nonneg_left ?_ hw
                exact mul_le_mul_of_nonneg_right (by linarith [hτ.1])
                  (mul_nonneg hBs.le (norm_nonneg _))
            _ = (Real.sqrt (τ * (1 - τ)))⁻¹ * (Bs * ‖z - z'‖) := by ring
      calc ‖∫ τ in (0 : ℝ)..1, ((Real.sqrt (τ * (1 - τ)))⁻¹ • ((1 - τ) • deriv (fun u : ℝ =>
                Work.OddVolterra.Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s)))
            - (Real.sqrt (τ * (1 - τ)))⁻¹ • ((1 - τ) • deriv (fun u : ℝ =>
                Work.OddVolterra.Kvec n h u σ (z' 0) (z' 1) (z' 2) (z' 3))
                (s + τ * (σ - s))))‖
          ≤ ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * (Bs * ‖z - z'‖) :=
            intervalIntegral.norm_integral_le_of_norm_le (by norm_num) hpoint
              (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const (Bs * ‖z - z'‖))
        _ = Real.pi * (Bs * ‖z - z'‖) := by
            rw [intervalIntegral.integral_mul_const,
              Work.OddVolterra.Existence.abel_weight_integral]
        _ = Real.pi * Bs * ‖z - z'‖ := by ring
    -- assembly, componentwise
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    fin_cases i
    · have h0 : |(-z 2) - (-z' 2)| ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := by
        rw [neg_sub_neg, abs_sub_comm]
        calc |z 2 - z' 2| ≤ ‖z - z'‖ := hcoord 2
          _ ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := le_mul_of_one_le_left (norm_nonneg _) hL1
      simpa [Work.OddVolterra.Theta, Real.norm_eq_abs] using h0
    · have h1 : |(-z 3) - (-z' 3)| ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := by
        rw [neg_sub_neg, abs_sub_comm]
        calc |z 3 - z' 3| ≤ ‖z - z'‖ := hcoord 3
          _ ≤ (Real.pi * Bs + 1) * ‖z - z'‖ := le_mul_of_one_le_left (norm_nonneg _) hL1
      simpa [Work.OddVolterra.Theta, Real.norm_eq_abs] using h1
    · show ‖(Work.OddVolterra.Theta n h s σ z - Work.OddVolterra.Theta n h s σ z')
            (2 : Fin 4)‖ ≤ (Real.pi * Bs + 1) * ‖z - z'‖
      have hd2 : deriv (fun u : ℝ =>
            (Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s
          = (deriv (fun u : ℝ =>
            Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s) 0 := by
        have h := congrFun (deriv_pi (𝕜 := ℝ) (x := s)
          (φ := fun u : ℝ => Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3))
          (fun j => (differentiableAt_pi.mp hHz.differentiableAt) j)) (0 : Fin 2)
        simpa using h.symm
      have hd2' : deriv (fun u : ℝ =>
            (Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 0) s
          = (deriv (fun u : ℝ =>
            Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) s) 0 := by
        have h := congrFun (deriv_pi (𝕜 := ℝ) (x := s)
          (φ := fun u : ℝ => Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3))
          (fun j => (differentiableAt_pi.mp hHz'.differentiableAt) j)) (0 : Fin 2)
        simpa using h.symm
      have heq : (Work.OddVolterra.Theta n h s σ z - Work.OddVolterra.Theta n h s σ z')
            (2 : Fin 4)
          = -((deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s) 0)
            + (deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) s) 0 := by
        simp only [Pi.sub_apply, Work.OddVolterra.Theta, hd2, hd2', Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        ring
      rw [heq, show -((deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s) 0)
            + (deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) s) 0
          = -((deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s
              - deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) s) 0) by
        rw [Pi.sub_apply]; ring, norm_neg]
      refine le_trans (norm_le_pi_norm _ (0 : Fin 2)) ?_
      refine le_trans hvec ?_
      exact mul_le_mul_of_nonneg_right (by linarith [hBs, Real.pi_pos]) (norm_nonneg _)
    · show ‖(Work.OddVolterra.Theta n h s σ z - Work.OddVolterra.Theta n h s σ z')
            (3 : Fin 4)‖ ≤ (Real.pi * Bs + 1) * ‖z - z'‖
      have hd3 : deriv (fun u : ℝ =>
            (Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s
          = (deriv (fun u : ℝ =>
            Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s) 1 := by
        have h := congrFun (deriv_pi (𝕜 := ℝ) (x := s)
          (φ := fun u : ℝ => Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3))
          (fun j => (differentiableAt_pi.mp hHz.differentiableAt) j)) (1 : Fin 2)
        simpa using h.symm
      have hd3' : deriv (fun u : ℝ =>
            (Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) 1) s
          = (deriv (fun u : ℝ =>
            Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) s) 1 := by
        have h := congrFun (deriv_pi (𝕜 := ℝ) (x := s)
          (φ := fun u : ℝ => Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3))
          (fun j => (differentiableAt_pi.mp hHz'.differentiableAt) j)) (1 : Fin 2)
        simpa using h.symm
      have heq : (Work.OddVolterra.Theta n h s σ z - Work.OddVolterra.Theta n h s σ z')
            (3 : Fin 4)
          = -((deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s) 1)
            + (deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) s) 1 := by
        simp only [Pi.sub_apply, Work.OddVolterra.Theta, hd3, hd3', Matrix.cons_val_three,
          Matrix.head_cons, Matrix.tail_cons]
        ring
      rw [heq, show -((deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s) 1)
            + (deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) s) 1
          = -((deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) s
              - deriv (fun u : ℝ =>
              Work.OddVolterra.G2 n h u σ (z' 0) (z' 1) (z' 2) (z' 3)) s) 1) by
        rw [Pi.sub_apply]; ring, norm_neg]
      refine le_trans (norm_le_pi_norm _ (1 : Fin 2)) ?_
      refine le_trans hvec ?_
      exact mul_le_mul_of_nonneg_right (by linarith [hBs, Real.pi_pos]) (norm_nonneg _)

end

end Work.OddExistence.Estimates
