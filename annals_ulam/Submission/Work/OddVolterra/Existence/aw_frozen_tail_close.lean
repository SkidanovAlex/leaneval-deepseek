import Mathlib
import Submission.Work.OddVolterra.Window.Theta_close_aux
import Submission.Work.OddVolterra.Window.Kvec_deriv_close
import Submission.Work.OddVolterra.Window.manifest_eq

/-!
# The frozen tail of the odd transition-slope system

The long-interval Volterra engine for the odd case is run on `[1/2, 19/20]` with a source term
that contains the *frozen tail*

`∫_{19/20}^{1} Θ(s,σ, baseState σ) dσ`,

which is invisible to the system (the solution is compared with `baseState` there) but must be
compared with its unperturbed value: the whole source `Xi n h s + ∫_{19/20}^1 Θ(s,σ,baseState σ)`
has to be `O(δ)`-close to the unperturbed one, uniformly in `s ∈ [1/2, 19/20]`.

This file proves that comparison for the *manifest* kernel `ThetaM`
(`annals_ulam`, `Work.OddVolterra.Existence.aw_frozen_tail_close`).  The pointwise input is

`‖ThetaM n h s σ (baseState σ) - ThetaM n 0 s σ (baseState σ)‖ ≤ K δ`   for `σ ∈ (19/20, 1]`,

with `δ` bounding the `C^{n+2}`-norm of the bump `h`; integrating over the tail of length `1/20`
and choosing `δ < 20 ε / K` finishes.

The pointwise estimate is the `s ∈ [1/2, 19/20]`, `σ ∈ (19/20,1]` variant of
`Work.OddVolterra.Window.Theta_close_window_of_kvec`: the last two rows of `ThetaM` are
`-∂_u (G2M n h · σ z)_i (s)`, the manifest average agrees with the paper's `G2` on `[9/20, σ]`
(`manifest_eq.G2M_eq_G2`, positivity of the radicand from `krad_pos_state_region`), and
`deriv_G2_eq_integral_of_lt` computes that derivative as an Abel-weighted integral of
`∂_a Kvec`, whose `h`-defect is `≤ C δ` by `Kvec_deriv_close`.
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- **Pointwise `O(δ)`-closeness of the manifest `Θ` on the frozen tail.**
For `s ∈ [1/2, 19/20]` and `σ ∈ (19/20, 1]` the last two rows of `ThetaM n h s σ (baseState σ)`
differ from the unperturbed ones by at most `K δ`, uniformly in `h` (supported in
`[1-2τ, 1-τ]`, `δ`-small in `C^{n+2}`) and in `σ`. -/
theorem awft_thetaM_tail_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h : ℝ → ℝ) (D : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < D → D ≤ 1 / 100 →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ D) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20 : ℝ), ∀ σ ∈ Set.Ioc (19 / 20 : ℝ) 1,
        ‖KernelExt.ThetaM n h s σ (baseState σ) -
          KernelExt.ThetaM n 0 s σ (baseState σ)‖ ≤ K * D := by
  obtain ⟨C, hC0, hKC⟩ := Window.Kvec_deriv_close n hn
  refine ⟨C * Real.pi, by positivity, ?_⟩
  intro h D hh hDpos hD100 hsupp hjet s hs σ hσ
  set z : St := baseState σ with hzdef
  have hσIcc : σ ∈ Set.Icc (7 / 10 : ℝ) 1 := ⟨by linarith [hσ.1], hσ.2⟩
  have hsσ : s < σ := by linarith [hs.2, hσ.1]
  have hzball : z ∈ Metric.closedBall (baseState σ) (1 / 2) := by
    rw [hzdef, Metric.mem_closedBall, dist_self]
    norm_num
  obtain ⟨hz0, hz1, hzbd⟩ :=
    Window.state_ball_box' (b := 19 / 20) (by norm_num) (by norm_num)
      σ ⟨le_of_lt hσ.1, hσ.2⟩ z hzball
  set e : ℝ := min (1 / 20) ((σ - s) / 2) with hedef
  have hepos : 0 < e := by rw [hedef]; exact lt_min (by norm_num) (by linarith)
  have he20 : e ≤ 1 / 20 := by rw [hedef]; exact min_le_left _ _
  have he2 : e ≤ (σ - s) / 2 := by rw [hedef]; exact min_le_right _ _
  have hse : (9 / 20 : ℝ) ≤ s - e := by linarith [hs.1, he20]
  have hpoint : ∀ x ∈ Set.Ioo (s - e) (s + e), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      x + τ * (σ - x) ∈ Set.Icc (s - e) σ ∧ x + τ * (σ - x) < σ := by
    intro x hx τ hτ
    have hxσ : x < σ := by linarith [hx.2, he2]
    have hconvex : x + τ * (σ - x) = (1 - τ) * x + τ * σ := by ring
    have hge : s - e ≤ x := le_of_lt hx.1
    constructor
    · rw [hconvex]
      constructor
      · nlinarith [hτ.1, hτ.2, hge]
      · nlinarith [hτ.1, hτ.2, hxσ]
    · rw [hconvex]; nlinarith [hτ.1, hτ.2, hxσ]
  have hsmallg : ∀ (g : ℝ → ℝ), (∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D) →
      ∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ 1 / 100 :=
    fun g hgj k hk x => le_trans (hgj k (le_trans hk (by omega)) x) hD100
  have hposg : ∀ (g : ℝ → ℝ), (∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ 1 / 100) →
      Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      ∀ σ' ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ a ∈ Set.Icc (9 / 20 : ℝ) σ',
        0 < krad g σ' (-(z 0)) a ∧ 0 < krad g σ' (z 1) a := by
    intro g hg1 hgs σ' hσ' a ha
    have ht0 : (1 / 5 : ℝ) ≤ |-(z 0)| := by
      rw [abs_neg, abs_of_nonneg (by linarith [hz0])]; exact hz0
    have ht1 : (1 / 5 : ℝ) ≤ |z 1| := by
      rw [abs_of_nonneg (by linarith [hz1])]; exact hz1
    exact ⟨krad_pos_state_region hgs hg1 (by norm_num : (0:ℝ) < 9 / 20) ha.1 ha.2 hσ'.2 ht0,
      krad_pos_state_region hgs hg1 (by norm_num : (0:ℝ) < 9 / 20) ha.1 ha.2 hσ'.2 ht1⟩
  have hjet0 : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) x| ≤ D := by
    intro k hk x
    have h0 : iteratedDeriv k (0 : ℝ → ℝ) x = 0 := by
      rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
      split <;> simp
    rw [h0, abs_zero]; exact le_of_lt hDpos
  have hsmall0 : ∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) x| ≤ 1 / 100 := by
    intro k hk x
    have h0 : iteratedDeriv k (0 : ℝ → ℝ) x = 0 := by
      rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
      split <;> simp
    rw [h0, abs_zero]; norm_num
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆ Set.Icc (1 - 2 * tau) (1 - tau) := by
    intro x hx
    rw [Function.mem_support] at hx
    exact absurd rfl hx
  have hbK : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgj : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D)
      (hgs : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau)),
      ∀ x ∈ Set.Ioo (s - e) (s + e), ∀ τ ∈ Set.Ico (0:ℝ) 1,
        ‖Kvec n g (x + τ * (σ - x)) σ (z 0) (z 1) (z 2) (z 3)‖ ≤ C + 1 := by
    intro g hg hgj hgs x hx τ hτ
    obtain ⟨hmem, hlt'⟩ := hpoint x hx τ hτ
    have := (hKC g D hg (le_of_lt hDpos) hD100 hgs hgj σ hσIcc z hz0 hz1 hzbd _
      ⟨le_trans hse hmem.1, hmem.2⟩ hlt').1
    linarith
  have hbD : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgj : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D)
      (hgs : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau)),
      ∀ x ∈ Set.Ioo (s - e) (s + e), ∀ τ ∈ Set.Icc (0:ℝ) 1,
        ‖(1 - τ) • deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
          (x + τ * (σ - x))‖ ≤ C + 1 := by
    intro g hg hgj hgs x hx τ hτ
    rcases eq_or_lt_of_le hτ.2 with h1 | h1
    · subst h1
      simp only [sub_self, zero_smul, norm_zero]; linarith [hC0]
    · obtain ⟨hmem, hlt'⟩ := hpoint x hx τ ⟨hτ.1, h1⟩
      have hb := (hKC g D hg (le_of_lt hDpos) hD100 hgs hgj σ hσIcc z hz0 hz1 hzbd _
        ⟨le_trans hse hmem.1, hmem.2⟩ hlt').2.2.1
      have hτle : (0:ℝ) ≤ 1 - τ := by linarith [hτ.1, h1]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτle]
      have h2 : (1 - τ) * ‖deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
          (x + τ * (σ - x))‖ ≤ 1 * (C + 1) := by
        calc (1 - τ) * ‖deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
              (x + τ * (σ - x))‖
            ≤ 1 * ‖deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
              (x + τ * (σ - x))‖ :=
              mul_le_mul_of_nonneg_right (by linarith [hτ.1, h1]) (norm_nonneg _)
          _ ≤ 1 * (C + 1) := mul_le_mul_of_nonneg_left (le_trans hb (by linarith)) (by norm_num)
      linarith [h2]
  have hdiffg : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgj : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D)
      (hgs : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau)),
      ∀ x ∈ Set.Ioo (s - e) (s + e), ∀ τ ∈ Set.Ico (0:ℝ) 1,
        DifferentiableAt ℝ (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
          (x + τ * (σ - x)) := by
    intro g hg hgj hgs x hx τ hτ
    obtain ⟨hmem, hlt'⟩ := hpoint x hx τ hτ
    exact differentiableAt_Kvec n hn hg (z := z) hlt'
      (hposg g (hsmallg g hgj) hgs σ hσIcc _ ⟨le_trans hse hmem.1, hmem.2⟩).1
      (hposg g (hsmallg g hgj) hgs σ hσIcc _ ⟨le_trans hse hmem.1, hmem.2⟩).2
  have hformula : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgj : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D)
      (hgs : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) (i : Fin 2),
      deriv (fun u : ℝ => (G2 n g u σ (z 0) (z 1) (z 2) (z 3)) i) s =
        ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * ((deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
            (s + τ * (σ - s))) i)) :=
    fun g hg hgj hgs i =>
      Window.deriv_G2_eq_integral_of_lt n hn hg hsσ z hepos (by linarith [hC0])
        (hbK g hg hgj hgs) (hdiffg g hg hgj hgs) (hbD g hg hgj hgs) i
  have hIntF : ∀ (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgj : ∀ k : ℕ, k ≤ n + 2 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ D)
      (hgs : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) (i : Fin 2),
      IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * ((deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
          (s + τ * (σ - s))) i))) volume (0:ℝ) 1 := by
    intro g hg hgj hgs i
    refine (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const (C + 1)).mono_fun' ?_ ?_
    · have hmw : Measurable (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹) :=
        ((Real.continuous_sqrt.measurable.comp
          (measurable_id.mul (measurable_const.sub measurable_id)))).inv
      have hA : Measurable (fun τ : ℝ => (deriv (fun u : ℝ =>
          Kvec n g u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i) :=
        (measurable_pi_apply i).comp
          ((measurable_deriv (𝕜 := ℝ) (fun u : ℝ =>
            Kvec n g u σ (z 0) (z 1) (z 2) (z 3))).comp
            (by fun_prop : Measurable fun τ : ℝ => s + τ * (σ - s)))
      exact (hmw.mul ((measurable_const.sub measurable_id).mul hA)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with τ hτ
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
      rcases eq_or_lt_of_le hτ.2 with h1 | h1
      · subst h1
        have h0 : (Real.sqrt ((1:ℝ) * (1 - 1)))⁻¹ = 0 := by
          rw [show (1:ℝ) * (1 - 1) = 0 by norm_num, Real.sqrt_zero, inv_zero]
        rw [h0]; simp
      · obtain ⟨hmem, hlt'⟩ := hpoint s ⟨by linarith, by linarith⟩ τ ⟨le_of_lt hτ.1, h1⟩
        have hb := (hKC g D hg (le_of_lt hDpos) hD100 hgs hgj σ hσIcc z hz0 hz1 hzbd _
          ⟨le_trans hse hmem.1, hmem.2⟩ hlt').2.2.1
        have hτle : (0:ℝ) ≤ 1 - τ := by linarith
        have hwb : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
        calc ‖(Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
              Kvec n g u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i))‖
            = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * |(deriv (fun u : ℝ =>
                Kvec n g u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i|) := by
              rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hwb, abs_of_nonneg hτle]
          _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ‖deriv (fun u : ℝ =>
                Kvec n g u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))‖) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hτle) hwb
              exact norm_le_pi_norm (deriv (fun u : ℝ =>
                Kvec n g u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i
          _ ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ * (1 * (C + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ hwb
              calc (1 - τ) * ‖deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
                    (s + τ * (σ - s))‖
                  ≤ 1 * ‖deriv (fun u : ℝ => Kvec n g u σ (z 0) (z 1) (z 2) (z 3))
                    (s + τ * (σ - s))‖ :=
                    mul_le_mul_of_nonneg_right (by linarith [hτ.1] : (1:ℝ) - τ ≤ 1) (norm_nonneg _)
                _ ≤ 1 * (C + 1) := mul_le_mul_of_nonneg_left (le_trans hb (by linarith))
                    (by norm_num)
          _ = (Real.sqrt (τ * (1 - τ)))⁻¹ * (C + 1) := by ring
  have hpt2 : ∀ i : Fin 2, ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖(Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
          Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)) -
        (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
          Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i))‖ ≤
      (Real.sqrt (τ * (1 - τ)))⁻¹ * (C * D) := by
    intro i τ hτ
    rcases eq_or_lt_of_le hτ.2 with h1 | h1
    · subst h1
      have h0 : (Real.sqrt ((1:ℝ) * (1 - 1)))⁻¹ = 0 := by
        rw [show (1:ℝ) * (1 - 1) = 0 by norm_num, Real.sqrt_zero, inv_zero]
      rw [h0]; simp
    · have hwb : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hτle : (0:ℝ) ≤ 1 - τ := by linarith [hτ.1, h1]
      have hrewrite : ((Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
              Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)) -
            (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
              Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)))
          = (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) *
              (((deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
                (s + τ * (σ - s))) i) -
               ((deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3))
                (s + τ * (σ - s))) i))) := by ring
      rw [hrewrite, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hwb, abs_of_nonneg hτle]
      refine mul_le_mul_of_nonneg_left ?_ hwb
      refine le_trans (mul_le_mul_of_nonneg_right (by linarith [hτ.1] : (1:ℝ) - τ ≤ 1)
        (abs_nonneg _)) ?_
      rw [one_mul]
      have hab : ((deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
            (s + τ * (σ - s))) i) - ((deriv (fun u : ℝ =>
            Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)
          = ((deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
            (s + τ * (σ - s))) - (deriv (fun u : ℝ =>
            Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s)))) i := rfl
      rw [hab, ← Real.norm_eq_abs]
      obtain ⟨hmem, hlt'⟩ := hpoint s ⟨by linarith, by linarith⟩ τ ⟨hτ.1, h1⟩
      have hb := (hKC h D hh (le_of_lt hDpos) hD100 hsupp hjet σ hσIcc z hz0 hz1 hzbd _
        ⟨le_trans hse hmem.1, hmem.2⟩ hlt').2.2.2
      exact le_trans (norm_le_pi_norm (deriv (fun u : ℝ => Kvec n h u σ (z 0) (z 1) (z 2) (z 3))
        (s + τ * (σ - s)) - deriv (fun u : ℝ => Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3))
        (s + τ * (σ - s))) i) hb
  have hfinal : ∀ i : Fin 2,
      |deriv (fun u : ℝ => (G2 n h u σ (z 0) (z 1) (z 2) (z 3)) i) s -
        deriv (fun u : ℝ => (G2 n 0 u σ (z 0) (z 1) (z 2) (z 3)) i) s| ≤
        C * D * Real.pi := by
    intro i
    rw [hformula h hh hjet hsupp i, hformula 0 contDiff_const hjet0 hsupp0 i]
    have hIh := hIntF h hh hjet hsupp i
    have hI0 := hIntF 0 contDiff_const hjet0 hsupp0 i
    rw [← intervalIntegral.integral_sub hIh hI0, ← Real.norm_eq_abs]
    calc ‖∫ τ in (0:ℝ)..1, ((Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
            Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)) -
          (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
            Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)))‖
        ≤ ∫ τ in (0:ℝ)..1, ‖((Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
            Kvec n h u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)) -
          (Real.sqrt (τ * (1 - τ)))⁻¹ * ((1 - τ) * ((deriv (fun u : ℝ =>
            Kvec n 0 u σ (z 0) (z 1) (z 2) (z 3)) (s + τ * (σ - s))) i)))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ τ in (0:ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ * (C * D) :=
          intervalIntegral.integral_mono_on (by norm_num) (hIh.sub hI0).norm
            (Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const (C * D))
            (fun τ hτ => hpt2 i τ hτ)
      _ = C * D * Real.pi := by
          rw [intervalIntegral.integral_mul_const, abel_weight_integral]
          ring
  -- the manifest average agrees with the paper's one near `s`
  have hbridge : ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ 1 / 100) →
      Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau) → ∀ i : Fin 2,
      deriv (fun u : ℝ => (KernelExt.G2M n g u σ (z 0) (z 1) (z 2) (z 3)) i) s =
        deriv (fun u : ℝ => (G2 n g u σ (z 0) (z 1) (z 2) (z 3)) i) s := by
    intro g hg hg1 hgs i
    apply Filter.EventuallyEq.deriv_eq
    have hnhds : Set.Ioo (9 / 20 : ℝ) σ ∈ 𝓝 s :=
      IsOpen.mem_nhds isOpen_Ioo ⟨by linarith [hs.1], hsσ⟩
    filter_upwards [hnhds] with u hu
    have h1 : ∀ a ∈ Set.Icc u σ, 0 < krad g σ (-(z 0)) a := fun a ha =>
      (hposg g hg1 hgs σ hσIcc a ⟨le_trans (le_of_lt hu.1) ha.1, ha.2⟩).1
    have h2 : ∀ a ∈ Set.Icc u σ, 0 < krad g σ (z 1) a := fun a ha =>
      (hposg g hg1 hgs σ hσIcc a ⟨le_trans (le_of_lt hu.1) ha.1, ha.2⟩).2
    exact congrFun (Window.G2M_eq_G2 n hn hg (le_of_lt hu.2) (z 0) (z 1) (z 2) (z 3) h1 h2) i
  have hd : ∀ i : Fin 2,
      |deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) i) s -
        deriv (fun u : ℝ => (KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) i) s| ≤
        C * D * Real.pi := by
    intro i
    rw [hbridge h hh (hsmallg h hjet) hsupp i, hbridge 0 contDiff_const hsmall0 hsupp0 i]
    exact hfinal i
  have hTheta : ‖KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z‖ ≤ C * D * Real.pi := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    fin_cases j
    · show ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z) 0‖ ≤ C * D * Real.pi
      have h0 : (KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z) 0 = 0 := by
        simp [KernelExt.ThetaM, Pi.sub_apply]
      rw [h0, norm_zero]; positivity
    · show ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z) 1‖ ≤ C * D * Real.pi
      have h0 : (KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z) 1 = 0 := by
        simp [KernelExt.ThetaM, Pi.sub_apply]
      rw [h0, norm_zero]; positivity
    · show ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z) 2‖ ≤ C * D * Real.pi
      have h0 : (KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z) 2 =
          -((deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 0) s) -
            (deriv (fun u : ℝ => (KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 0) s)) := by
        simp only [KernelExt.ThetaM, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
        ring
      rw [h0, norm_neg, Real.norm_eq_abs]
      exact hd 0
    · show ‖(KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z) 3‖ ≤ C * D * Real.pi
      have h0 : (KernelExt.ThetaM n h s σ z - KernelExt.ThetaM n 0 s σ z) 3 =
          -((deriv (fun u : ℝ => (KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) 1) s) -
            (deriv (fun u : ℝ => (KernelExt.G2M n 0 u σ (z 0) (z 1) (z 2) (z 3)) 1) s)) := by
        simp only [KernelExt.ThetaM, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
        ring
      rw [h0, norm_neg, Real.norm_eq_abs]
      exact hd 1
  rw [hzdef] at hTheta
  calc ‖KernelExt.ThetaM n h s σ (baseState σ) - KernelExt.ThetaM n 0 s σ (baseState σ)‖
      ≤ C * D * Real.pi := hTheta
    _ = (C * Real.pi) * D := by ring

/-- **The frozen tail is small.**  For every `ε > 0` there is `δ > 0` such that for every smooth
bump `h` supported in the transition window `[1 - 2τ, 1 - τ]` whose derivatives up to order `n + 2`
are bounded by `δ` and every `s ∈ [1/2, 19/20]`, the `σ`-integral of the manifest `Θ`-defect over
the frozen tail `[19/20, 1]` (where the state is the unperturbed `baseState`) is smaller than `ε`
in norm. -/
theorem aw_frozen_tail_close (n : ℕ) (hn : 1 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20 : ℝ),
        ‖(∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
            (Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.baseState σ) -
             Work.OddVolterra.KernelExt.ThetaM n 0 s σ (Work.OddVolterra.baseState σ)))‖ < ε := by
  obtain ⟨K, hK0, hK⟩ := awft_thetaM_tail_bound n hn
  intro ε hε
  refine ⟨min (1 / 100) (20 * ε / (K + 1)), lt_min (by norm_num) (by positivity), ?_⟩
  intro h hh hsupp hjet s hs
  have hDpos : 0 < min (1 / 100) (20 * ε / (K + 1)) := lt_min (by norm_num) (by positivity)
  have hD100 : min (1 / 100) (20 * ε / (K + 1)) ≤ 1 / 100 := min_le_left _ _
  have hpt : ∀ σ ∈ Set.uIoc (19 / 20 : ℝ) 1,
      ‖(Work.OddVolterra.KernelExt.ThetaM n h s σ (Work.OddVolterra.baseState σ) -
        Work.OddVolterra.KernelExt.ThetaM n 0 s σ (Work.OddVolterra.baseState σ))‖ ≤
      K * min (1 / 100) (20 * ε / (K + 1)) := by
    intro σ hσ
    rw [Set.uIoc_of_le (by norm_num : (19:ℝ) / 20 ≤ 1)] at hσ
    exact hK h (min (1 / 100) (20 * ε / (K + 1))) hh hDpos hD100 hsupp hjet s hs σ
      ⟨hσ.1, hσ.2⟩
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (19 / 20 : ℝ)) (b := 1) (C := K * min (1 / 100) (20 * ε / (K + 1))) hpt
  have hlen : |(1:ℝ) - 19 / 20| = 1 / 20 := by
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 - 19 / 20)]; norm_num
  rw [hlen] at hmain
  refine lt_of_le_of_lt hmain ?_
  have hle : min (1 / 100) (20 * ε / (K + 1)) ≤ 20 * ε / (K + 1) := min_le_right _ _
  have h1 : K * min (1 / 100) (20 * ε / (K + 1)) ≤ K * (20 * ε / (K + 1)) :=
    mul_le_mul_of_nonneg_left hle hK0
  have h2 : K * (20 * ε / (K + 1)) / 20 = ε * (K / (K + 1)) := by
    field_simp
  have h3 : K / (K + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have h4 : ε * (K / (K + 1)) < ε * 1 := mul_lt_mul_of_pos_left h3 hε
  linarith [h1, h2, h4]

/-- The zero function is `C¹`-small. -/
lemma awft_hsmall_zero : ∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) x| ≤ 1 / 100 := by
  intro k hk x
  have h0 : iteratedDeriv k (0 : ℝ → ℝ) x = 0 := by
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split <;> simp
  rw [h0, abs_zero]; norm_num

/-- **The frozen tail is small, in the paper's own kernel `Θ`.**

Same statement as `aw_frozen_tail_close` with the raw datum `Theta` in place of the manifest
`ThetaM`.  On the tail `σ ∈ (19/20, 1]` and `s ∈ [1/2, 19/20]` the two agree
(`Window.manifest_eq.ThetaM_eq_Theta`, the radicands staying positive by
`Existence.krad_pos_state_region`), so the manifest estimate transfers verbatim. -/
theorem awft_frozen_tail_close_Theta (n : ℕ) (hn : 1 ≤ n) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ s ∈ Set.Icc (1 / 2 : ℝ) (19 / 20 : ℝ),
        ‖(∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
            (Work.OddVolterra.Theta n h s σ (Work.OddVolterra.baseState σ) -
             Work.OddVolterra.Theta n 0 s σ (Work.OddVolterra.baseState σ)))‖ < ε := by
  intro ε hε
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := aw_frozen_tail_close n hn ε hε
  set δ : ℝ := min (1 / 100) (min (1 / 20) δ₀) with hδdef
  have hδpos : 0 < δ := lt_min (by norm_num) (lt_min (by norm_num) hδ₀pos)
  have hδ100 : δ ≤ 1 / 100 := le_trans (le_of_eq hδdef.symm) (min_le_left _ _)
  have hδ20 : δ ≤ 1 / 20 :=
    le_trans (le_of_eq hδdef.symm) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδδ₀ : δ ≤ δ₀ :=
    le_trans (le_of_eq hδdef.symm) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨δ, hδpos, ?_⟩
  intro h hh hsupp hjet s hs
  have hsmall : ∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
    fun k hk x => le_trans (hjet k (le_trans hk (by omega)) x) hδ100
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) := by
    intro x hx
    rw [Function.mem_support] at hx
    exact absurd rfl hx
  have hkey : ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ 1 / 100) →
      Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      ∀ σ ∈ Set.Ioc (19 / 20 : ℝ) 1,
        KernelExt.ThetaM n g s σ (baseState σ) = Work.OddVolterra.Theta n g s σ (baseState σ) := by
    intro g hg hg1 hgs σ hσ
    have hσIcc : σ ∈ Set.Icc (19 / 20 : ℝ) 1 := ⟨le_of_lt hσ.1, hσ.2⟩
    have hsσ : s < σ := by linarith [hs.2, hσ.1]
    have hzball : baseState σ ∈ Metric.closedBall (baseState σ) (1 / 2) := by
      rw [Metric.mem_closedBall, dist_self]; norm_num
    obtain ⟨hz0, hz1, -⟩ :=
      Window.state_ball_box' (b := 19 / 20) (by norm_num) (by norm_num) σ hσIcc
        (baseState σ) hzball
    have h1 : ∀ a ∈ Set.Icc (s - δ) σ, 0 < krad g σ (-((baseState σ) 0)) a := by
      intro a ha
      have ha9 : (9 / 20 : ℝ) ≤ a := by linarith [ha.1, hs.1, hδ20]
      have ht : (1 / 5 : ℝ) ≤ |(-((baseState σ) 0))| := by
        rw [abs_neg, abs_of_nonneg (by linarith [hz0])]; exact hz0
      exact krad_pos_state_region hgs hg1 (by norm_num) ha9 ha.2 hσ.2 ht
    have h2 : ∀ a ∈ Set.Icc (s - δ) σ, 0 < krad g σ ((baseState σ) 1) a := by
      intro a ha
      have ha9 : (9 / 20 : ℝ) ≤ a := by linarith [ha.1, hs.1, hδ20]
      have ht : (1 / 5 : ℝ) ≤ |((baseState σ) 1)| := by
        rw [abs_of_nonneg (by linarith [hz1])]; exact hz1
      exact krad_pos_state_region hgs hg1 (by norm_num) ha9 ha.2 hσ.2 ht
    exact Window.ThetaM_eq_Theta n hn hg hsσ hδpos (baseState σ) h1 h2
  have hcongr : (∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
        (Work.OddVolterra.Theta n h s σ (baseState σ) -
         Work.OddVolterra.Theta n 0 s σ (baseState σ))) =
      ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
        (KernelExt.ThetaM n h s σ (baseState σ) - KernelExt.ThetaM n 0 s σ (baseState σ)) := by
    refine intervalIntegral.integral_congr_ae' ?_ ?_
    · filter_upwards with σ hσ
      rw [← hkey h hh hsmall hsupp σ hσ,
        ← hkey (0 : ℝ → ℝ) contDiff_const awft_hsmall_zero hsupp0 σ hσ]
    · filter_upwards with σ hσ
      exact absurd hσ.1 (by linarith [hσ.2])
  rw [hcongr]
  exact hδ₀ h hh hsupp (fun k hk x => le_trans (hjet k hk x) hδδ₀) s hs

end

end Work.OddVolterra.Existence
