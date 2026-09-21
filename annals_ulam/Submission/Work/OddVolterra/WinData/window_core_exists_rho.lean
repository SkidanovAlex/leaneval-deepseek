import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Window.window_core_exists

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra
open Work.OddVolterra.Window

-- This is `Work.OddVolterra.Window.window_core_exists` (in
-- `Submission/Work/OddVolterra/Window/window_core_exists.lean`, sorry-free) with the fixed
-- closeness constant `1/100` of the conclusion replaced by a parameter `ρ`.
-- The proof is the same proof with `εeng` shrunk by an extra factor `ρ/(2*B*M₀*EE)`.
-- The only constraint is `ρ ≤ 1/100`, which is needed because the conversion of the cut-off
-- solution back to the paper's `Godd` uses that the state is within `1/100` of `baseState`.
theorem window_core_exists_rho (n : ℕ) (hn : 1 ≤ n) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 100) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 1 - 2 * Work.OddVolterra.tau ≤ s →
        s < 1 - 2 * Work.OddVolterra.tau + η → h s = 0) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ ε) →
      h 0 = 0 → h ≠ 0 →
      ∃ Z : ℝ → Work.OddVolterra.St,
        ContinuousOn Z (Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ)) ∧
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ),
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(19 / 20 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              (Work.OddVolterra.Xi n h s +
                ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
                  Work.OddVolterra.Theta n h s σ (Work.OddVolterra.baseState σ))) ∧
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ),
          dist (Z s) (Work.OddVolterra.baseState s) ≤ ρ) ∧
        Z (19 / 20 : ℝ) = Work.OddVolterra.baseState (19 / 20 : ℝ) := by
  classical
  obtain ⟨hΘcont, L, hL0, hΘlip⟩ := TW2_regular n hn
  obtain ⟨Cg, C₃, hCg0, hC₃0, hdcl⟩ := GW2_fderiv_close_unif n hn
  obtain ⟨A, B, hB, hAspec, hAcont, hAb⟩ :=
    Work.OddVolterra.Existence.odd_linearization n hn wLeft wRight wLeft_pos wLeft_le_wRight
      (le_of_lt wRight_lt_one)
  set M₀ : ℝ := 2 + (wRight - wLeft) with hM₀def
  set lam : ℝ := 4 * B * L + 1 with hlamdef
  set EE : ℝ := Real.exp (lam * (wRight - wLeft)) with hEEdef
  have hEEpos : 0 < EE := by rw [hEEdef]; exact Real.exp_pos _
  have hM₀pos : 0 < M₀ := by rw [hM₀def]; linarith [wLeft_le_wRight]
  have hpos2 : 0 < 2 * B * M₀ * EE := by positivity
  have hden1 : 0 < 200 * B * M₀ * EE := by positivity
  have hden2 : 0 < 8 * B * (2 * B * Cg * M₀ * EE + 1) := by positivity
  set εeng : ℝ := min (1 / 100) (min (ρ / (2 * B * M₀ * EE))
    (1 / (8 * B * (2 * B * Cg * M₀ * EE + 1)))) with hεengdef
  have hεengpos : 0 < εeng := by
    rw [hεengdef]
    exact lt_min (by norm_num) (lt_min (div_pos hρ hpos2) (div_pos one_pos hden2))
  obtain ⟨γ, hγ0, hγc⟩ := wc_GW2_close n hn εeng hεengpos
  obtain ⟨δΘ, hδΘ0, hδΘc⟩ := wc_TW2_close n hn εeng hεengpos
  obtain ⟨δΞ, hδΞ0, hδΞc⟩ := wc_XW_close n hn εeng hεengpos
  set δ₃ : ℝ := εeng / (C₃ + 1) with hδ₃def
  have hδ₃0 : 0 < δ₃ := by rw [hδ₃def]; positivity
  set e0 : ℝ := min (1 / 100) (min γ (min δΘ (min δΞ δ₃))) with he0def
  have he0pos : 0 < e0 := by
    rw [he0def]
    exact lt_min (by norm_num) (lt_min hγ0 (lt_min hδΘ0 (lt_min hδΞ0 hδ₃0)))
  have he0_100 : e0 ≤ 1 / 100 := by rw [he0def]; exact min_le_left _ _
  have he0_γ : e0 ≤ γ := by
    rw [he0def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have he0_δΘ : e0 ≤ δΘ := by
    rw [he0def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have he0_δΞ : e0 ≤ δΞ := by
    rw [he0def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have he0_δ₃ : e0 ≤ δ₃ := by
    rw [he0def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨e0, he0pos, ?_⟩
  intro h hh hsupp _hη hsmall _h0 _hne
  have hsm100 : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hsmall k hk s) he0_100
  have hsmγ : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ γ :=
    fun k hk s => le_trans (hsmall k hk s) he0_γ
  have hsmδΘ : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δΘ :=
    fun k hk s => le_trans (hsmall k hk s) he0_δΘ
  have hsmδΞ : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δΞ :=
    fun k hk s => le_trans (hsmall k hk s) he0_δΞ
  have hsmδ₃ : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ₃ :=
    fun k hk s => le_trans (hsmall k hk s) he0_δ₃
  have hsm1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsm100 k (by omega) s
  have hsm2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsm100 k (by omega) s
  -- the engine thresholds
  have hεe100 : εeng ≤ 1 / 100 := min_le_left _ _
  have hεedenρ : εeng ≤ ρ / (2 * B * M₀ * EE) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hεeden1 : εeng ≤ 1 / (200 * B * M₀ * EE) := by
    refine le_trans hεedenρ ?_
    have hb : ρ / (2 * B * M₀ * EE) ≤ 1 / (200 * B * M₀ * EE) := by
      have h1 : (1 : ℝ) / (200 * B * M₀ * EE) = (1 / 100) / (2 * B * M₀ * EE) := by
        field_simp
        ring
      rw [h1]
      exact div_le_div_of_nonneg_right hρ1 hpos2.le
    exact hb
  have hεeden2 : εeng ≤ 1 / (8 * B * (2 * B * Cg * M₀ * EE + 1)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hε1 : εeng < 1 := by linarith [hεe100]
  have hε2 : εeng < 1 / (2 * B * M₀ * EE) :=
    lt_of_le_of_lt hεeden1 (by
      refine one_div_lt_one_div_of_lt hpos2 ?_
      nlinarith [hpos2])
  have hε3 : εeng < 1 / (4 * B * (2 * B * Cg * M₀ * EE + 1)) :=
    lt_of_le_of_lt hεeden2 (by
      have hpos : 0 < 4 * B * (2 * B * Cg * M₀ * EE + 1) := by positivity
      refine one_div_lt_one_div_of_lt hpos ?_
      nlinarith [hpos])
  -- engine hypotheses
  have hAspec' : ∀ s ∈ Set.Icc wLeft wRight,
      (A s : St →L[ℝ] St) = fderiv ℝ (fun z => GW2 n 0 s z) (baseState s) := by
    intro s hs
    rw [hAspec s hs]
    exact (wc_eventuallyEq_GW2_Godd (h := fun _ : ℝ => (0 : ℝ)) n hs).fderiv_eq.symm
  have hGcd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × St => GW2 n h p.1 p.2) :=
    wc_GW2_contDiff n hh hsupp hsm1
  have hGcont : Continuous (fun p : ℝ × St => GW2 n h p.1 p.2) := hGcd.continuous
  have hΞcont : Continuous (XW n h) := XW_continuous n hn hh hsupp hsm100
  have hZ₀cont : ContinuousOn baseState (Set.Icc wLeft wRight) :=
    wdr_contDiff_baseState.continuous.continuousOn
  have hΘ0cont : Continuous (fun p : ℝ × ℝ × St => TW2 n 0 p.1 p.2.1 p.2.2) :=
    hΘcont (fun _ : ℝ => (0 : ℝ)) contDiff_const (fun x hx => absurd rfl hx)
      (fun k hk s => by simp)
  have hbase : ∀ s ∈ Set.Icc wLeft wRight,
      GW2 n 0 s (baseState s) =
        (∫ σ in s..wRight, TW2 n 0 s σ (baseState σ)) + XW n 0 s := wc_base_identity n hn
  have hΘcontinst : Continuous (fun p : ℝ × ℝ × St => TW2 n h p.1 p.2.1 p.2.2) :=
    hΘcont h hh hsupp hsm100
  have hΘlip' : ∀ s ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
      ∀ z ∈ Metric.closedBall (baseState σ) 1, ∀ z' ∈ Metric.closedBall (baseState σ) 1,
      ‖TW2 n h s σ z - TW2 n h s σ z'‖ ≤ L * ‖z - z'‖ :=
    hΘlip h hh hsupp hsm100
  have hdiff : ∀ s ∈ Set.Icc wLeft wRight, ∀ z ∈ Metric.closedBall (baseState s) 1,
      DifferentiableAt ℝ (fun w => GW2 n h s w) z := by
    intro s hs z _hz
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : St => (s, w)) z := by fun_prop
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : St => GW2 n h s w) z := by
      have hc := (hGcd.contDiffAt).comp z h1
      have h' : (fun p : ℝ × St => GW2 n h p.1 p.2) ∘ (fun w : St => (s, w)) =
          fun w : St => GW2 n h s w := by funext w; rfl
      rwa [h'] at hc
    exact h2.differentiableAt (by simp)
  have hΞc : ∀ s ∈ Set.Icc wLeft wRight, dist (XW n h s) (XW n 0 s) < εeng :=
    hδΞc h hh hsupp hsmδΞ
  have hGc : ∀ s ∈ Set.Icc wLeft wRight, ∀ z ∈ Metric.closedBall (baseState s) 1,
      dist (GW2 n h s z) (GW2 n 0 s z) < εeng := hγc h hh hsupp hsmγ
  have hΘc : ∀ s ∈ Set.Icc wLeft wRight, ∀ σ ∈ Set.Icc wLeft wRight,
      ∀ z ∈ Metric.closedBall (baseState σ) 1,
      dist (TW2 n h s σ z) (TW2 n 0 s σ z) < εeng := hδΘc h hh hsupp hsmδΘ
  have hδ₃_le : δ₃ ≤ 1 / 100 := by
    rw [hδ₃def]
    refine le_trans (div_le_self hεengpos.le (by linarith [hC₃0])) ?_
    exact hεe100
  have hder : ∀ s ∈ Set.Icc wLeft wRight, ∀ z ∈ Metric.closedBall (baseState s) 1,
      ‖fderiv ℝ (fun w => GW2 n h s w) z - (A s : St →L[ℝ] St)‖
        ≤ Cg * ‖z - baseState s‖ + εeng := by
    intro s hs z hz
    have h1 := hdcl δ₃ hδ₃0 hδ₃_le h hh hsupp hsmδ₃ s hs z hz
    rw [hAspec' s hs]
    have hle : C₃ * δ₃ ≤ εeng := by
      have hC3p : (0 : ℝ) < C₃ + 1 := by linarith [hC₃0]
      have h2 : (C₃ + 1) * δ₃ = εeng := by
        rw [hδ₃def, mul_comm, div_mul_cancel₀ _ (ne_of_gt hC3p)]
      have hmono : C₃ * δ₃ ≤ (C₃ + 1) * δ₃ :=
        mul_le_mul_of_nonneg_right (by linarith [hC₃0]) hδ₃0.le
      linarith [hmono, h2]
    linarith
  obtain ⟨Z, hZc, hZsolve, hZd⟩ :=
    Work.VolterraLong.volterra_long_exists_eps (E := St) (a := wLeft) (b := wRight)
      wLeft_le_wRight A (fun s z => GW2 n 0 s z) (fun s z => GW2 n h s z)
      (fun s σ z => TW2 n 0 s σ z) (fun s σ z => TW2 n h s σ z)
      (XW n 0) (XW n h) baseState
      hB hL0 hCg0 hAspec' hAcont hAb hGcont hΘcontinst hΞcont hZ₀cont hΘ0cont hbase hΘlip'
      hdiff lam M₀ EE hlamdef hM₀def hEEdef
      hεengpos hε1 hε2 hε3 hΞc hGc hΘc hder
  -- the conclusion
  have hZd' : ∀ s ∈ Set.Icc wLeft wRight, dist (Z s) (baseState s) ≤ ρ := by
    intro s hs
    have hk : (2 * B * M₀ * EE) * (ρ / (2 * B * M₀ * EE)) = ρ := by
      have hne : (2 * B * M₀ * EE) ≠ 0 := ne_of_gt hpos2
      field_simp
    calc dist (Z s) (baseState s) ≤ 2 * B * M₀ * EE * εeng := hZd s hs
      _ ≤ (2 * B * M₀ * EE) * (ρ / (2 * B * M₀ * EE)) :=
          mul_le_mul_of_nonneg_left hεedenρ hpos2.le
      _ = ρ := hk
  have hZdist : ∀ s ∈ Set.Icc wLeft wRight, ‖Z s - baseState s‖ ≤ 1 / 100 := by
    intro s hs
    rw [← dist_eq_norm]
    exact le_trans (hZd' s hs) hρ1
  have hZeq : ∀ s ∈ Set.Icc wLeft wRight,
      Godd n h s (Z s) = (∫ σ in s..wRight, Theta n h s σ (Z σ)) +
        (Xi n h s + ∫ σ in wRight..(1 : ℝ), Theta n h s σ (baseState σ)) := by
    intro s hs
    have hZs := hZsolve s hs
    dsimp only at hZs
    rw [wc_GW2_eq_Godd_of_close n hs (hZdist s hs), wc_XW_eq n hs] at hZs
    have hint : (∫ σ in s..wRight, TW2 n h s σ (Z σ))
        = ∫ σ in s..wRight, Theta n h s σ (Z σ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with σ hσ
      rw [Set.uIoc_of_le hs.2] at hσ
      have hσw : σ ∈ Set.Icc wLeft wRight := ⟨le_trans hs.1 hσ.1.le, hσ.2⟩
      exact wc_TW2_eq_Theta_of_close n hs hσw hσ.1 (hZdist σ hσw)
    rw [hint] at hZs
    exact hZs
  have hend : Z wRight = baseState wRight := by
    have hwmem : wRight ∈ Set.Icc wLeft wRight := ⟨wLeft_le_wRight, le_rfl⟩
    have h1 := hZeq wRight hwmem
    rw [intervalIntegral.integral_same, zero_add] at h1
    have h2 : Xi n h wRight + (∫ σ in wRight..(1 : ℝ), Theta n h wRight σ (baseState σ))
        = Godd n h wRight (baseState wRight) :=
      (add_comm _ _).trans (wc_base_volterra_right n hn hsupp).symm
    rw [h2] at h1
    obtain ⟨c, hc0, hcinj⟩ :=
      Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat n hn hh hsupp hsm2
        wRight_pos (le_of_lt wRight_lt_one)
    have hZin : Z wRight ∈ Metric.closedBall (baseState wRight) (1 / 2) := by
      rw [Metric.mem_closedBall]
      exact le_trans (hZd' wRight hwmem) (by linarith)
    have hBin : baseState wRight ∈ Metric.closedBall (baseState wRight) (1 / 2) := by
      rw [Metric.mem_closedBall, dist_self]; norm_num
    have h3 := hcinj wRight ⟨le_refl wRight, le_of_lt wRight_lt_one⟩ (Z wRight) hZin
      (baseState wRight) hBin
    rw [h1, sub_self, norm_zero] at h3
    have h4 : ‖Z wRight - baseState wRight‖ = 0 :=
      le_antisymm (by nlinarith [hc0, norm_nonneg (Z wRight - baseState wRight), h3])
        (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h4)
  exact ⟨Z, hZc, hZeq, hZd', hend⟩

end

end Work.OddVolterra.WinData
