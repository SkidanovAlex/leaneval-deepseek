import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Window.window_tail_glue

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

-- This is `Work.OddVolterra.Window.window_tail_glue` (in
-- `Submission/Work/OddVolterra/Window/window_tail_glue.lean`, already proved) with the fixed
-- closeness constant `1/100` replaced throughout by a parameter `ρ ≤ 1/2`.
-- Exactly the same proof works: `ρ` is used only to place the state in the ball of radius `1/2`
-- around `baseState` (for `eqOn_of_solves`) and to bound the final distance.
theorem window_tail_glue_rho (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∀ Z : ℝ → Work.OddVolterra.St,
      ContinuousOn Z (Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ)) →
      (∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ),
        Work.OddVolterra.Godd n h s (Z s) =
          (∫ σ in s..(19 / 20 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
            (Work.OddVolterra.Xi n h s +
              ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
                Work.OddVolterra.Theta n h s σ (Work.OddVolterra.baseState σ))) →
      (∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20 : ℝ),
        dist (Z s) (Work.OddVolterra.baseState s) ≤ ρ) →
      Z (19 / 20 : ℝ) = Work.OddVolterra.baseState (19 / 20 : ℝ) →
      ∃ Z' : ℝ → Work.OddVolterra.St,
        ContinuousOn Z' (Set.Icc (7 / 10 : ℝ) 1) ∧
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
          Work.OddVolterra.Godd n h s (Z' s) =
            (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z' σ)) +
              Work.OddVolterra.Xi n h s) ∧
        (∀ s : ℝ, 9 / 10 ≤ s → Z' s = Work.OddVolterra.baseState s) ∧
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
          dist (Z' s) (Work.OddVolterra.baseState s) ≤ ρ) := by
  intro Z hZc hZeq hZdist hZend
  have hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (by omega) s
  -- the quantitative data of `Θ` and `Godd` on the state ball around `baseState`
  obtain ⟨L, hL, C, hC, hLip, hBd, hCont⟩ :=
    Existence.theta_lipschitz_state_ball n hn hh hsupp hsmall2 (b := (7 / 10 : ℝ))
      (by norm_num) (by norm_num)
  obtain ⟨c, hc, hInj⟩ :=
    Existence.godd_injective_modulus_state_ball_compat n hn hh hsupp hsmall2
      (b := (7 / 10 : ℝ)) (by norm_num) (by norm_num)
  -- the extension of `Z` past `19/20` by the unperturbed state
  let Zh : ℝ → St := fun s => if s < (19 / 20 : ℝ) then Z s else baseState s
  have hZh_lt : ∀ s : ℝ, s < (19 / 20 : ℝ) → Zh s = Z s := by
    intro s hs
    show (if s < (19 / 20 : ℝ) then Z s else baseState s) = Z s
    rw [if_pos hs]
  have hZh_ge : ∀ s : ℝ, (19 / 20 : ℝ) ≤ s → Zh s = baseState s := by
    intro s hs
    show (if s < (19 / 20 : ℝ) then Z s else baseState s) = baseState s
    rw [if_neg (not_lt.mpr hs)]
  -- continuity of the extension
  have hZh_cont : ContinuousOn Zh (Set.Icc (7 / 10 : ℝ) 1) := by
    have h1 : ContinuousOn Zh (Set.Icc (7 / 10 : ℝ) (19 / 20)) :=
      (hZc.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)).congr (fun s hs => by
        rcases lt_or_eq_of_le hs.2 with h | h
        · exact hZh_lt s h
        · rw [h]
          exact (hZh_ge (19 / 20) le_rfl).trans hZend.symm)
    have h2 : ContinuousOn Zh (Set.Icc (19 / 20 : ℝ) 1) :=
      (Window.continuous_baseState.continuousOn).congr (fun s hs => hZh_ge s hs.1)
    have hunion := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Set.Icc_union_Icc_eq_Icc (by norm_num : (7 / 10 : ℝ) ≤ 19 / 20)
      (by norm_num : (19 / 20 : ℝ) ≤ 1)] at hunion
  -- the extension stays in the state ball
  have hZh_ball : ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1, ‖Zh s - baseState s‖ ≤ 1 / 2 := by
    intro s hs
    by_cases h : s < 19 / 20
    · rw [hZh_lt s h, ← dist_eq_norm]
      exact le_trans (hZdist s ⟨hs.1, le_of_lt h⟩) hρ2
    · rw [hZh_ge s (not_lt.mp h), sub_self, norm_zero]
      norm_num
  -- interval-integrability of the `Θ`-integrand along the extension
  have hintZh : ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
      IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Zh σ)) volume s 1 := by
    intro s hs
    exact Existence.intervalIntegrable_Theta_integrand (n := n) (h := h) (b := (7 / 10 : ℝ))
      hBd hCont ⟨hs.1, le_trans hs.2 (by norm_num)⟩ (le_trans hs.2 (by norm_num)) le_rfl
      (hZh_cont.mono (Set.Icc_subset_Icc hs.1 le_rfl))
      (fun σ hσ => hZh_ball σ ⟨le_trans hs.1 hσ.1, hσ.2⟩)
  -- the truncated equation upgrades to the full one on the window
  have hZh_eq : ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
      Godd n h s (Zh s) = (∫ σ in s..(1 : ℝ), Theta n h s σ (Zh σ)) + Xi n h s := by
    intro s hs
    have hint := hintZh s hs
    have hA : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Zh σ)) volume s (19 / 20) :=
      hint.mono_set (by
        rw [Set.uIcc_of_le hs.2,
          Set.uIcc_of_le (le_trans hs.2 (by norm_num : (19 / 20 : ℝ) ≤ 1))]
        exact Set.Icc_subset_Icc le_rfl (by norm_num))
    have hB : IntervalIntegrable (fun σ : ℝ => Theta n h s σ (Zh σ)) volume (19 / 20) 1 :=
      hint.mono_set (by
        rw [Set.uIcc_of_le (by norm_num : (19 / 20 : ℝ) ≤ 1),
          Set.uIcc_of_le (le_trans hs.2 (by norm_num : (19 / 20 : ℝ) ≤ 1))]
        exact Set.Icc_subset_Icc (by linarith [hs.2]) le_rfl)
    have hsplit : (∫ σ in s..(1 : ℝ), Theta n h s σ (Zh σ))
        = (∫ σ in s..(19 / 20 : ℝ), Theta n h s σ (Zh σ))
          + (∫ σ in (19 / 20 : ℝ)..(1 : ℝ), Theta n h s σ (Zh σ)) :=
      (intervalIntegral.integral_add_adjacent_intervals hA hB).symm
    have hc1 : (∫ σ in s..(19 / 20 : ℝ), Theta n h s σ (Zh σ))
        = ∫ σ in s..(19 / 20 : ℝ), Theta n h s σ (Z σ) :=
      intervalIntegral.integral_congr_Ioo_of_le hs.2 (fun σ hσ => by rw [hZh_lt σ hσ.2])
    have hc2 : (∫ σ in (19 / 20 : ℝ)..(1 : ℝ), Theta n h s σ (Zh σ))
        = ∫ σ in (19 / 20 : ℝ)..(1 : ℝ), Theta n h s σ (baseState σ) :=
      intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        (fun σ hσ => by rw [hZh_ge σ hσ.1.le])
    have hZh_s : Zh s = Z s := by
      rcases lt_or_eq_of_le hs.2 with h | h
      · exact hZh_lt s h
      · rw [hZh_ge s (le_of_eq h.symm), h]
        exact hZend.symm
    rw [hZh_s, hZeq s hs, hsplit, hc1, hc2]
    abel
  -- the same equation on the whole right half-window, via the unperturbed identity
  have hZh_eq_full : ∀ s ∈ Set.Ioo (9 / 10 : ℝ) 1,
      Godd n h s (Zh s) = (∫ σ in s..(1 : ℝ), Theta n h s σ (Zh σ)) + Xi n h s := by
    intro s hs
    rcases lt_or_ge s (19 / 20) with hlt | hle
    · exact hZh_eq s ⟨by linarith [hs.1], le_of_lt hlt⟩
    · have hstau : (1 : ℝ) - Work.OddVolterra.tau < s := by
        rw [Window.one_sub_tau_eq_window]; linarith [hle]
      have h1 : Zh s = baseState s := hZh_ge s hle
      have h2 : (∫ σ in s..(1 : ℝ), Theta n h s σ (Zh σ))
          = ∫ σ in s..(1 : ℝ), Theta n h s σ (baseState σ) :=
        intervalIntegral.integral_congr_Ioo_of_le hs.2.le
          (fun σ hσ => by rw [hZh_ge σ (le_of_lt (lt_of_le_of_lt hle hσ.1))])
      rw [h1, h2]
      exact Window.base_volterra_right n hn hsupp hstau hs.2
  -- uniqueness on the right half-window
  have huniq : ∀ s ∈ Set.Ioo (9 / 10 : ℝ) 1, Zh s = baseState s :=
    Existence.eqOn_of_solves (n := n) (h := h) (b := (9 / 10 : ℝ)) hL hc (by norm_num)
      (by norm_num)
      (fun s hs σ hσ z hz z' hz' => hLip s ⟨by linarith [hs.1], hs.2⟩ σ hσ z hz z' hz')
      (fun s hs σ hσ z hz => hBd s ⟨by linarith [hs.1], hs.2⟩ σ hσ z hz)
      (fun s hs => hCont s ⟨by linarith [hs.1], hs.2⟩)
      (fun s hs z hz z' hz' => hInj s ⟨by linarith [hs.1], hs.2⟩ z hz z' hz')
      (hZh_cont.mono (Set.Icc_subset_Icc (by norm_num) le_rfl))
      Window.continuous_baseState.continuousOn
      (fun s hs => hZh_eq_full s hs)
      (fun s hs => Window.base_volterra_right n hn hsupp
        (by rw [Window.one_sub_tau_eq_window]; linarith [hs.1]) hs.2)
      (fun s hs => hZh_ball s ⟨by linarith [hs.1], hs.2⟩)
      (fun s _ => by simp)
  -- hence `Z` and `baseState` agree on the middle piece
  have hZ_base : ∀ s ∈ Set.Ioo (9 / 10 : ℝ) (19 / 20), Z s = baseState s := by
    intro s hs
    have h1 : Zh s = Z s := hZh_lt s hs.2
    rw [← h1]
    exact huniq s ⟨hs.1, by linarith [hs.2]⟩
  -- and, by continuity, at the left endpoint of that piece
  have hZ9 : Z (9 / 10 : ℝ) = baseState (9 / 10 : ℝ) := by
    have hclosed : IsClosed {x : ℝ | x ∈ Set.Icc (9 / 10 : ℝ) (19 / 20) ∧ Z x = baseState x} :=
      IsClosed.isClosed_eq isClosed_Icc
        (hZc.mono (Set.Icc_subset_Icc (by norm_num) le_rfl))
        Window.continuous_baseState.continuousOn
    have hsub : Set.Ioo (9 / 10 : ℝ) (19 / 20) ⊆
        {x : ℝ | x ∈ Set.Icc (9 / 10 : ℝ) (19 / 20) ∧ Z x = baseState x} :=
      fun x hx => ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, hZ_base x hx⟩
    have hmem : (9 / 10 : ℝ) ∈ closure (Set.Ioo (9 / 10 : ℝ) (19 / 20)) := by
      rw [closure_Ioo (by norm_num : (9 / 10 : ℝ) ≠ 19 / 20)]
      exact ⟨le_rfl, by norm_num⟩
    exact (closure_minimal hsub hclosed hmem).2
  -- the glued curve
  let Z' : ℝ → St := fun s => if s < (9 / 10 : ℝ) then Z s else baseState s
  have hZ'lt : ∀ s : ℝ, s < (9 / 10 : ℝ) → Z' s = Z s := by
    intro s hs
    show (if s < (9 / 10 : ℝ) then Z s else baseState s) = Z s
    rw [if_pos hs]
  have hZ'ge : ∀ s : ℝ, (9 / 10 : ℝ) ≤ s → Z' s = baseState s := by
    intro s hs
    show (if s < (9 / 10 : ℝ) then Z s else baseState s) = baseState s
    rw [if_neg (not_lt.mpr hs)]
  have hZ'Zh : ∀ s : ℝ, Z' s = Zh s := by
    intro s
    rcases lt_trichotomy s (9 / 10) with h | h | h
    · rw [hZ'lt s h, hZh_lt s (by linarith)]
    · rw [h, hZ'ge (9 / 10) le_rfl, hZh_lt (9 / 10) (by norm_num), hZ9]
    · rw [hZ'ge s h.le]
      by_cases hc : s < 19 / 20
      · rw [hZh_lt s hc]
        exact (hZ_base s ⟨h, hc⟩).symm
      · rw [hZh_ge s (not_lt.mp hc)]
  refine ⟨Z', ?_, ?_, ?_, ?_⟩
  · -- continuity of the glued curve
    have h1 : ContinuousOn Z' (Set.Icc (7 / 10 : ℝ) (9 / 10)) :=
      (hZc.mono (Set.Icc_subset_Icc (by norm_num) (by norm_num))).congr (fun s hs => by
        rcases lt_or_eq_of_le hs.2 with h | h
        · exact hZ'lt s h
        · rw [h]
          exact (hZ'ge (9 / 10) le_rfl).trans hZ9.symm)
    have h2 : ContinuousOn Z' (Set.Icc (9 / 10 : ℝ) 1) :=
      (Window.continuous_baseState.continuousOn).congr (fun s hs => hZ'ge s hs.1)
    have hunion := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Set.Icc_union_Icc_eq_Icc (by norm_num : (7 / 10 : ℝ) ≤ 9 / 10)
      (by norm_num : (9 / 10 : ℝ) ≤ 1)] at hunion
  · -- the full equation on `[7/10, 9/10]`
    intro s hs
    have h1 : Z' s = Zh s := hZ'Zh s
    have h2 : (∫ σ in s..(1 : ℝ), Theta n h s σ (Z' σ))
        = ∫ σ in s..(1 : ℝ), Theta n h s σ (Zh σ) :=
      intervalIntegral.integral_congr (fun σ _ => by rw [hZ'Zh σ])
    rw [h1, h2]
    exact hZh_eq s ⟨hs.1, le_trans hs.2 (by norm_num)⟩
  · -- the glued curve is the unperturbed state past `9/10`
    intro s hs
    exact hZ'ge s hs
  · -- and stays in the ball
    intro s hs
    rcases lt_or_eq_of_le hs.2 with h | h
    · rw [hZ'lt s h]
      exact hZdist s ⟨hs.1, le_trans hs.2 (by norm_num)⟩
    · rw [h, hZ'ge (9 / 10) le_rfl, dist_self]
      exact hρ.le

end

end Work.OddVolterra.WinData
