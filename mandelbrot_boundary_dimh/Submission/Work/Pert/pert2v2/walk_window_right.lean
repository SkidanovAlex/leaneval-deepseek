import Mathlib
import Submission.Work.Pert.pert2v2.walk_right_deep

namespace Work.Pert.pert2v2

/-!
# `Work.Pert.pert2v2.walk_window_right`: the right walk lands in the window `[0,2]`

This is the *windowed* form of `walk_right_deep` (which lands only in `|w.re - x₀| ≤ 3` for a
caller-chosen `x₀`).  With `x₀ = -1` the stopping rule of that walk ("first time the real part
drops below `x₀ + 3 = 2`") becomes the window rule "first time `Re w ≤ 2`", and then

* the *previous* iterate has `Re > 2`, so the landing point has `Re > 2 - 33/32 = 31/32 > 0`;
* the step count satisfies `N ≤ 32 (z.re - 2)/31 + 1`.

Everything else is the induction of `walk_right_deep` verbatim: `walkStep` is the chosen
backward step of `hbwd`, `W n = (walkStep hbwd)^[n] z`, and the margin `margA_g` loses at most
`17/16` per step (`margA_step_le`) while the walk needs at most `32 (z.re - 2)/31 + 1` steps, so
it is legal below the depth threshold `walkY2 Ξ (-1) α` (`margA_deep_bound`, which for `x₀ = -1`
is exactly the inequality needed here).
-/

noncomputable section

open Complex Metric Set

theorem walk_window_right {Ξ : ℝ} {α : ℂ} {F Φ : ℂ → ℂ}
    (hbwd : ∀ z ∈ Work.Pert.Qm Ξ α, 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α z →
      ∃ w : ℂ, ‖w - (z - 1)‖ ≤ 1 / 32 ∧ F w = z ∧ w ∈ Work.Pert.Qm Ξ α ∧
        Φ w = Φ z - 1) :
    ∃ Y₂ : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, z.im ≤ -Y₂ → 2 ≤ z.re →
      ∃ (N : ℕ) (w : ℕ → ℂ), w 0 = z ∧ w N ∈ Work.Pert.Qm Ξ α ∧
        (w N).re ∈ Set.Icc 0 2 ∧ Φ (w N) = Φ z - (N : ℂ) ∧
        (∀ n < N, w (n + 1) ∈ Work.Pert.Qm Ξ α ∧ F (w (n + 1)) = w n ∧
          Φ (w (n + 1)) = Φ (w n) - 1 ∧ ‖w (n + 1) - (w n - 1)‖ ≤ 1 / 32) ∧
        (∀ n ≤ N, (w n).im ≤ z.im + (n : ℝ) / 32) ∧
        (N : ℝ) ≤ 32 * (z.re - 2) / 31 + 1 := by
  classical
  refine ⟨walkY2 Ξ (-1) α, ?_⟩
  intro z hz hzim hzre
  -- the walk
  let W : ℕ → ℂ := fun n => (walkStep hbwd)^[n] z
  have hW0 : W 0 = z := by simp only [W, Function.iterate_zero, id_eq]
  have hWsucc : ∀ n : ℕ, W (n + 1) = walkStep hbwd (W n) := by
    intro n
    simp only [W, Function.iterate_succ_apply']
  -- the step count: we stop at the first `Re ≤ 2`, and `2 = x₀ + 3` with `x₀ = -1`
  set t : ℝ := 32 * (z.re - 2) / 31 with ht
  have ht_nonneg : 0 ≤ t := by rw [ht]; linarith only [hzre]
  set N₀ : ℕ := Nat.floor t + 1 with hN₀
  have hN₀sub : ((N₀ - 1 : ℕ) : ℝ) ≤ t := by
    rw [hN₀]
    rw [Nat.add_sub_cancel]
    exact Nat.floor_le ht_nonneg
  have hN₀ge : t ≤ (N₀ : ℝ) := by
    rw [hN₀]
    have h1 : t < ((Nat.floor t : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
    push_cast
    linarith only [h1]
  -- the depth bound: `margA_deep_bound` at `x₀ = -1` is exactly `5/4 + (17/16) t ≤ margA_g`
  have hdeep : 5 / 4 + (17 / 16) * t ≤ Work.Pert.margA_g Ξ α z := by
    have h := margA_deep_bound (Ξ := Ξ) (x₀ := -1) (α := α) hz hzim
      (by linarith only [hzre] : (-1 : ℝ) + 3 ≤ z.re)
    have he : (32 * (z.re - (-1) - 3) / 31 : ℝ) = t := by rw [ht]; ring
    rwa [he] at h
  -- the induction
  have key : ∀ n : ℕ, n ≤ N₀ →
      (W n ∈ Work.Pert.Qm Ξ α ∧ Φ (W n) = Φ z - (n : ℂ) ∧
       (W n).re ≤ z.re - (31 / 32) * (n : ℝ) ∧
       |(W n).im - z.im| ≤ (1 / 32) * (n : ℝ) ∧
       Work.Pert.margA_g Ξ α z - (17 / 16) * (n : ℝ) ≤ Work.Pert.margA_g Ξ α (W n) ∧
       (n < N₀ → 5 / 4 ≤ Work.Pert.margA_g Ξ α (W n))) := by
    intro n hn
    induction n with
    | zero =>
      refine ⟨by rw [hW0]; exact hz, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hW0]; norm_num
      · rw [hW0]; norm_num
      · rw [hW0]; norm_num
      · rw [hW0]; norm_num
      · intro _
        rw [hW0]
        have h17 : 0 ≤ (17 / 16 : ℝ) * t :=
          mul_nonneg (by norm_num) ht_nonneg
        linarith only [hdeep, h17]
    | succ m ih =>
      have hmle : m ≤ N₀ := by omega
      have hmlt : m < N₀ := by omega
      obtain ⟨hmem, hmphi, hmreub, hmimb, hmmarg, hm5⟩ := ih hmle
      have hmargin5 : 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α (W m) := by
        have h := hm5 hmlt
        linarith only [h]
      obtain ⟨hdw, hFw, hwQ, hΦw⟩ := walkStep_spec hbwd hmem hmargin5
      have hWs : W (m + 1) = walkStep hbwd (W m) := hWsucc m
      have hm1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hWs]; exact hwQ
      · rw [hWs, hΦw, hmphi]
        push_cast
        ring
      · rw [hWs, hm1]
        have hb := (walk_step_bounds hdw).2.1
        linarith only [hb, hmreub]
      · rw [hWs, hm1]
        have hb := (walk_step_bounds hdw).2.2
        have hsum : (walkStep hbwd (W m)).im - z.im
            = ((walkStep hbwd (W m)).im - (W m).im) + ((W m).im - z.im) := by ring
        rw [hsum]
        calc |((walkStep hbwd (W m)).im - (W m).im) + ((W m).im - z.im)|
            ≤ |(walkStep hbwd (W m)).im - (W m).im| + |(W m).im - z.im| := abs_add_le _ _
          _ ≤ 1 / 32 + (1 / 32) * (m : ℝ) := by linarith only [hb, hmimb]
          _ = (1 / 32) * ((m : ℝ) + 1) := by ring
      · rw [hWs, hm1]
        have hb := margA_step_le (Ξ := Ξ) (α := α) hdw
        linarith only [hb, hmmarg]
      · intro hlt
        rw [hWs]
        have hb := margA_step_le (Ξ := Ξ) (α := α) hdw
        have hle : (m : ℝ) + 1 ≤ t := by
          have h1 : m + 1 ≤ N₀ - 1 := by omega
          have h2 : ((m + 1 : ℕ) : ℝ) ≤ ((N₀ - 1 : ℕ) : ℝ) := by exact_mod_cast h1
          linarith only [h2, hm1, hN₀sub]
        linarith only [hb, hmmarg, hdeep, hle]
  have hN₀re : (W N₀).re ≤ 2 := by
    have hreub := (key N₀ le_rfl).2.2.1
    have h31 : z.re - (31 / 32) * (N₀ : ℝ) ≤ 2 := by
      have hmul : (31 / 32) * t ≤ (31 / 32) * (N₀ : ℝ) :=
        mul_le_mul_of_nonneg_left hN₀ge (by norm_num)
      have htval : (31 / 32) * t = z.re - 2 := by rw [ht]; ring
      linarith only [hmul, htval]
    linarith only [hreub, h31]
  have hex : ∃ n : ℕ, (W n).re ≤ 2 := ⟨N₀, hN₀re⟩
  set N : ℕ := Nat.find hex with hN
  have hNspec : (W N).re ≤ 2 := by rw [hN]; exact Nat.find_spec hex
  have hNle : N ≤ N₀ := by rw [hN]; exact Nat.find_min' hex hN₀re
  obtain ⟨hWNQm, hWphi, hWreub, hWimb, hWmarg, hW5⟩ := key N hNle
  refine ⟨N, W, hW0, hWNQm, ?_, hWphi, ?_, ?_, ?_⟩
  · -- the landing point lies in the window `[0,2]`
    refine ⟨?_, hNspec⟩
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0, hW0]
      linarith only [hzre]
    · have hN_eq : (N - 1) + 1 = N := by omega
      have hmN : N - 1 < N := by omega
      have hnotle : ¬ (W (N - 1)).re ≤ 2 := by
        rw [hN]; exact Nat.find_min hex hmN
      have hlt : 2 < (W (N - 1)).re := not_le.mp hnotle
      have hmle : N - 1 < N₀ := by omega
      obtain ⟨hmQm, -, -, -, -, hm5⟩ := key (N - 1) (le_of_lt hmle)
      have hmargin5 : 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α (W (N - 1)) := by
        have h := hm5 (by omega)
        linarith only [h]
      obtain ⟨hdw, -, -, -⟩ := walkStep_spec hbwd hmQm hmargin5
      have hWN : W N = walkStep hbwd (W (N - 1)) := by
        have h := hWsucc (N - 1)
        rwa [hN_eq] at h
      have hrelb : (W (N - 1)).re - 33 / 32 ≤ (W N).re := by
        rw [hWN]; exact (walk_step_bounds hdw).1
      linarith only [hrelb, hlt]
  · -- the one-step clause
    intro n hn
    have hnN₀ : n < N₀ := lt_of_lt_of_le hn hNle
    obtain ⟨hmQm, -, -, -, -, hm5⟩ := key n (le_of_lt hnN₀)
    have hmargin5 : 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α (W n) := by
      have h := hm5 hnN₀
      linarith only [h]
    obtain ⟨hdw, hFw, hwQ, hΦw⟩ := walkStep_spec hbwd hmQm hmargin5
    have hWs : W (n + 1) = walkStep hbwd (W n) := hWsucc n
    exact ⟨by rw [hWs]; exact hwQ, by rw [hWs]; exact hFw, by rw [hWs]; exact hΦw,
      by rw [hWs]; exact hdw⟩
  · -- the imaginary part never rises faster than `1/32` per step
    intro n hn
    have h := (abs_le.mp ((key n (le_trans hn hNle)).2.2.2.1)).2
    have he : (n : ℝ) / 32 = (1 / 32) * (n : ℝ) := by ring
    rw [he]
    linarith only [h]
  · -- the step budget
    have h1 : (N : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hNle
    have h2 : (N₀ : ℝ) ≤ t + 1 := by
      rw [hN₀]
      have h := Nat.floor_le ht_nonneg
      push_cast
      linarith only [h]
    have h3 : t = 32 * (z.re - 2) / 31 := ht
    linarith only [h1, h2, h3]

end

end Work.Pert.pert2v2
