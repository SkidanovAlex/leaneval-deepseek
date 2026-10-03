import Mathlib
import Submission.Work.Pert.pert2v2.steps
import Submission.Work.Pert.pert2v2.walkY2
import Submission.Work.Pert.pert2v2.walk_step_bounds
import Submission.Work.Pert.pert2v2.margA_step_le
import Submission.Work.Pert.pert2v2.margA_deep_bound

namespace Work.Pert.pert2v2

open Complex Metric Set

noncomputable section

/-!
# `Work.Pert.pert2v2.walk_right_deep`: the backward walk reaches `x₀`

Given the backward step hypothesis

`hbwd : z ∈ Qm Ξ α → 1 + 1/4 ≤ margA_g Ξ α z → ∃ w, ‖w - (z-1)‖ ≤ 1/32 ∧ F w = z ∧
  w ∈ Qm Ξ α ∧ Φ w = Φ z - 1`

we walk backwards from any point `z` of the lower gate which is deep below (`z.im ≤ -Y₂`) and far
to the right (`x₀ + 3 ≤ z.re`), stopping at the first time the real part drops below `x₀ + 3`.  The
number of steps is `≈ 32(z.re - x₀ - 3)/31`, and

* each step loses at most `17/16` of the left margin (`margA_step_le`), so the walk is legal as long
  as the initial margin dominates `5/4 + (17/16)·32(z.re - x₀ - 3)/31` — which is exactly
  `margA_deep_bound`, the reason for the explicit threshold `walkY2`;
* each step moves the real part down by between `31/32` and `33/32` and the imaginary part by at
  most `1/32` (`walk_step_bounds`), which gives both `|w.re - x₀| ≤ 3` at the stopping time and the
  imaginary-part bound `w.im ≤ z.im + (z.re - x₀)/2 + 1`.

The hypotheses `hM`, `hκ`, `hρ` and `hdec` (the decay of `F - id - ρ` at depth) are not needed for
this purely combinatorial walk; they belong to the caller's interface.
-/

/-- The (partial) backward step map: the chosen `w` of `hbwd` when the hypotheses hold, and `0`
off the domain (a junk value which is never used). -/
def walkStep {Ξ : ℝ} {α : ℂ} {F Φ : ℂ → ℂ}
    (hbwd : ∀ z ∈ Work.Pert.Qm Ξ α, 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α z →
      ∃ w : ℂ, ‖w - (z - 1)‖ ≤ 1 / 32 ∧ F w = z ∧ w ∈ Work.Pert.Qm Ξ α ∧ Φ w = Φ z - 1)
    (p : ℂ) : ℂ := by
  classical
  exact if h : p ∈ Work.Pert.Qm Ξ α ∧ 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α p
    then (hbwd p h.1 h.2).choose else 0

/-- The specification of a single backward step. -/
lemma walkStep_spec {Ξ : ℝ} {α : ℂ} {F Φ : ℂ → ℂ}
    (hbwd : ∀ z ∈ Work.Pert.Qm Ξ α, 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α z →
      ∃ w : ℂ, ‖w - (z - 1)‖ ≤ 1 / 32 ∧ F w = z ∧ w ∈ Work.Pert.Qm Ξ α ∧ Φ w = Φ z - 1)
    {p : ℂ} (hp : p ∈ Work.Pert.Qm Ξ α) (hp2 : 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α p) :
    ‖walkStep hbwd p - (p - 1)‖ ≤ 1 / 32 ∧ F (walkStep hbwd p) = p ∧
      walkStep hbwd p ∈ Work.Pert.Qm Ξ α ∧ Φ (walkStep hbwd p) = Φ p - 1 := by
  have h : p ∈ Work.Pert.Qm Ξ α ∧ 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α p := ⟨hp, hp2⟩
  have hstep : walkStep hbwd p = (hbwd p hp hp2).choose := by
    simp only [walkStep]
    rw [dif_pos h]
  obtain ⟨h1, h2, h3, h4⟩ := (hbwd p hp hp2).choose_spec
  exact ⟨by rw [hstep]; exact h1, by rw [hstep]; exact h2,
    by rw [hstep]; exact h3, by rw [hstep]; exact h4⟩

theorem walk_right_deep {Ξ : ℝ} {α ρ : ℂ} {M κ Y : ℝ} {F Φ : ℂ → ℂ} {x₀ : ℝ}
    (hM : 0 < M) (hκ : 0 < κ) (hρ : ‖ρ - 1‖ ≤ 1 / 32)
    (hbwd : ∀ z ∈ Work.Pert.Qm Ξ α, 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α z →
      ∃ w : ℂ, ‖w - (z - 1)‖ ≤ 1 / 32 ∧ F w = z ∧ w ∈ Work.Pert.Qm Ξ α ∧ Φ w = Φ z - 1)
    (hdec : ∀ w ∈ Work.Pert.Qm Ξ α, w.im < -Y →
      ‖F w - (w + ρ)‖ ≤ M * Real.exp (κ * w.im)) :
    ∃ Y₂ : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, z.im ≤ -Y₂ → x₀ + 3 ≤ z.re →
      ∃ (k : ℕ) (w : ℂ), w ∈ Work.Pert.Qm Ξ α ∧ Φ w = Φ z - k ∧
        |w.re - x₀| ≤ 3 ∧ w.im ≤ z.im + (z.re - x₀) / 2 + 1 := by
  classical
  refine ⟨walkY2 Ξ x₀ α, ?_⟩
  intro z hz hzim hzre
  have hY2pos : 0 < walkY2 Ξ x₀ α := walkY2_pos Ξ x₀ α
  have hzim_neg : z.im < 0 := lt_of_le_of_lt hzim (neg_lt_zero.mpr hY2pos)
  have hzabs : |z.im| = -z.im := abs_of_neg hzim_neg
  obtain ⟨hzA, hzB⟩ := (Work.Pert.mem_Qm_iff_g (Ξ := Ξ) (α := α) z).mp hz
  have hzre_lt : z.re < -z.im - Ξ := by
    have h := hzB
    simp only [Work.Pert.margB_g] at h
    rw [hzabs] at h
    linarith only [h]
  -- the walk
  let W : ℕ → ℂ := fun n => (walkStep hbwd)^[n] z
  have hW0 : W 0 = z := by simp only [W, Function.iterate_zero, id_eq]
  have hWsucc : ∀ n : ℕ, W (n + 1) = walkStep hbwd (W n) := by
    intro n
    simp only [W, Function.iterate_succ_apply']
  -- the step count
  set t : ℝ := 32 * (z.re - x₀ - 3) / 31 with ht
  have ht_nonneg : 0 ≤ t := by
    rw [ht]
    have h : 0 ≤ z.re - x₀ - 3 := by linarith only [hzre]
    positivity
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
  have hdeep := margA_deep_bound hz hzim hzre
  rw [← ht] at hdeep
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
  have hN₀re : (W N₀).re ≤ x₀ + 3 := by
    have hreub := (key N₀ le_rfl).2.2.1
    have h31 : z.re - (31 / 32) * (N₀ : ℝ) ≤ x₀ + 3 := by
      have hmul : (31 / 32) * t ≤ (31 / 32) * (N₀ : ℝ) :=
        mul_le_mul_of_nonneg_left hN₀ge (by norm_num)
      have htval : (31 / 32) * t = z.re - x₀ - 3 := by
        rw [ht]; ring
      linarith only [hmul, htval]
    linarith only [hreub, h31]
  have hex : ∃ n : ℕ, (W n).re ≤ x₀ + 3 := ⟨N₀, hN₀re⟩
  set N : ℕ := Nat.find hex with hN
  have hNspec : (W N).re ≤ x₀ + 3 := by rw [hN]; exact Nat.find_spec hex
  have hNle : N ≤ N₀ := by rw [hN]; exact Nat.find_min' hex hN₀re
  obtain ⟨hWNQm, hWphi, hWreub, hWimb, hWmarg, hW5⟩ := key N hNle
  refine ⟨N, W N, hWNQm, hWphi, ?_, ?_⟩
  · -- the stopping time lands within `3` of `x₀`
    have hub : (W N).re ≤ x₀ + 3 := hNspec
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]
      have hzle : z.re ≤ x₀ + 3 := by
        have h := hNspec
        rw [h0, hW0] at h
        exact h
      rw [hW0, abs_le]
      constructor <;> linarith only [hzre, hzle]
    · have hN_eq : (N - 1) + 1 = N := by omega
      have hmN : N - 1 < N := by omega
      have hnotle : ¬ (W (N - 1)).re ≤ x₀ + 3 := by
        rw [hN]; exact Nat.find_min hex hmN
      have hlt : x₀ + 3 < (W (N - 1)).re := not_le.mp hnotle
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
      rw [abs_le]
      constructor <;> linarith only [hrelb, hlt, hub]
  · -- the imaginary part
    have him := hWimb
    have him' : (W N).im ≤ z.im + (1 / 32) * (N : ℝ) := by
      have h := (abs_le.mp him).2
      linarith only [h]
    have hNle' : (N : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hNle
    have hN₀le : (N₀ : ℝ) ≤ t + 1 := by
      rw [hN₀]
      have h := Nat.floor_le ht_nonneg
      push_cast
      linarith only [h]
    have hfin : (1 / 32) * (N : ℝ) ≤ (z.re - x₀) / 2 + 1 := by
      have h1 : (1 / 32) * (N : ℝ) ≤ (1 / 32) * (t + 1) :=
        mul_le_mul_of_nonneg_left (le_trans hNle' hN₀le) (by norm_num)
      have h2 : (1 / 32) * (t + 1) ≤ (z.re - x₀) / 2 + 1 := by
        rw [ht]
        nlinarith only [hzre]
      linarith only [h1, h2]
    linarith only [him', hfin]

end

end Work.Pert.pert2v2
