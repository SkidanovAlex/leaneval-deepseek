import Mathlib
import Submission.Work.Pert.pert2v2.walk_right_deep
import Submission.Work.Pert.pert2v2.walk_window_right
import Submission.Work.Pert.pert2v2.drift_sum_le

namespace Work.Pert.pert2v2

open Complex Metric Set Filter
open scoped Topology

noncomputable section

/-!
# `Work.Pert.pert2v2.walk_right_drift`: the drift of the rightward walk

Given the backward-step hypothesis `hbwd` (a preimage of `z` one unit to the left, with `Φ` falling
by `1`) and the depth hypothesis `hdec` (`F` is a `1/32`-near-translation by `ρ` deep below), every
point `z` of the lower gate which is deep below and far to the right admits a backward walk
landing in the window `{0 ≤ Re ≤ 2}`, with the *drift* form

`‖(Φ w - w/ρ) - (Φ z - z/ρ)‖ ≤ 1`.

The point is that the two error sources cancel: each step moves `z` by about `1` (the `hbwd` bound)
while `hdec` moves it by about `ρ`, so the drift accumulated in one step is exactly the *error*
`F w - (w + ρ)` of the near-translation, which decays exponentially with the depth.  Summing over
the (at most `32 z.re/31 + 1`) steps and choosing the depth threshold `Y₂` large enough so that
"polynomial times exponential" beats `‖ρ‖/M` gives the claim.

The pieces are
* `exists_mul_exp_neg_le` — the elementary "exponential beats linear" fact;
* `walk_window_right` — the walk itself (threshold `2`, as in `walk_right_deep` with `x₀ = -1`);
* `drift_sum_le` — the telescoping of the per-step error into the drift sum.
-/

/-- **Exponential beats linear.**  For `0 < c`, `0 < ε` there is a threshold beyond which
`(a u + b) exp (-(c u)) ≤ ε`. -/
theorem exists_mul_exp_neg_le {a b c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∃ T : ℝ, ∀ u : ℝ, T ≤ u → (a * u + b) * Real.exp (-(c * u)) ≤ ε := by
  have hcomp : Filter.Tendsto (fun u : ℝ => (c * u) * Real.exp (-(c * u))) Filter.atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hc)
    exact h.congr' (Filter.Eventually.of_forall (fun u => by simp [Function.comp_apply]))
  have hexp : Filter.Tendsto (fun u : ℝ => Real.exp (-(c * u))) Filter.atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
  have hlin : Filter.Tendsto (fun u : ℝ =>
      (a / c) * ((c * u) * Real.exp (-(c * u))) + b * Real.exp (-(c * u)))
      Filter.atTop (𝓝 ((a / c) * 0 + b * 0)) :=
    (hcomp.const_mul (a / c)).add (hexp.const_mul b)
  simp only [mul_zero, zero_add] at hlin
  have h3 : Filter.Tendsto (fun u : ℝ => (a * u + b) * Real.exp (-(c * u)))
      Filter.atTop (𝓝 0) :=
    hlin.congr' (Filter.Eventually.of_forall (fun u => by field_simp))
  have h4 := (tendsto_order.1 h3).2 ε hε
  rw [eventually_atTop] at h4
  obtain ⟨T, hT⟩ := h4
  exact ⟨T, fun u hu => le_of_lt (hT u hu)⟩

theorem walk_right_drift {Ξ : ℝ} {α ρ : ℂ} {M κ Y : ℝ} {F Φ : ℂ → ℂ}
    (hM : 0 < M) (hκ : 0 < κ) (hρ : ‖ρ - 1‖ ≤ 1 / 32)
    (hbwd : ∀ z ∈ Work.Pert.Qm Ξ α, 1 + 1 / 4 ≤ Work.Pert.margA_g Ξ α z →
      ∃ w : ℂ, ‖w - (z - 1)‖ ≤ 1 / 32 ∧ F w = z ∧ w ∈ Work.Pert.Qm Ξ α ∧ Φ w = Φ z - 1)
    (hdec : ∀ w ∈ Work.Pert.Qm Ξ α, w.im < -Y →
      ‖F w - (w + ρ)‖ ≤ M * Real.exp (κ * w.im)) :
    ∃ Y₂ : ℝ, ∀ z ∈ Work.Pert.Qm Ξ α, z.im ≤ -Y₂ → 2 ≤ z.re →
      ∃ w : ℂ, w ∈ Work.Pert.Qm Ξ α ∧ w.re ∈ Set.Icc 0 2 ∧
        ‖(Φ w - w / ρ) - (Φ z - z / ρ)‖ ≤ 1 ∧ w.im ≤ z.im + |z.re| / 2 + 2 := by
  -- `ρ` is invertible: `‖ρ‖ ≥ 31/32`
  have hρnorm : (31 : ℝ) / 32 ≤ ‖ρ‖ := by
    have h1 : |‖ρ‖ - ‖(1 : ℂ)‖| ≤ ‖ρ - 1‖ := abs_norm_sub_norm_le ρ 1
    rw [norm_one] at h1
    have h2 : |‖ρ‖ - 1| ≤ 1 / 32 := le_trans h1 hρ
    have h3 := (abs_le.mp h2).1
    linarith only [h3]
  have hρpos : 0 < ‖ρ‖ := by linarith only [hρnorm]
  set C₀ : ℝ := |Ξ| / 31 + 1 / 32 with hC₀
  -- the walk
  obtain ⟨Yw, hwalk⟩ := walk_window_right (Ξ := Ξ) (α := α) hbwd
  set B : ℝ := (31 / 30) * (Y + C₀) + 1 with hB
  -- the threshold beyond which the accumulated error is `< ‖ρ‖/M`
  obtain ⟨T, hT⟩ := exists_mul_exp_neg_le (a := 32 / 31) (b := 32 * |Ξ| / 31 + 1)
    (c := 30 * κ / 31) (ε := ‖ρ‖ / (M * Real.exp (κ * C₀)))
    (by positivity) (by positivity)
  refine ⟨max (max (max Yw B) T) 1, ?_⟩
  have hYwle : Yw ≤ max (max (max Yw B) T) 1 :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hBle : B ≤ max (max (max Yw B) T) 1 :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hTle : T ≤ max (max (max Yw B) T) 1 :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hY2one : (1 : ℝ) ≤ max (max (max Yw B) T) 1 := le_max_right _ _
  intro z hz hzim hzre
  have hY2pos : 0 < max (max (max Yw B) T) 1 := lt_of_lt_of_le one_pos hY2one
  have hzim_neg : z.im < 0 := lt_of_le_of_lt hzim (neg_lt_zero.mpr hY2pos)
  have hzabs : |z.im| = -z.im := abs_of_neg hzim_neg
  -- the gate gives `Re z < |Im z| - Ξ`, so `z.re` is controlled by the depth
  have hzre_disj : z.re < -z.im - Ξ := by
    have hB' : 0 < Work.Pert.margB_g Ξ z := ((Work.Pert.mem_Qm_iff_g z).mp hz).2
    rw [Work.Pert.margB_g, hzabs] at hB'
    linarith only [hB']
  obtain ⟨N, w, hw0, hwNQm, hwre, _hwphi, hstep, himb, hNbound⟩ :=
    hwalk z hz (le_trans hzim (neg_le_neg hYwle)) hzre
  -- the imaginary part of every walk point, in terms of `z` alone
  have hpt : ∀ n : ℕ, n < N → (w (n + 1)).im ≤ (30 / 31) * z.im + C₀ := by
    intro n hn
    have h1 : (w (n + 1)).im ≤ z.im + ((n + 1 : ℕ) : ℝ) / 32 := himb (n + 1) (by omega)
    have h2 : ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have : n + 1 ≤ N := by omega
      exact_mod_cast this
    have h3 : (N : ℝ) / 32 ≤ (z.re - 2) / 31 + 1 / 32 := by linarith only [hNbound]
    have h4 : (z.re - 2) / 31 ≤ (-z.im + |Ξ|) / 31 := by
      have h5 : -Ξ ≤ |Ξ| := neg_le_abs Ξ
      linarith only [hzre_disj, h5]
    have h6 : (w (n + 1)).im ≤ z.im + ((z.re - 2) / 31 + 1 / 32) := by
      have h7 : ((n + 1 : ℕ) : ℝ) / 32 ≤ (N : ℝ) / 32 := by linarith only [h2]
      linarith only [h1, h7, h3]
    have h8 : z.im + ((z.re - 2) / 31 + 1 / 32) ≤ (30 / 31) * z.im + C₀ := by
      rw [hC₀]; linarith only [h4]
    linarith only [h6, h8]
  -- the walk points are deeper than `-Y`
  have hheight : ∀ n : ℕ, n < N → (w (n + 1)).im < -Y := by
    intro n hn
    have h1 := hpt n hn
    have h2 : (30 / 31) * z.im ≤ (30 / 31) * (-B) := by
      have h3 : z.im ≤ -B := le_trans hzim (neg_le_neg hBle)
      exact mul_le_mul_of_nonneg_left h3 (by norm_num)
    have h4 : (30 / 31) * (-B) + C₀ = -Y - 30 / 31 := by rw [hB]; ring
    linarith only [h1, h2, h4]
  -- the per-step errors sum to at most `‖ρ‖/M`
  have hsum : (∑ n ∈ Finset.range N, Real.exp (κ * (w (n + 1)).im)) ≤ ‖ρ‖ / M := by
    have hper : ∀ n ∈ Finset.range N, Real.exp (κ * (w (n + 1)).im)
        ≤ Real.exp (κ * ((30 / 31) * z.im + C₀)) := by
      intro n hn
      rw [Finset.mem_range] at hn
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hpt n hn) (le_of_lt hκ))
    have hsumle := Finset.sum_le_sum hper
    have hcard : (∑ _n ∈ Finset.range N, Real.exp (κ * ((30 / 31) * z.im + C₀)))
        = (N : ℝ) * Real.exp (κ * ((30 / 31) * z.im + C₀)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hcard] at hsumle
    -- the exponential in terms of the depth
    have hEeq : Real.exp (κ * ((30 / 31) * z.im + C₀))
        = Real.exp (κ * C₀) * Real.exp (-((30 * κ / 31) * (-z.im))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    -- the number of steps in terms of the depth
    have hNb : (N : ℝ) ≤ (32 / 31) * (-z.im) + (32 * |Ξ| / 31 + 1) := by
      have h5 : -Ξ ≤ |Ξ| := neg_le_abs Ξ
      have h6 : 32 * (z.re - 2) / 31 < (32 / 31) * (-z.im) + 32 * |Ξ| / 31 := by
        linarith only [hzre_disj, h5]
      linarith only [hNbound, h6]
    have hstep1 : (N : ℝ) * Real.exp (κ * ((30 / 31) * z.im + C₀))
        ≤ ((32 / 31) * (-z.im) + (32 * |Ξ| / 31 + 1))
          * Real.exp (κ * ((30 / 31) * z.im + C₀)) :=
      mul_le_mul_of_nonneg_right hNb (Real.exp_pos _).le
    have hstep2 : ((32 / 31) * (-z.im) + (32 * |Ξ| / 31 + 1))
          * Real.exp (κ * ((30 / 31) * z.im + C₀))
        = Real.exp (κ * C₀)
          * (((32 / 31) * (-z.im) + (32 * |Ξ| / 31 + 1))
            * Real.exp (-((30 * κ / 31) * (-z.im)))) := by
      rw [hEeq]; ring
    have hTleu : T ≤ -z.im := le_trans hTle (by linarith only [hzim])
    have hdecay := hT (-z.im) hTleu
    have hfin : Real.exp (κ * C₀)
          * (((32 / 31) * (-z.im) + (32 * |Ξ| / 31 + 1))
            * Real.exp (-((30 * κ / 31) * (-z.im)))) ≤ ‖ρ‖ / M := by
      have h1 := mul_le_mul_of_nonneg_left hdecay (Real.exp_pos (κ * C₀)).le
      have h2 : Real.exp (κ * C₀) * (‖ρ‖ / (M * Real.exp (κ * C₀))) = ‖ρ‖ / M := by
        field_simp
      linarith only [h1, h2]
    linarith only [hsumle, hstep1, hstep2, hfin]
  -- the telescoped drift
  have hdrift := drift_sum_le (Ξ := Ξ) (α := α) (ρ := ρ) (M := M) (κ := κ) (Y := Y)
    (F := F) (Φ := Φ) (w := w) (N := N) (le_of_lt hM) hρ hdec hstep hheight
  rw [hw0] at hdrift
  have hmain : ‖(Φ (w N) - w N / ρ) - (Φ z - z / ρ)‖ ≤ 1 := by
    have h1 : M / ‖ρ‖ * (∑ n ∈ Finset.range N, Real.exp (κ * (w (n + 1)).im))
        ≤ M / ‖ρ‖ * (‖ρ‖ / M) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h2 : M / ‖ρ‖ * (‖ρ‖ / M) = 1 := by field_simp
    linarith only [hdrift, h1, h2]
  refine ⟨w N, hwNQm, hwre, hmain, ?_⟩
  -- the height of the landing point
  have himN : (w N).im ≤ z.im + (N : ℝ) / 32 := himb N le_rfl
  have hN32 : (N : ℝ) / 32 ≤ (z.re - 2) / 31 + 1 / 32 := by linarith only [hNbound]
  have hzabsre : |z.re| = z.re := abs_of_nonneg (by linarith only [hzre])
  have hfin2 : (N : ℝ) / 32 ≤ z.re / 2 + 2 := by
    have h5 : (z.re - 2) / 31 ≤ z.re / 2 := by linarith only [hzre]
    linarith only [hN32, h5]
  rw [hzabsre]
  linarith only [himN, hfin2]

end

end Work.Pert.pert2v2
