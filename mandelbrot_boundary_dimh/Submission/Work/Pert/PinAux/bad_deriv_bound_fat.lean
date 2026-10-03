import Mathlib
import Submission.Work.Pert.PinAux.CollarDefs
import Submission.Work.FatouL1.deriv_le_deriv_mul_of_injOn_ball

/-!
# `Work.Pert.PinAux.bad_deriv_bound_fat`

Uniform bound for the derivative of a Fatou coordinate of a near-translation on the gate
`Qm Ξ α`, on the part of the gate where `w` carries a positive margin `ρ ≤ minmarg Ξ α w` and the
slice at the height of `w` is *fat*, `√2 Rde ≤ minmarg Ξ α (med Ξ α w.im)`.

The proof uses two ingredients and none of the fine structure of the Fatou flow.

* **Compactness.**  On the set of points of the gate with `|Im z| ≤ |Im (1/α)|` and
  `ρ ≤ minmarg z` the derivative `Φ'` is bounded: that set is closed, bounded, and lies in the
  open gate, where `Φ'` is continuous.

* **Vertical iteration.**  For `|Im w| > |Im (1/α)|` write `x = Re w`, `t = Im w`, `m = minmarg w`
  and let `σ = ±1` be the sign of `t`; then `σ t ≥ |Im (1/α)|`, and for every real `s` with
  `σ s ≥ |Im (1/α)|` moving to the height `s + σ δ` (i.e. *vertically away from both `0` and
  `−(1/α).im`*) raises both margins by exactly `δ ≥ 0` (`minmarg_vert_step`).  Iterating the
  vertical move by `δ_j = m (3/2)^j / 2` produces points `ζ_j` with `minmarg ζ_j = m (3/2)^j`,
  and each step costs only the two-sided Koebe distortion factor `K` — the ratio
  `|ζ_j − ζ_{j+1}| / (minmarg ζ_{j+1}/√2)` is `√2/3 < 1/2`.  After `N` steps,
  `minmarg ζ_N ≥ ρ (3/2)^N ≥ √2 Rde`, so that the whole-gate derivative estimate `hDEest`
  (Shishikura A.2.4(i)) applies at `ζ_N`.

Since `(3/2)^N ≥ √2 Rde / ρ` for `N = ⌈2 √2 Rde / ρ⌉` (Bernoulli), the result follows.  The fat
hypothesis is not needed for this argument; it is part of the interface the caller uses.
-/

namespace Work.Pert.PinAux

open MandelDim Complex Metric Filter

noncomputable section

set_option maxHeartbeats 800000

/-! ### The margins on a vertical line -/

lemma margA_vert (Ξ : ℝ) (α : ℂ) (x s : ℝ) :
    margA Ξ α ((x : ℂ) + s * Complex.I) = x - Ξ + (1 / α).re + |s + (1 / α).im| :=
  Work.Pert.margA_eval Ξ α x s

lemma margB_vert (Ξ : ℝ) (α : ℂ) (x s : ℝ) :
    margB Ξ α ((x : ℂ) + s * Complex.I) = |s| - Ξ - x :=
  Work.Pert.margB_eval Ξ α x s

lemma abs_eq_one_of_eq_one_or_eq_neg_one {σ : ℝ} (h : σ = 1 ∨ σ = -1) : |σ| = 1 := by
  rcases h with h | h <;> rw [h] <;> norm_num

/-- If `σ = ±1` and `0 ≤ σ s` then `|s| = σ s`. -/
lemma abs_eq_mul_of_eq_one_or_neg_one {σ s : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : 0 ≤ σ * s) :
    |s| = σ * s := by
  rcases hσ with h' | h'
  · rw [h'] at h ⊢
    simp only [one_mul] at h ⊢
    rw [abs_of_nonneg h]
  · rw [h'] at h ⊢
    simp only [neg_one_mul] at h ⊢
    rw [abs_of_nonpos (by linarith : s ≤ 0)]

/-- If `σ = ±1`, `0 ≤ σ s` and `0 ≤ δ` then `|s + σ δ| = σ s + δ`. -/
lemma abs_add_mul_eq {σ s δ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : 0 ≤ σ * s) (hδ : 0 ≤ δ) :
    |s + σ * δ| = σ * s + δ := by
  have hσsq : σ * σ = 1 := by rcases hσ with h' | h' <;> rw [h'] <;> norm_num
  have hnn : 0 ≤ σ * s + δ := by linarith
  have h' : s + σ * δ = σ * (σ * s + δ) := by
    rw [mul_add, ← mul_assoc, hσsq, one_mul]
    try ring
  rw [h', abs_mul, abs_eq_one_of_eq_one_or_eq_neg_one hσ, one_mul, abs_of_nonneg hnn]

/-- Moving vertically from the height `s` to the height `h = s + σ δ` (vertically away from both
`0` and `-(1/α).im`) raises *both* margins by exactly `δ`. -/
lemma minmarg_vert_step {Ξ : ℝ} {α : ℂ} {x s h σ δ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hσs : |(1 / α).im| ≤ σ * s) (hδ : 0 ≤ δ) (hh : h = s + σ * δ) :
    minmarg Ξ α ((x : ℂ) + h * Complex.I)
      = minmarg Ξ α ((x : ℂ) + s * Complex.I) + δ := by
  have h0 : 0 ≤ σ * s := le_trans (abs_nonneg _) hσs
  have h1 : 0 ≤ σ * (s + (1 / α).im) := by
    have h2 : |σ * (1 / α).im| = |(1 / α).im| := by
      rw [abs_mul, abs_eq_one_of_eq_one_or_eq_neg_one hσ, one_mul]
    have h3 := neg_abs_le (σ * (1 / α).im)
    rw [h2] at h3
    have h4 : σ * (s + (1 / α).im) = σ * s + σ * (1 / α).im := by ring
    rw [h4]
    linarith
  have hA' : |h + (1 / α).im| = |s + (1 / α).im| + δ := by
    have heq : h + (1 / α).im = (s + (1 / α).im) + σ * δ := by rw [hh]; ring
    rw [heq, abs_add_mul_eq hσ h1 hδ, ← abs_eq_mul_of_eq_one_or_neg_one hσ h1]
  have hB' : |h| = |s| + δ := by
    rw [hh, abs_add_mul_eq hσ h0 hδ, abs_eq_mul_of_eq_one_or_neg_one hσ h0]
  have hB'' : |s| + δ - Ξ - x = (|s| - Ξ - x) + δ := by ring
  have hA'' : x - Ξ + (1 / α).re + (|s + (1 / α).im| + δ)
      = (x - Ξ + (1 / α).re + |s + (1 / α).im|) + δ := by ring
  simp only [minmarg]
  rw [margA_vert, margA_vert, margB_vert, margB_vert, hA', hB', hA'', hB'', min_add_add_right]

/-! ### The vertical iteration -/

/-- Iteration of the two-sided Koebe bound along the vertical direction. -/
lemma deriv_le_pow_of_vert {Ξ Rde C₂ ρ K : ℝ} {α : ℂ} {Φ : ℂ → ℂ} {σ : ℝ}
    (hKpos : 0 < K)
    (hKd : ∀ (z₀ : ℂ) (R : ℝ) (z : ℂ), 0 < R →
      (∀ u ∈ Metric.ball z₀ R, AnalyticAt ℂ Φ u) → Set.InjOn Φ (Metric.ball z₀ R) →
      z ∈ Metric.ball z₀ (R / 2) → ‖deriv Φ z‖ ≤ K * ‖deriv Φ z₀‖)
    (hkey : ∀ z : ℂ, ∀ R : ℝ, Rde ≤ R → Metric.ball z R ⊆ Work.Pert.Qm Ξ α →
      ‖deriv Φ z‖ ≤ C₂ / Rde + 4 / 3)
    (hQopen : IsOpen (Work.Pert.Qm Ξ α))
    (hΦd : DifferentiableOn ℂ Φ (Work.Pert.Qm Ξ α)) (hΦi : Set.InjOn Φ (Work.Pert.Qm Ξ α))
    (hσ1 : σ = 1 ∨ σ = -1) (hRde : 0 < Rde) (hρ : 0 < ρ)
    {w : ℂ} (hw : w ∈ Work.Pert.Qm Ξ α) (hρw : ρ ≤ minmarg Ξ α w)
    {N : ℕ} (hN : Real.sqrt 2 * Rde / ρ ≤ (3 / 2 : ℝ) ^ N)
    (hσt : |(1 / α).im| ≤ σ * w.im) :
    ‖deriv Φ w‖ ≤ K ^ N * (C₂ / Rde + 4 / 3) := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hσsq : σ * σ = 1 := by rcases hσ1 with h | h <;> rw [h] <;> norm_num
  set m : ℝ := minmarg Ξ α w with hmdef
  have hmpos : 0 < m := by rw [hmdef]; exact lt_of_lt_of_le hρ hρw
  have hρm : ρ ≤ m := by rw [hmdef]; exact hρw
  set x : ℝ := w.re with hxdef
  set t : ℝ := w.im with htdef
  have hwt : w = (x : ℂ) + t * Complex.I := by
    rw [hxdef, htdef]
    apply Complex.ext <;> simp
  -- the heights of the vertical iteration
  set s : ℕ → ℝ := fun j => t + σ * (m * ((3 / 2 : ℝ) ^ j - 1)) with hsdef
  set δ : ℕ → ℝ := fun j => m * (3 / 2 : ℝ) ^ j / 2 with hδdef
  have hs_succ : ∀ j : ℕ, s (j + 1) = s j + σ * δ j := by
    intro j
    have hp : (3 / 2 : ℝ) ^ (j + 1) = (3 / 2 : ℝ) ^ j * (3 / 2) := by rw [pow_succ]
    simp only [hsdef, hδdef, hp]
    ring
  have hδpos : ∀ j : ℕ, 0 < δ j := by
    intro j
    rw [hδdef]
    have hp : (0 : ℝ) < (3 / 2 : ℝ) ^ j := by positivity
    positivity
  have hσs : ∀ j : ℕ, |(1 / α).im| ≤ σ * s j := by
    intro j
    have h1 : σ * (t + σ * (m * ((3 / 2 : ℝ) ^ j - 1)))
        = σ * t + m * ((3 / 2 : ℝ) ^ j - 1) := by
      rw [mul_add, show σ * (σ * (m * ((3 / 2 : ℝ) ^ j - 1))) = m * ((3 / 2 : ℝ) ^ j - 1) by
        rw [← mul_assoc, hσsq, one_mul]]
      try ring
    have h2 : (0 : ℝ) ≤ m * ((3 / 2 : ℝ) ^ j - 1) := by
      have hp : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      exact mul_nonneg hmpos.le (by linarith)
    simp only [hsdef]
    rw [h1]
    linarith
  -- the main induction
  have key : ∀ j : ℕ,
      minmarg Ξ α ((x : ℂ) + s j * Complex.I) = m * (3 / 2 : ℝ) ^ j
      ∧ ‖deriv Φ w‖ ≤ K ^ j * ‖deriv Φ ((x : ℂ) + s j * Complex.I)‖ := by
    intro j
    induction j with
    | zero =>
      have hs0 : s 0 = t := by simp [hsdef]
      have hpt : (x : ℂ) + s 0 * Complex.I = w := by rw [hs0, hwt]
      constructor
      · rw [hpt, pow_zero, mul_one]
      · rw [hpt, pow_zero, one_mul]
    | succ j ih =>
      obtain ⟨ihm, ihd⟩ := ih
      have hstep_min : minmarg Ξ α ((x : ℂ) + s (j + 1) * Complex.I)
          = m * (3 / 2 : ℝ) ^ j + δ j := by
        rw [minmarg_vert_step hσ1 (hσs j) (hδpos j).le (hs_succ j), ihm]
      have hnew : minmarg Ξ α ((x : ℂ) + s (j + 1) * Complex.I)
          = m * (3 / 2 : ℝ) ^ (j + 1) := by
        rw [hstep_min, hδdef, pow_succ]
        ring
      -- the distortion step from `ζ_j` to `ζ_{j+1}`
      have hRpos : 0 < minmarg Ξ α ((x : ℂ) + s (j + 1) * Complex.I) / Real.sqrt 2 := by
        rw [hnew]; positivity
      have hball : Metric.ball ((x : ℂ) + s (j + 1) * Complex.I)
          (minmarg Ξ α ((x : ℂ) + s (j + 1) * Complex.I) / Real.sqrt 2)
          ⊆ Work.Pert.Qm Ξ α :=
        ball_subset_Qm_of_minmarg (le_of_lt (by rw [hnew]; positivity))
      have hmem : (x : ℂ) + s j * Complex.I ∈ Metric.ball ((x : ℂ) + s (j + 1) * Complex.I)
          (minmarg Ξ α ((x : ℂ) + s (j + 1) * Complex.I) / Real.sqrt 2 / 2) := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hdiff : (x : ℂ) + s j * Complex.I - ((x : ℂ) + s (j + 1) * Complex.I)
            = ((-(s (j + 1) - s j) : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        rw [hdiff, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
          hnew]
        have hsub : s (j + 1) - s j = σ * δ j := by rw [hs_succ j]; ring
        simp only [hsub, abs_mul, abs_eq_one_of_eq_one_or_eq_neg_one hσ1, one_mul, hδdef,
          pow_succ]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ m * (3 / 2 : ℝ) ^ j / 2)]
        have hp : (0 : ℝ) < (3 / 2 : ℝ) ^ j := by positivity
        have hlt : (1 : ℝ) < (3 / 2) / Real.sqrt 2 := by
          rw [lt_div_iff₀ hs2]
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
        have hkey2 : m * (3 / 2 : ℝ) ^ j / 2 * ((3 / 2) / Real.sqrt 2)
            = m * ((3 / 2 : ℝ) ^ j * (3 / 2)) / Real.sqrt 2 / 2 := by ring
        rw [← hkey2]
        have hApos : (0 : ℝ) < m * (3 / 2 : ℝ) ^ j / 2 := by positivity
        nlinarith [hApos, hlt]
      have hstep : ‖deriv Φ ((x : ℂ) + s j * Complex.I)‖
          ≤ K * ‖deriv Φ ((x : ℂ) + s (j + 1) * Complex.I)‖ :=
        hKd ((x : ℂ) + s (j + 1) * Complex.I) _ ((x : ℂ) + s j * Complex.I) hRpos
          (fun u hu => hΦd.analyticAt (hQopen.mem_nhds (hball hu)))
          (hΦi.mono hball) hmem
      refine ⟨hnew, ?_⟩
      calc ‖deriv Φ w‖ ≤ K ^ j * ‖deriv Φ ((x : ℂ) + s j * Complex.I)‖ := ihd
        _ ≤ K ^ j * (K * ‖deriv Φ ((x : ℂ) + s (j + 1) * Complex.I)‖) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = K ^ (j + 1) * ‖deriv Φ ((x : ℂ) + s (j + 1) * Complex.I)‖ := by
            rw [pow_succ]; ring
  obtain ⟨hminN, hderN⟩ := key N
  have hgood : Real.sqrt 2 * Rde ≤ minmarg Ξ α ((x : ℂ) + s N * Complex.I) := by
    rw [hminN]
    have h1 : ρ * (Real.sqrt 2 * Rde / ρ) = Real.sqrt 2 * Rde := by field_simp
    calc Real.sqrt 2 * Rde = ρ * (Real.sqrt 2 * Rde / ρ) := h1.symm
      _ ≤ ρ * (3 / 2 : ℝ) ^ N := mul_le_mul_of_nonneg_left hN hρ.le
      _ ≤ m * (3 / 2 : ℝ) ^ N := mul_le_mul_of_nonneg_right hρm (by positivity)
  have hkeyN : ‖deriv Φ ((x : ℂ) + s N * Complex.I)‖ ≤ C₂ / Rde + 4 / 3 := by
    refine hkey _ _ ?_ (ball_subset_Qm_of_minmarg (le_of_lt (lt_of_lt_of_le ?_ hgood)))
    · rw [le_div_iff₀ hs2]
      linarith [hgood]
    · exact mul_pos hs2 hRde
  calc ‖deriv Φ w‖ ≤ K ^ N * ‖deriv Φ ((x : ℂ) + s N * Complex.I)‖ := hderN
    _ ≤ K ^ N * (C₂ / Rde + 4 / 3) := mul_le_mul_of_nonneg_left hkeyN (by positivity)

/-! ### The target -/

theorem bad_deriv_bound_fat {F Φ : ℂ → ℂ} {α : ℂ} {Ξ c ρ Rde C₂ : ℝ}
    (hΞ : 0 < Ξ) (hc0 : 0 ≤ c) (hρ : 0 < ρ) (hRdepos : 0 < Rde)
    (hC₂pos : 0 < C₂)
    (hDEest : ∀ (Φ' v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ' (Metric.ball z₀ R) → Set.InjOn Φ' (Metric.ball z₀ R) →
      DifferentiableOn ℂ v (Metric.ball z₀ R) → (∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ' (z + v z) = Φ' z + 1) →
      ‖deriv Φ' z₀ - 1 / v z₀‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm Ξ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm Ξ α)) :
    ∃ D : ℝ, 0 < D ∧ ∀ w : ℂ, w ∈ Work.Pert.Qm Ξ α → ρ ≤ Work.Pert.PinAux.minmarg Ξ α w →
      Real.sqrt 2 * Rde ≤ Work.Pert.PinAux.minmarg Ξ α (Work.Pert.PinAux.med Ξ α w.im) →
      ‖deriv Φ w - 1‖ ≤ D := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hQopen : IsOpen (Work.Pert.Qm Ξ α) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    refine Filter.mem_of_superset (Metric.ball_mem_nhds z (div_pos (minmarg_pos_of_mem hz) hs2)) ?_
    exact ball_subset_Qm_of_minmarg (le_of_lt (minmarg_pos_of_mem hz))
  -- (1) Shishikura A.2.4(i) at every centre where a ball of radius `Rde` fits in the gate
  have hkey : ∀ z : ℂ, ∀ R : ℝ, Rde ≤ R → Metric.ball z R ⊆ Work.Pert.Qm Ξ α →
      ‖deriv Φ z‖ ≤ C₂ / Rde + 4 / 3 := by
    intro z R hR hball
    have hz : z ∈ Work.Pert.Qm Ξ α := hball (Metric.mem_ball_self (lt_of_lt_of_le hRdepos hR))
    have hDE := hDEest Φ (fun u : ℂ => F u - u) z R hR
      (hΦ.1.mono hball) (hΦ.2.1.mono hball) ((hNT.1.1.mono hball).sub differentiableOn_id)
      (fun u hu => by
        have h := (hNT.1.2 u (hball hu)).1
        rw [show F u - u - 1 = F u - (u + 1) by ring]
        linarith)
      (fun u hu hu2 => by
        have huQ : u ∈ Work.Pert.Qm Ξ α := hball hu
        have hFuQ : F u ∈ Work.Pert.Qm Ξ α := by
          have : u + (F u - u) = F u := by ring
          rw [← this]; exact hball hu2
        have h := hΦ.2.2 u huQ hFuQ
        rw [show u + (F u - u) = F u by ring]; exact h)
    have hv : ‖F z - z - 1‖ ≤ 1 / 32 := by
      have h := (hNT.1.2 z hz).1
      rwa [show F z - (z + 1) = F z - z - 1 by ring] at h
    have h3 : (3 : ℝ) / 4 ≤ ‖F z - z‖ := by
      have h := abs_norm_sub_norm_le (F z - z) 1
      rw [norm_one] at h
      have h5 : |‖F z - z‖ - 1| ≤ 1 / 32 := le_trans h hv
      rw [abs_le] at h5
      linarith [h5.1]
    have h4 : ‖1 / (F z - z)‖ ≤ 4 / 3 := by
      rw [one_div, norm_inv]
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 4) h3
      simpa using this
    have h5 : C₂ / R ≤ C₂ / Rde := div_le_div_of_nonneg_left hC₂pos.le hRdepos hR
    calc ‖deriv Φ z‖ = ‖(deriv Φ z - 1 / (F z - z)) + 1 / (F z - z)‖ := by congr 1; ring
      _ ≤ ‖deriv Φ z - 1 / (F z - z)‖ + ‖1 / (F z - z)‖ := norm_add_le _ _
      _ ≤ C₂ / Rde + 4 / 3 := add_le_add (le_trans hDE h5) h4
  -- (2) the two-sided Koebe distortion constant
  obtain ⟨K, hKpos, hKd⟩ := Work.FatouL1.deriv_le_deriv_mul_of_injOn_ball
  have hKd' : ∀ (z₀ : ℂ) (R : ℝ) (z : ℂ), 0 < R →
      (∀ u ∈ Metric.ball z₀ R, AnalyticAt ℂ Φ u) → Set.InjOn Φ (Metric.ball z₀ R) →
      z ∈ Metric.ball z₀ (R / 2) → ‖deriv Φ z‖ ≤ K * ‖deriv Φ z₀‖ :=
    fun z₀ R z hR hA hI hmem => hKd Φ z₀ R z hR hA hI hmem
  -- (3) compactness for the points of bounded height
  have hcomp : ∃ M : ℝ, ∀ z : ℂ, z ∈ Work.Pert.Qm Ξ α → ρ ≤ minmarg Ξ α z →
      |z.im| ≤ |(1 / α).im| → ‖deriv Φ z‖ ≤ M := by
    have hcontA : Continuous fun z : ℂ => margA Ξ α z := by
      have h : (fun z : ℂ => margA Ξ α z)
          = fun z : ℂ => z.re - Ξ + (1 / α).re + |z.im + (1 / α).im| := by
        funext z; rw [Work.Pert.margA]
      rw [h]; fun_prop
    have hcontB : Continuous fun z : ℂ => margB Ξ α z := by
      have h : (fun z : ℂ => margB Ξ α z) = fun z : ℂ => |z.im| - Ξ - z.re := by
        funext z; rw [Work.Pert.margB]
      rw [h]; fun_prop
    have hcont : Continuous fun z : ℂ => minmarg Ξ α z := by
      have h : (fun z : ℂ => minmarg Ξ α z)
          = fun z : ℂ => min (margA Ξ α z) (margB Ξ α z) := by
        funext z; rw [minmarg]
      rw [h]; exact hcontA.min hcontB
    have hcontderiv : ContinuousOn (deriv Φ) (Work.Pert.Qm Ξ α) :=
      ((hΦ.1).contDiffOn hQopen).continuousOn_deriv_of_isOpen hQopen le_top
    set T : ℝ := |(1 / α).im| with hTdef
    set Kset : Set ℂ := {z : ℂ | ρ ≤ minmarg Ξ α z ∧ |z.im| ≤ T} with hKsetdef
    have hKclosed : IsClosed Kset := by
      rw [hKsetdef]
      exact (isClosed_le continuous_const hcont).inter
        (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
    have hKbdd : Bornology.IsBounded Kset := by
      refine Metric.isBounded_closedBall (x := (0 : ℂ)) (r :=
        |T - Ξ - ρ| + |ρ + Ξ - (1 / α).re - (T + |(1 / α).im|)| + T + 1) |>.subset ?_
      intro z hz
      rw [hKsetdef] at hz
      obtain ⟨hmin, him⟩ := hz
      have hmA : ρ ≤ margA Ξ α z := le_trans hmin (minmarg_le_margA Ξ α z)
      have hmB : ρ ≤ margB Ξ α z := le_trans hmin (minmarg_le_margB Ξ α z)
      rw [Work.Pert.margA] at hmA
      rw [Work.Pert.margB] at hmB
      have hc : |z.im + (1 / α).im| ≤ T + |(1 / α).im| := by
        calc |z.im + (1 / α).im| ≤ |z.im| + |(1 / α).im| := abs_add_le _ _
          _ ≤ T + |(1 / α).im| := by linarith
      have hre_ub : z.re ≤ T - Ξ - ρ := by linarith
      have hre_lb : ρ + Ξ - (1 / α).re - (T + |(1 / α).im|) ≤ z.re := by linarith
      have hre : |z.re| ≤ |ρ + Ξ - (1 / α).re - (T + |(1 / α).im|)| + |T - Ξ - ρ| := by
        rw [abs_le]
        constructor
        · linarith [neg_abs_le (ρ + Ξ - (1 / α).re - (T + |(1 / α).im|)), abs_nonneg (T - Ξ - ρ)]
        · linarith [le_abs_self (T - Ξ - ρ), abs_nonneg (ρ + Ξ - (1 / α).re - (T + |(1 / α).im|))]
      have him' : |z.im| ≤ T := him
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      linarith
    have hKcpt : IsCompact Kset := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKclosed, hKbdd⟩
    have hKQ : Kset ⊆ Work.Pert.Qm Ξ α := by
      intro z hz
      rw [hKsetdef] at hz
      exact mem_Qm_iff_minmarg_pos.mpr (lt_of_lt_of_le hρ hz.1)
    obtain ⟨M, hM⟩ := hKcpt.exists_bound_of_continuousOn (hcontderiv.mono hKQ)
    exact ⟨M, fun z hz hρz himz => hM z (by rw [hKsetdef]; exact ⟨hρz, himz⟩)⟩
  obtain ⟨M, hM⟩ := hcomp
  -- (4) the number of vertical steps
  set Y : ℝ := Real.sqrt 2 * Rde / ρ with hYdef
  have hYpos : 0 < Y := by rw [hYdef]; positivity
  set N : ℕ := Nat.ceil (2 * Y) with hNdef
  have hNceil : 2 * Y ≤ (N : ℝ) := by
    rw [hNdef]
    exact Nat.le_ceil (2 * Y)
  have hNpow : Y ≤ (3 / 2 : ℝ) ^ N := by
    have hber := one_add_mul_le_pow (a := (1 / 2 : ℝ)) (by norm_num) N
    have h3 : ((1 : ℝ) + 1 / 2) = 3 / 2 := by norm_num
    rw [h3] at hber
    linarith
  refine ⟨max (max 0 M + 1) (K ^ N * (C₂ / Rde + 4 / 3) + 1), ?_, ?_⟩
  · refine lt_of_lt_of_le zero_lt_one (le_trans ?_ (le_max_left _ _))
    have h3 : (0 : ℝ) ≤ max 0 M := le_max_left 0 M
    linarith
  · intro w hw hρw hfatw
    have hnorm1 : ‖deriv Φ w - 1‖ ≤ ‖deriv Φ w‖ + 1 := by
      calc ‖deriv Φ w - 1‖ ≤ ‖deriv Φ w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖deriv Φ w‖ + 1 := by rw [norm_one]
    by_cases htw : |w.im| ≤ |(1 / α).im|
    · have h1 := hM w hw hρw htw
      have h2 : M ≤ max 0 M := le_max_right 0 M
      have h3 : (0 : ℝ) ≤ max 0 M := le_max_left 0 M
      calc ‖deriv Φ w - 1‖ ≤ ‖deriv Φ w‖ + 1 := hnorm1
        _ ≤ M + 1 := by linarith
        _ ≤ max 0 M + 1 := by linarith
        _ ≤ max (max 0 M + 1) (K ^ N * (C₂ / Rde + 4 / 3) + 1) := le_max_left _ _
    · have htw' : |(1 / α).im| < |w.im| := not_le.mp htw
      by_cases ht0 : 0 < w.im
      · have hσt : |(1 / α).im| ≤ (1 : ℝ) * w.im := by
          rw [one_mul, ← abs_of_pos ht0]; exact htw'.le
        have h2 := deriv_le_pow_of_vert (Ξ := Ξ) (Rde := Rde) (C₂ := C₂) (ρ := ρ) (K := K)
          (α := α) (Φ := Φ) (σ := 1) hKpos hKd' hkey hQopen hΦ.1 hΦ.2.1 (Or.inl rfl)
          hRdepos hρ hw hρw hNpow hσt
        calc ‖deriv Φ w - 1‖ ≤ ‖deriv Φ w‖ + 1 := hnorm1
          _ ≤ K ^ N * (C₂ / Rde + 4 / 3) + 1 := by linarith
          _ ≤ max (max 0 M + 1) (K ^ N * (C₂ / Rde + 4 / 3) + 1) := le_max_right _ _
      · have htneg : w.im < 0 := by
          rcases lt_or_eq_of_le (not_lt.mp ht0) with h | h
          · exact h
          · exfalso
            rw [h] at htw'
            simp only [abs_zero] at htw'
            exact absurd htw' (not_lt.mpr (abs_nonneg (1 / α).im))
        have hσt : |(1 / α).im| ≤ (-1 : ℝ) * w.im := by
          rw [neg_one_mul, ← abs_of_neg htneg]
          exact htw'.le
        have h2 := deriv_le_pow_of_vert (Ξ := Ξ) (Rde := Rde) (C₂ := C₂) (ρ := ρ) (K := K)
          (α := α) (Φ := Φ) (σ := -1) hKpos hKd' hkey hQopen hΦ.1 hΦ.2.1 (Or.inr rfl)
          hRdepos hρ hw hρw hNpow hσt
        calc ‖deriv Φ w - 1‖ ≤ ‖deriv Φ w‖ + 1 := hnorm1
          _ ≤ K ^ N * (C₂ / Rde + 4 / 3) + 1 := by linarith
          _ ≤ max (max 0 M + 1) (K ^ N * (C₂ / Rde + 4 / 3) + 1) := le_max_right _ _

end

end Work.Pert.PinAux
