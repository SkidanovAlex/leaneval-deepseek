import Mathlib
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk_le
import Submission.Work.Pert.Ksub2.deriv_phi_strip_lower_bdd
import Submission.Work.Pert.Ksub2.deriv_Phi_close_ball
import Submission.Work.Pert.Ksub2.walk_translate_deriv_le
import Submission.Work.Pert.Ksub2.walk_translate_mem_Dphi

/-!
# `Work.Pert.Ksub2.walk_explicit`

Two variants of lemmas of `Ksub2` in which the *thresholds* produced existentially are replaced by
explicit (datum-determined) expressions, so that downstream callers can bound them.

* `deriv_phi_bounds_walk_le_bdd` — same contract as `deriv_phi_bounds_walk_le`, but the depth
  threshold `M₀` is the **explicit** one of `deriv_phi_strip_lower_bdd`, and the lower constant is
  the explicit `1/64` (instead of an opaque witness of `deriv_phi_strip_lower`).  Hence
  `M₀ ≤ max 1 (max (C₀+2) (max (Tb+4) (…)))` and `Ce₀ ≤ max 1 (max C Cd)`, both explicit.
* `deriv_Phi_sub_one_le` — the *quantitative* form of `deriv_Phi_close_ball`:
  `‖Φ' - 1‖ ≤ C₂/R + 1/31` (rather than the bare `≤ 1/2`), which is what
  `Work.Pert.dev_le_right_strip_v3` / `Work.Pert.goodP_high_strip` consume as `hder`.
-/

namespace Work.Pert.Ksub2

open MandelDim Complex Set Metric

noncomputable section

/-- A point within `ρe` of a walk point `w - m` lies in `d.Dφ` (`walk_translate_mem_Dphi`),
re-exported at the argument order used below. -/
private lemma aux_walk_mem' {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} {ρe Tb R : ℝ} {w : ℂ} (hw : w ∈ K') (hTb : ∀ w ∈ K', ‖w‖ ≤ Tb)
    (hZsub : ∀ k ∈ Finset.range (⌈Tb + max R (d.ξ₀ + 1) + ρe⌉₊ + 1),
        ∀ u ∈ (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K'), u ∈ d.Dφ)
    {m : ℕ} {z : ℂ} (hz : ‖z - (w - (m : ℂ))‖ ≤ ρe) : z ∈ d.Dφ :=
  walk_translate_mem_Dphi d hw hTb hZsub hz

/-- The deep/shallow derivative bound at a walk point. -/
private lemma aux_walk_deriv' {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} {ρe Tb R C Cd : ℝ} {w : ℂ} (hw : w ∈ K') (hρe : 0 ≤ ρe)
    (hTb : ∀ w ∈ K', ‖w‖ ≤ Tb)
    (hdeep : ∀ u : ℂ, u ∈ d.Dφ → R ≤ -u.re → |u.im| ≤ Tb + ρe → ‖deriv d.φ u‖ ≤ C)
    (hshallow : ∀ u ∈ (⋃ k ∈ Finset.range (⌈R + Tb + ρe⌉₊ + 1),
        (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K')), ‖deriv d.φ u‖ ≤ Cd)
    {m : ℕ} {z : ℂ} (hz : ‖z - (w - (m : ℂ))‖ ≤ ρe) (hzD : z ∈ d.Dφ) :
    ‖deriv d.φ z‖ ≤ max C Cd :=
  walk_translate_deriv_le d hw hρe hTb hdeep hshallow hz hzD

/-- **The walk bound with explicit thresholds.**  Same contract as
`Work.Pert.Ksub2.deriv_phi_bounds_walk_le`, but the depth threshold `M₀` is the explicit one of
`deriv_phi_strip_lower_bdd` (invoked at the strip parameter `Tb + 1`, with the curvature constant
`C₀` of the caller) and the lower constant is the explicit `1/64`. -/
theorem deriv_phi_bounds_walk_le_bdd {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ)
    {ρe Tb R C Cd : ℝ}
    (hρe : 0 < ρe) (hρele : ρe ≤ 1 / 4)
    (hTb : ∀ w ∈ K', ‖w‖ ≤ Tb) (hTb1 : (1 : ℝ) ≤ Tb)
    (hballw : ∀ w ∈ K', Metric.ball w ρe ⊆ d.Dφ)
    (hdeep : ∀ u : ℂ, u ∈ d.Dφ → R ≤ -u.re → |u.im| ≤ Tb + ρe → ‖deriv d.φ u‖ ≤ C)
    (hshallow : ∀ u ∈ (⋃ k ∈ Finset.range (⌈R + Tb + ρe⌉₊ + 1),
        (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K')), ‖deriv d.φ u‖ ≤ Cd)
    (hZsub : ∀ k ∈ Finset.range (⌈Tb + max R (d.ξ₀ + 1) + ρe⌉₊ + 1),
        ∀ u ∈ (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K'), u ∈ d.Dφ)
    {C₀ R_A R_B R_L : ℝ} {a b : ℂ}
    (hC₀ : 0 < C₀)
    (hXcur : ∀ u : ℂ, u ∈ MandelDim.QLeft d.ξ₀ → C₀ ≤ ‖u‖ →
      Metric.ball u (‖u‖ / 10) ⊆ MandelDim.QLeft d.ξ₀ →
      ‖Work.Pert.Xc d u - u‖ ≤ C₀ * (1 + Real.log ‖u‖) ∧
      ‖deriv (Work.Pert.Xc d) u - 1‖ ≤ C₀ * (1 + Real.log ‖u‖) / ‖u‖)
    (hA : ∀ w : ℂ, w ∈ MandelDim.QLeft d.ξ₀ → R_A < ‖w‖ →
      ‖MandelDim.tau0 (d.φ w) - (w + a * Complex.log (-w) + b)‖ < 1)
    (hB : ∀ u : ℂ, R_B ≤ ‖u‖ → 1 ≤ ‖u + a * Complex.log (-u) + b‖)
    (hL : ∀ x : ℝ, R_L ≤ x → C₀ * Real.log (2 * x) + C₀ < x / 4) :
    ∃ M₀ : ℝ, 0 < M₀ ∧
      M₀ ≤ max 1 (max (C₀ + 2) (max (Tb + 1 + 3) (max (d.ξ₀ + 2)
        (max (max R_A R_B + 1) (max R_L ((10 / 9) * (d.ξ₀ + 1 / 4 + (Tb + 1 + 3 / 2) / 10 + 1))))))) ∧
      ∃ Ce₀ : ℝ, 0 < Ce₀ ∧ Ce₀ ≤ max 1 (max C Cd) ∧
      ∀ M : ℝ, M₀ ≤ M → ∀ w ∈ K', ∀ u ∈ Work.Pert.Dstrip M (Tb + 1), ∀ n : ℕ, u + (n : ℂ) = w →
        (∀ i : ℕ, i ≤ n → Metric.ball (u + (i : ℂ)) ρe ⊆ d.Dφ ∧
          ∀ z : ℂ, z ∈ d.Dφ → ‖z - (u + (i : ℂ))‖ ≤ ρe → ‖deriv d.φ z‖ ≤ Ce₀) ∧
        (∀ z : ℂ, z ∈ d.Dφ → ‖z - u‖ ≤ ρe → (1 / 64) / (M * M) ≤ ‖deriv d.φ z‖) := by
  obtain ⟨Mwalk, hMwalkpos, hMwalkle, hMwalkbnd⟩ :=
    deriv_phi_strip_lower_bdd d (T := Tb + 1) hC₀ hXcur hA hB hL
  have _ := hballw
  have _ := hTb1
  have _ := hK'c
  have _ := hK'
  refine ⟨Mwalk, hMwalkpos, hMwalkle, max 1 (max C Cd),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), le_refl _, ?_⟩
  intro M hM w hw u hu n hn
  constructor
  · -- ## Clause 1
    intro i hi
    have hp : u + (i : ℂ) = w - ((n - i : ℕ) : ℂ) := by
      rw [Nat.cast_sub hi, ← hn]; ring
    rw [hp]
    have hmem : ∀ z : ℂ, ‖z - (w - ((n - i : ℕ) : ℂ))‖ ≤ ρe → z ∈ d.Dφ :=
      fun z hz => aux_walk_mem' d hw hTb hZsub hz
    have hbd : ∀ z : ℂ, z ∈ d.Dφ → ‖z - (w - ((n - i : ℕ) : ℂ))‖ ≤ ρe →
        ‖deriv d.φ z‖ ≤ max C Cd :=
      fun z hzD hz => aux_walk_deriv' d hw (le_of_lt hρe) hTb hdeep hshallow hz hzD
    constructor
    · intro z hz
      exact hmem z (by rw [← dist_eq_norm]; exact le_of_lt (Metric.mem_ball.mp hz))
    · intro z hzD hzd
      exact le_trans (hbd z hzD hzd) (le_max_right 1 (max C Cd))
  · -- ## Clause 2
    intro z hzD hzd
    exact hMwalkbnd M hM u hu z hzD (le_trans hzd hρele)

/-- **The quantitative derivative estimate on gate balls.**  This is `deriv_Phi_close_ball` with
the bound `C₂/R + 1/31` in place of the bare `1/2`: the two sources of the `1/31` are the inverse
of the vertical displacement map `v = F - id` (`‖1/v - 1‖ ≤ 1/31` on the gate, from
`NearTranslationL1`) and the estimate `‖Φ' - 1/v‖ ≤ C₂/R` of Lemma A.2.4(i). -/
theorem deriv_Phi_sub_one_le {F Φ : ℂ → ℂ} {α : ℂ} {ξ₁ Rde C₁ C₂ : ℝ}
    (hRdepos : 0 < Rde) (hC₁pos : 0 < C₁) (hC₂pos : 0 < C₂)
    (hDEest : ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), Rde ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z₀ R) → Set.InjOn Φ (Metric.ball z₀ R) →
      DifferentiableOn ℂ v (Metric.ball z₀ R) → (∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ (z + v z) = Φ z + 1) →
      ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₁ * (1 / R ^ 2 + ‖deriv v z₀‖) ∧
      ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₂ / R)
    (hNT : MandelDim.NearTranslationL1 F (Work.Pert.Qm ξ₁ α))
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Work.Pert.Qm ξ₁ α)) :
    ∀ (w : ℂ) (R : ℝ), max Rde (64 * C₂) ≤ R → Metric.ball w R ⊆ Work.Pert.Qm ξ₁ α →
      ‖deriv Φ w - 1‖ ≤ C₂ / R + 1 / 31 := by
  intro w R hR hball
  have hRQ : Rde ≤ R := le_trans (le_max_left _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le hRdepos hRQ
  have hwball : w ∈ Metric.ball w R := Metric.mem_ball_self hRpos
  have hwQ : w ∈ Work.Pert.Qm ξ₁ α := hball hwball
  set v : ℂ → ℂ := fun u => F u - u with hv
  have hvdiff : DifferentiableOn ℂ v (Metric.ball w R) := by
    have h1 : DifferentiableOn ℂ (fun u : ℂ => F u - u) (Metric.ball w R) :=
      (hNT.1.1.mono hball).sub differentiableOn_id
    simpa [hv] using h1
  have hvnear : ∀ u ∈ Metric.ball w R, ‖v u - 1‖ < 1 / 4 := by
    intro u hu
    have huQ : u ∈ Work.Pert.Qm ξ₁ α := hball hu
    have hbound : ‖v u - 1‖ ≤ 1 / 32 := by
      have heq : v u - 1 = F u - (u + 1) := by simp only [hv]; ring
      rw [heq]; exact (hNT.1.2 u huQ).1
    linarith
  have habel : ∀ u ∈ Metric.ball w R, u + v u ∈ Metric.ball w R →
      Φ (u + v u) = Φ u + 1 := by
    intro u hu huv
    have huQ : u ∈ Work.Pert.Qm ξ₁ α := hball hu
    have heq : u + v u = F u := by simp only [hv]; ring
    have hFQ : F u ∈ Work.Pert.Qm ξ₁ α := by rw [← heq]; exact hball huv
    have h := hΦ.2.2 u huQ hFQ
    rwa [heq]
  have hΦdiff : DifferentiableOn ℂ Φ (Metric.ball w R) := hΦ.1.mono hball
  have hΦinj : Set.InjOn Φ (Metric.ball w R) := hΦ.2.1.mono hball
  obtain ⟨_, hb2⟩ := hDEest Φ v w R hRQ hΦdiff hΦinj hvdiff hvnear habel
  -- `‖1/v w - 1‖ ≤ 1/31`
  have hvw : ‖v w - 1‖ ≤ 1 / 32 := by
    have heq : v w - 1 = F w - (w + 1) := by simp only [hv]; ring
    rw [heq]; exact (hNT.1.2 w hwQ).1
  have h1a : ‖1 - v w‖ ≤ 1 / 32 := by
    rw [norm_sub_rev (1 : ℂ) (v w)]; exact hvw
  have hanorm : (31 : ℝ) / 32 ≤ ‖v w‖ := by
    have h1 : (1 : ℝ) ≤ ‖v w‖ + ‖1 - v w‖ := by
      have he : (1 : ℂ) = v w + (1 - v w) := by ring
      calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
        _ = ‖v w + (1 - v w)‖ := congrArg (fun x : ℂ => ‖x‖) he
        _ ≤ ‖v w‖ + ‖1 - v w‖ := norm_add_le _ _
    linarith
  have hne : v w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hanorm
    norm_num at hanorm
  have hvinv : ‖1 / v w - 1‖ ≤ 1 / 31 := by
    rw [div_sub_one hne, norm_div]
    calc ‖1 - v w‖ / ‖v w‖ ≤ (1 / 32) / (31 / 32) :=
          div_le_div₀ (by norm_num) h1a (by norm_num) hanorm
      _ = 1 / 31 := by norm_num
  have htri : ‖deriv Φ w - 1‖ ≤ ‖deriv Φ w - 1 / v w‖ + ‖1 / v w - 1‖ := by
    have he : deriv Φ w - 1 = (deriv Φ w - 1 / v w) + (1 / v w - 1) := by ring
    rw [he]; exact norm_add_le _ _
  linarith [hb2, hvinv, htri]

end

end Work.Pert.Ksub2
