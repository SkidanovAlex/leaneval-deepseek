import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.model_deep_branch
import Submission.Work.L62.E_equivariant_of_eta0

/-!
# `Work.Horn.deep_branch_bu`

The deep inverse branch of the lifted horn map `d.E` of §4.1 data `d : ParabData f₀ D₀`: for a set
`Bu` containing the upper half plane `{η < Im ·}` there is a holomorphic `H` on a deep half plane
with `d.E (H w) = w`, `H w ∈ Bu`, `‖H w - w‖ ≤ 1/4`, `H (w + 1) = H w + 1` and `H w - w → 0` at
the upper end.

This is `Work.L62.model_deep_branch_nosign` (equivalently `Work.L62.avail_deep_branch_nosign`) at
`β = 0`, but with the `HornData` hypothesis replaced by the single half-plane statement on `Bu`
(the only two things the model's branch proof used from `HornData` are `η` and
`{η < Im ·} ⊆ Bu`).

Proof.  `Ψ := d.E - id` is holomorphic, with `‖Ψ‖ ≤ 1/8` and `‖deriv Ψ‖ ≤ 1/2`, on a deep half
plane `Ω = {Y < Im ·}` (`Work.L62.model_deep_correction_bounds`, from `E_upper`), and is
`1`-periodic there (`Work.L62.E_equivariant_of_eta0`).  Hence `u ↦ w - Ψ u` is a `1/2`-contraction
of `closedBall w (1/4)` into itself, and `Work.L62.model_deep_contraction` produces the family of
fixed points `H`, holomorphically in `w`.  The fixed point equation `H w = w - Ψ (H w)` is
`d.E (H w) = w`; the closeness `‖H w - w‖ ≤ 1/4` is the ball membership, which also forces
`Im (H w) > η` for `w` deep, whence `H w ∈ Bu`; the `1`-periodicity of `Ψ` makes `H (w+1) - 1`
another fixed point of the same contraction (in the same ball), so it equals `H w`
(`H (w+1) = H w + 1`); and `H w - w = -Ψ (H w) → 0` because `Im (H w) → +∞`.

-/

namespace Work.Horn

open Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-! ## Fixed points of `u ↦ w - Ψ u` -/

/-- Unpacking the fixed point equation of `u ↦ w - Ψ u` into `F u = w`, where `Ψ = F - id`. -/
private lemma deep_eq_of_fixpt {Ψ F : ℂ → ℂ} (hΨF : ∀ u : ℂ, Ψ u = F u - u) {u w : ℂ}
    (h : u = w - Ψ u) : F u = w := by
  have h1 : u + Ψ u = w := by nth_rewrite 1 [h]; ring
  rw [hΨF u] at h1
  have h2 : u + (F u - u) = F u := by ring
  rwa [h2] at h1

/-- The displacement of a fixed point of `u ↦ w - Ψ u`. -/
private lemma deep_sub_eq_neg_of_fixpt {Ψ : ℂ → ℂ} {u w : ℂ} (h : u = w - Ψ u) :
    u - w = -(Ψ u) := by
  nth_rewrite 1 [h]; ring

theorem deep_branch_bu {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Bu : Set ℂ} {η : ℝ} (hup : {w : ℂ | η < Complex.im w} ⊆ Bu) :
    ∃ y' : ℝ, η < y' ∧ ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H {w : ℂ | y' < Complex.im w} ∧
      (∀ w : ℂ, y' < Complex.im w → H w ∈ Bu ∧ d.E (H w) = w) ∧
      (∀ w : ℂ, y' < Complex.im w → ‖H w - w‖ ≤ 1 / 4) ∧
      (∀ w : ℂ, y' < Complex.im w → H (w + 1) = H w + 1) ∧
      (∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, R < Complex.im w → ‖H w - w‖ < ε) := by
  obtain ⟨Y, hYη, hΨdiff, hΨsmall, hΨderiv⟩ :=
    Work.L62.model_deep_correction_bounds d (κ := 1) one_pos
  set Ψ : ℂ → ℂ := fun u : ℂ => d.E u - u with hΨdef
  have hΨE : ∀ u : ℂ, Ψ u = d.E u - u := fun u => by simp only [hΨdef]
  -- `Ψ` is `1`-periodic on the deep half plane
  have hΨper : ∀ u : ℂ, Y < u.im → Ψ (u + 1) = Ψ u := by
    intro u hu
    have h := Work.L62.E_equivariant_of_eta0 d
      (lt_of_lt_of_le (lt_trans hYη hu) (le_abs_self u.im))
    simp only [hΨdef]
    rw [h]
    ring
  set r : ℝ := 1 / 4 with hrdef
  have hr : 0 < r := by rw [hrdef]; norm_num
  -- the depth of the branch
  set y' : ℝ := max (max (Y + r) (η + r)) η + 1 with hy'def
  have hy'ηr : η + r < y' := by
    rw [hy'def]
    have h1 : η + r ≤ max (Y + r) (η + r) := le_max_right _ _
    have h2 : max (Y + r) (η + r) ≤ max (max (Y + r) (η + r)) η := le_max_left _ _
    linarith
  have hy'Yr : Y + r < y' := by
    rw [hy'def]
    have h1 : Y + r ≤ max (Y + r) (η + r) := le_max_left _ _
    have h2 : max (Y + r) (η + r) ≤ max (max (Y + r) (η + r)) η := le_max_left _ _
    linarith
  have hy'η : η < y' := by linarith [hy'ηr, hr]
  refine ⟨y', hy'η, ?_⟩
  set s : Set ℂ := {w : ℂ | y' < w.im} with hsdef
  have hsopen : IsOpen s := by rw [hsdef]; exact isOpen_lt continuous_const continuous_im
  set Ω : Set ℂ := {u : ℂ | Y < u.im} with hΩdef
  have hΩopen : IsOpen Ω := by rw [hΩdef]; exact isOpen_lt continuous_const continuous_im
  have hΨΩ : DifferentiableOn ℂ Ψ Ω := by rw [hΨdef, hΩdef]; exact hΨdiff
  have hmem_s : ∀ {w : ℂ}, y' < w.im → w ∈ s := by intro w hw; rw [hsdef]; exact hw
  -- the contraction balls sit inside the deep half plane
  have hball : ∀ w ∈ s, Metric.closedBall w r ⊆ Ω := by
    intro w hw u hu
    have h1 : ‖u - w‖ ≤ r := by
      have h := Metric.mem_closedBall.mp hu
      rwa [dist_eq_norm] at h
    have h2 : u.im ≥ w.im - ‖u - w‖ := by
      have h3 := (abs_le.mp (Complex.abs_im_le_norm (u - w))).1
      rw [Complex.sub_im] at h3
      linarith
    rw [hΩdef]
    simp only [Set.mem_ofPred_eq]
    have hw' : y' < w.im := hw
    linarith [hy'Yr, h1, h2]
  have hballβ : ∀ w ∈ s, Metric.closedBall (w + (0 : ℂ)) r ⊆ Ω := by
    intro w hw
    simpa only [add_zero] using hball w hw
  have hsmallc : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + (0 : ℂ)) r,
      ‖Ψ u‖ ≤ (1 - 1 / 2) * r := by
    intro w hw u hu
    have huΩ : u ∈ Ω := hballβ w hw hu
    rw [hΩdef] at huΩ
    have h := hΨsmall u huΩ
    rw [hΨdef]
    refine h.trans ?_
    rw [min_self, hrdef]
    norm_num
  have hlipc : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + (0 : ℂ)) r,
      ‖deriv Ψ u‖ ≤ (1 / 2 : ℝ) := by
    intro w hw u hu
    have huΩ : u ∈ Ω := hballβ w hw hu
    rw [hΩdef] at huΩ
    have h := hΨderiv u huΩ
    rwa [hΨdef] at h
  obtain ⟨H, hHdiff, hHfix, hHuniq⟩ :=
    Work.L62.model_deep_contraction hsopen hΩopen hΨΩ (β := 0) hr
      (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1) hballβ hsmallc hlipc
  -- basic consequences of the fixed point equation
  have hHbd : ∀ w ∈ s, ‖H w - w‖ ≤ r := by
    intro w hw
    have h := Metric.mem_closedBall.mp (hHfix w hw).1
    rw [dist_eq_norm] at h
    simpa only [add_zero] using h
  have hHΩ : ∀ w ∈ s, H w ∈ Ω := fun w hw => hballβ w hw (hHfix w hw).1
  have hfix' : ∀ w ∈ s, H w = w - Ψ (H w) := fun w hw =>
    by simpa only [add_zero] using (hHfix w hw).2
  have hEdot : ∀ w ∈ s, d.E (H w) = w := fun w hw => deep_eq_of_fixpt hΨE (hfix' w hw)
  have hρval : ∀ w ∈ s, H w - w = -(Ψ (H w)) := fun w hw =>
    deep_sub_eq_neg_of_fixpt (hfix' w hw)
  -- `T`-equivariance, by uniqueness in the contraction ball
  have hHper : ∀ w ∈ s, H (w + 1) = H w + 1 := by
    intro w hw
    have hw1 : w + 1 ∈ s := by
      rw [hsdef] at hw ⊢
      simp only [Set.mem_ofPred_eq] at hw ⊢
      rw [Complex.add_im, Complex.one_im]
      linarith
    have hfix1 := hHfix (w + 1) hw1
    have hd1 : ‖H (w + 1) - (w + 1)‖ ≤ r := by
      have h := Metric.mem_closedBall.mp hfix1.1
      rw [dist_eq_norm] at h
      simpa only [add_zero] using h
    have hmem1' : H (w + 1) - 1 ∈ Metric.closedBall w r := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hz : H (w + 1) - 1 - w = H (w + 1) - (w + 1) := by ring
      rw [hz]
      exact hd1
    have hmem1'β : H (w + 1) - 1 ∈ Metric.closedBall (w + (0 : ℂ)) r := by
      simpa only [add_zero] using hmem1'
    have hperψ : Ψ (H (w + 1) - 1) = Ψ (H (w + 1)) := by
      have hmΩ : H (w + 1) - 1 ∈ Ω := hball w hw hmem1'
      rw [hΩdef] at hmΩ
      have hz : (H (w + 1) - 1) + 1 = H (w + 1) := by ring
      have h := hΨper (H (w + 1) - 1) hmΩ
      rw [hz] at h
      exact h.symm
    have hpt : H (w + 1) - 1 = w + (0 : ℂ) - Ψ (H (w + 1) - 1) := by
      have h1 : H (w + 1) = (w + 1) - Ψ (H (w + 1)) := hfix' (w + 1) hw1
      have h2 : H (w + 1) = w + 1 - Ψ (H (w + 1) - 1) := by
        conv_lhs => rw [h1]
        rw [hperψ]
      linear_combination h2
    have hconcl := hHuniq w hw (H (w + 1) - 1) hmem1'β hpt
    rw [← hconcl]
    ring_nf
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hsdef] using hHdiff
  · intro w hw
    have hws : w ∈ s := hmem_s hw
    have hbd := hHbd w hws
    have him : η < (H w).im := by
      have h3 := (abs_le.mp (Complex.abs_im_le_norm (H w - w))).1
      rw [Complex.sub_im] at h3
      linarith [hy'ηr, hbd, hw, h3, hr]
    exact ⟨hup him, hEdot w hws⟩
  · intro w hw
    simpa only [hrdef] using hHbd w (hmem_s hw)
  · intro w hw
    exact hHper w (hmem_s hw)
  · -- `H w - w = -Ψ (H w) → 0` at the upper end
    intro ε hε
    obtain ⟨R₁, hR₁⟩ := Work.L62.model_deep_correction_small d ε hε
    refine ⟨max (y' + 1) (R₁ + r + 1), fun w hw => ?_⟩
    have hb' : y' < w.im :=
      lt_of_le_of_lt (by linarith [le_max_left (y' + 1) (R₁ + r + 1)] : y' ≤ max (y' + 1) (R₁ + r + 1)) hw
    have hb'' : R₁ + r + 1 ≤ w.im :=
      le_of_lt (lt_of_le_of_lt (le_max_right (y' + 1) (R₁ + r + 1)) hw)
    have hws : w ∈ s := hmem_s hb'
    have hbd := hHbd w hws
    have him : R₁ < (H w).im := by
      have h3 := (abs_le.mp (Complex.abs_im_le_norm (H w - w))).1
      rw [Complex.sub_im] at h3
      linarith [hbd, hb'', h3]
    rw [hρval w hws, norm_neg]
    exact hR₁ (H w) him

end

end Work.Horn
