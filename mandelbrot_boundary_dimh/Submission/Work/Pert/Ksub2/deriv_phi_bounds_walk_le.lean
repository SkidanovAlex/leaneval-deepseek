import Mathlib
import Submission.Work.Pert.Ksub2.deriv_phi_bounds_walk_bdd
import Submission.Work.Pert.Ksub2.sup_deriv_le_of_deep_or_shallow
import Submission.Work.Pert.Ksub2.deriv_phi_deep_upper_le
import Submission.Work.Pert.Ksub2.deriv_phi_strip_lower
import Submission.Work.Pert.Ksub2.walk_translate_deriv_le
import Submission.Work.Pert.Ksub2.walk_translate_mem_Dphi

/-!
# `Work.Pert.Ksub2.deriv_phi_bounds_walk_le`

The *quantitative*, supplied-constants form of `Work.Pert.Ksub2.deriv_phi_bounds_walk`: the caller
already owns a radius `ρe` whose balls around `K'` lie in `d.Dφ`, a bound `Tb ≥ 1` for `K'`, a deep
bound `C` (valid on `{|Im| ≤ Tb + ρe}` to the left of `Re = -R`) and a shallow bound `Cd` (valid on
the translates of `cthickening ρe K'` by `k ≤ ⌈R + Tb + ρe⌉₊`), together with the *membership*
statement `hZsub` for translates up to the (slightly larger) level `⌈Tb + max R (ξ₀+1) + ρe⌉₊`.

The conclusion is the two-sided bound along the walk `u, u+1, …, u+n = w`:

* `‖deriv φ₀‖ ≤ Ce₀` on the whole `ρe`-ball of every walk point, with the *explicit* constant
  `Ce₀ = max 1 (max C Cd)`;
* `cc₀ / M² ≤ ‖deriv φ₀‖` on the `ρe`-ball of the initial point `u ∈ Dstrip M (Tb+1)`.

The first clause is purely the deep/shallow alternative of
`Work.Pert.Ksub2.deriv_phi_le_of_deep_or_shallow`: a walk point is `w - m` with `m = n - i`, so it
either lies in one of the (finitely many) shallow translates of `cthickening ρe K'`, or it is so far
to the left that the whole `ρe`-ball is in `{Re < -ξ₀} ⊆ QLeft ξ₀ ⊆ Dφ`; in the latter case
`|Im| ≤ Tb + ρe` because a real translate does not change the imaginary part and `w ∈ K'` has
`‖w‖ ≤ Tb`.  Membership in `Dφ` in the intermediate range comes from `hZsub`.  The second clause is
`Work.Pert.Ksub2.deriv_phi_strip_lower` (`ρe ≤ 1/4`).
-/

namespace Work.Pert.Ksub2

open MandelDim Complex Set Metric

noncomputable section

/-- A point within `ρe` of a walk point `w - m` lies in `d.Dφ` (`walk_translate_mem_Dphi`),
re-exported at the exact argument order used below. -/
private lemma aux_walk_mem {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} {ρe Tb R : ℝ} {w : ℂ} (hw : w ∈ K') (hTb : ∀ w ∈ K', ‖w‖ ≤ Tb)
    (hZsub : ∀ k ∈ Finset.range (⌈Tb + max R (d.ξ₀ + 1) + ρe⌉₊ + 1),
        ∀ u ∈ (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K'), u ∈ d.Dφ)
    {m : ℕ} {z : ℂ} (hz : ‖z - (w - (m : ℂ))‖ ≤ ρe) : z ∈ d.Dφ :=
  walk_translate_mem_Dphi d hw hTb hZsub hz

/-- The deep/shallow derivative bound at a walk point: `‖deriv φ₀ z‖ ≤ max C Cd` for `z` within
`ρe` of `w - m`, `z ∈ d.Dφ`.  Direct from `deriv_phi_le_of_deep_or_shallow` with
`z₀ = z + m ∈ cthickening ρe K'`. -/
private lemma aux_walk_deriv {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} {ρe Tb R C Cd : ℝ} {w : ℂ} (hw : w ∈ K') (hρe : 0 ≤ ρe)
    (hTb : ∀ w ∈ K', ‖w‖ ≤ Tb)
    (hdeep : ∀ u : ℂ, u ∈ d.Dφ → R ≤ -u.re → |u.im| ≤ Tb + ρe → ‖deriv d.φ u‖ ≤ C)
    (hshallow : ∀ u ∈ (⋃ k ∈ Finset.range (⌈R + Tb + ρe⌉₊ + 1),
        (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K')), ‖deriv d.φ u‖ ≤ Cd)
    {m : ℕ} {z : ℂ} (hz : ‖z - (w - (m : ℂ))‖ ≤ ρe) (hzD : z ∈ d.Dφ) :
    ‖deriv d.φ z‖ ≤ max C Cd :=
  walk_translate_deriv_le d hw hρe hTb hdeep hshallow hz hzD

theorem deriv_phi_bounds_walk_le {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ)
    {ρe Tb R C Cd : ℝ}
    (hρe : 0 < ρe) (hρele : ρe ≤ 1 / 4)
    (hTb : ∀ w ∈ K', ‖w‖ ≤ Tb) (hTb1 : (1 : ℝ) ≤ Tb)
    (hballw : ∀ w ∈ K', Metric.ball w ρe ⊆ d.Dφ)
    (hdeep : ∀ u : ℂ, u ∈ d.Dφ → R ≤ -u.re → |u.im| ≤ Tb + ρe → ‖deriv d.φ u‖ ≤ C)
    (hshallow : ∀ u ∈ (⋃ k ∈ Finset.range (⌈R + Tb + ρe⌉₊ + 1),
        (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K')), ‖deriv d.φ u‖ ≤ Cd)
    (hZsub : ∀ k ∈ Finset.range (⌈Tb + max R (d.ξ₀ + 1) + ρe⌉₊ + 1),
        ∀ u ∈ (fun u : ℂ => u - (k : ℂ)) '' (Metric.cthickening ρe K'), u ∈ d.Dφ) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ Ce₀ cc₀ : ℝ, 0 < Ce₀ ∧ 0 < cc₀ ∧
      Ce₀ ≤ max 1 (max C Cd) ∧
      ∀ M : ℝ, M₀ ≤ M → ∀ w ∈ K', ∀ u ∈ Work.Pert.Dstrip M (Tb + 1), ∀ n : ℕ, u + (n : ℂ) = w →
        (∀ i : ℕ, i ≤ n → Metric.ball (u + (i : ℂ)) ρe ⊆ d.Dφ ∧
          ∀ z : ℂ, z ∈ d.Dφ → ‖z - (u + (i : ℂ))‖ ≤ ρe → ‖deriv d.φ z‖ ≤ Ce₀) ∧
        (∀ z : ℂ, z ∈ d.Dφ → ‖z - u‖ ≤ ρe → cc₀ / (M * M) ≤ ‖deriv d.φ z‖) := by
  -- the uniform lower bound on the deep strip (at the parameter `Tb + 1`)
  obtain ⟨M₁, c, hM₁pos, hcpos, hB⟩ := deriv_phi_strip_lower d (Tb + 1)
  -- the remaining hypotheses are part of the caller's contract; record them to keep them live
  have _ := hballw
  have _ := hTb1
  have _ := hK'c
  have _ := hK'
  refine ⟨M₁, hM₁pos, max 1 (max C Cd), c, lt_of_lt_of_le zero_lt_one (le_max_left _ _), hcpos,
    le_refl _, ?_⟩
  intro M hM w hw u hu n hn
  constructor
  · -- ## Clause 1: the walk points `u + i = w - (n - i)`
    intro i hi
    have hp : u + (i : ℂ) = w - ((n - i : ℕ) : ℂ) := by
      rw [Nat.cast_sub hi, ← hn]; ring
    rw [hp]
    have hmem : ∀ z : ℂ, ‖z - (w - ((n - i : ℕ) : ℂ))‖ ≤ ρe → z ∈ d.Dφ :=
      fun z hz => aux_walk_mem d hw hTb hZsub hz
    have hbd : ∀ z : ℂ, z ∈ d.Dφ → ‖z - (w - ((n - i : ℕ) : ℂ))‖ ≤ ρe →
        ‖deriv d.φ z‖ ≤ max C Cd :=
      fun z hzD hz => aux_walk_deriv d hw (le_of_lt hρe) hTb hdeep hshallow hz hzD
    constructor
    · intro z hz
      exact hmem z (by rw [← dist_eq_norm]; exact le_of_lt (Metric.mem_ball.mp hz))
    · intro z hzD hzd
      exact le_trans (hbd z hzD hzd) (le_max_right 1 (max C Cd))
  · -- ## Clause 2: the uniform lower bound on the deep strip
    intro z hzD hzd
    exact hB M hM u hu z hzD (le_trans hzd hρele)

end

end Work.Pert.Ksub2
