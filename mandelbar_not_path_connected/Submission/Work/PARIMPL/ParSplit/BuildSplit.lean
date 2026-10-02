/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.ParSplit.BuildSplit` — the split datum from its two symmetric halves

By `Work.PARIMPL.ParSplit.Split`, the input of everything downstream (`ParSplit.phase_of_split`,
the germ, the assembly of `ParNormal`) is the structure `SplitData d`: a ball `ball c₀ ρ`, a disc
`ball z₁ R`, continuous `m E` with `m c₀ = z₁`, `E c₀ = 0`, `m ± E/2` the two fixed points of
`Work.EL.F c`, and *uniqueness* — these two are the only fixed points of `Work.EL.F c` in the
disc.

This module splits that datum into two halves which are proved (or delegated) separately, and
neither of which mentions the *continuity of a chosen square root*:

* **(H1) the two symmetric halves.**  `ParSplit.splitPair_exists`: there are `ρ, R > 0` and
  continuous `m G : ℂ → ℂ` with `m c₀ = z₁`, `G c₀ = 0` and, for every `c` in the ball,

    `∀ z ∈ ball z₁ R, F c z = z ↔ (z - m c)² = G c`.

  Here `m c` is the *midpoint* of the split pair and `G c = Δ c²` the square of the
  *half-difference*: both are symmetric functions of the two roots, hence single-valued, and in
  fact real analytic on the ball — no monodromy is involved.

* **(H2) a continuous square root of `G`.**  `ParSplit.exists_continuous_sqrt_of_char`: there are
  `ρ' ≤ ρ` and `Δ : ℂ → ℂ` continuous on `ball c₀ ρ'` with `Δ c² = G c`.  This is the only place
  where the *real analyticity* of the parameter dependence is used: `G` vanishes exactly on the
  collision locus `Z = {c : the two split fixed points coincide}`, and in the tricorn `Z` is a
  real curve through `c₀` (the parabolic arc), so that a continuous square root exists; for a
  holomorphic family, where `Z` is an isolated point, none does.  See `ParSplit.NOTES.md` and
  `ParSplit.Sqrt` (`exists_continuousOn_sq_eq_mul_of_real`), where an explicit real "wall
  function" `A` with `G = A·h`, `h` nowhere zero, is turned into `Δ`.

`SplitData d` then follows by pure glue, given in this module.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.Split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-- **The split pair is small.**  Continuity of the midpoint `m` (`m c₀ = z₁`) and of the
half-difference `Δ` (`Δ c₀ = 0`) forces both split points `m c ± Δ c` into the disc
`ball z₁ R` for `c` close to `c₀`. -/
theorem exists_small_ball_of_continuous {z₁ c₀ : ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R)
    {m Δ : ℂ → ℂ} (hm : ContinuousOn m (ball c₀ ρ)) (hΔ : ContinuousOn Δ (ball c₀ ρ))
    (hm₀ : m c₀ = z₁) (hΔ₀ : Δ c₀ = 0) :
    ∃ ρ' > 0, ρ' ≤ ρ ∧ ∀ c ∈ ball c₀ ρ',
      dist (m c) z₁ + ‖Δ c‖ < R := by
  have hc0 : c₀ ∈ ball c₀ ρ := mem_ball_self hρ
  have hmc : ContinuousAt m c₀ := hm.continuousAt (isOpen_ball.mem_nhds hc0)
  have hΔc : ContinuousAt Δ c₀ := hΔ.continuousAt (isOpen_ball.mem_nhds hc0)
  have hcont : ContinuousAt (fun c => dist (m c) z₁ + ‖Δ c‖) c₀ :=
    (hmc.dist continuousAt_const).add hΔc.norm
  have h0 : dist (m c₀) z₁ + ‖Δ c₀‖ = 0 := by
    rw [hm₀, hΔ₀, dist_self, norm_zero, add_zero]
  have hlt : {x : ℝ | x < R} ∈ 𝓝 (dist (m c₀) z₁ + ‖Δ c₀‖) :=
    (isOpen_lt continuous_id continuous_const).mem_nhds (by rw [h0]; exact hR)
  have hmem : {c : ℂ | dist (m c) z₁ + ‖Δ c‖ < R} ∈ 𝓝 c₀ := hcont hlt
  obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨min ε ρ, lt_min hε hρ, min_le_right _ _, fun c hc => ?_⟩
  rw [mem_ball, dist_eq_norm] at hc
  exact hεb (by rw [mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hc (min_le_left _ _))

/-- **The split datum from its two symmetric halves and a continuous square root.** -/
theorem nonempty_splitData_of_char {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R) {m G : ℂ → ℂ}
    (hm : ContinuousOn m (ball c₀ ρ)) (hG : ContinuousOn G (ball c₀ ρ))
    (hm₀ : m c₀ = d.z₁) (hG₀ : G c₀ = 0) {Δ : ℂ → ℂ} (hΔ : ContinuousOn Δ (ball c₀ ρ))
    (hΔsq : ∀ c ∈ ball c₀ ρ, Δ c ^ 2 = G c)
    (hchar : ∀ c ∈ ball c₀ ρ, ∀ z ∈ ball d.z₁ R, (Work.EL.F c z = z ↔ (z - m c) ^ 2 = G c))
    {ρ' : ℝ} (hρ' : 0 < ρ') (hρ'ρ : ρ' ≤ ρ)
    (hsmall : ∀ c ∈ ball c₀ ρ', dist (m c) d.z₁ + ‖Δ c‖ < R) :
    Nonempty (SplitData d) := by
  have hsub : ball c₀ ρ' ⊆ ball c₀ ρ := ball_subset_ball hρ'ρ
  have hΔ₀ : Δ c₀ = 0 := by
    have h1 : Δ c₀ ^ 2 = 0 := by rw [hΔsq c₀ (mem_ball_self hρ), hG₀]
    exact sq_eq_zero_iff.mp h1
  have hE₀ : (fun c => 2 * Δ c) c₀ = 0 := by
    show 2 * Δ c₀ = 0
    rw [hΔ₀, mul_zero]
  refine ⟨{ ρ := ρ', hρ := hρ', R := R, hR := hR, m := m, E := fun c => 2 * Δ c, cont_m := hm.mono hsub, cont_E := continuousOn_const.mul (hΔ.mono hsub), m₀ := hm₀, E₀ := hE₀, fixed_add := ?_, fixed_sub := ?_, unique := ?_ }⟩
  · intro c hc
    have hcρ : c ∈ ball c₀ ρ := hsub hc
    have hz : m c + 2 * Δ c / 2 ∈ ball d.z₁ R := by
      rw [mem_ball]
      calc dist (m c + 2 * Δ c / 2) d.z₁
          = dist (m c + Δ c) d.z₁ := by ring_nf
        _ ≤ dist (m c + Δ c) (m c) + dist (m c) d.z₁ := dist_triangle _ _ _
        _ = ‖Δ c‖ + dist (m c) d.z₁ := by rw [dist_eq_norm]; ring_nf
        _ < R := by linarith [hsmall c hc]
    have hsq : (m c + 2 * Δ c / 2 - m c) ^ 2 = G c := by
      have h1 : m c + 2 * Δ c / 2 - m c = Δ c := by ring
      rw [h1, hΔsq c hcρ]
    have := (hchar c hcρ _ hz).mpr hsq
    simpa using this
  · intro c hc
    have hcρ : c ∈ ball c₀ ρ := hsub hc
    have hz : m c - 2 * Δ c / 2 ∈ ball d.z₁ R := by
      rw [mem_ball]
      calc dist (m c - 2 * Δ c / 2) d.z₁
          = dist (m c - Δ c) d.z₁ := by ring_nf
        _ ≤ dist (m c - Δ c) (m c) + dist (m c) d.z₁ := dist_triangle _ _ _
        _ = ‖Δ c‖ + dist (m c) d.z₁ := by
            rw [dist_eq_norm, dist_eq_norm]
            congr 1
            rw [show (m c - Δ c) - m c = -Δ c by ring, norm_neg]
        _ < R := by linarith [hsmall c hc]
    have hsq : (m c - 2 * Δ c / 2 - m c) ^ 2 = G c := by
      have h1 : m c - 2 * Δ c / 2 - m c = -Δ c := by ring
      rw [h1, neg_sq, hΔsq c hcρ]
    have := (hchar c hcρ _ hz).mpr hsq
    simpa using this
  · intro c hc z hz
    have hcρ : c ∈ ball c₀ ρ := hsub hc
    constructor
    · intro hfix
      have h1 : (z - m c) ^ 2 = G c := (hchar c hcρ z hz).mp hfix
      have h2 : (z - m c) ^ 2 = Δ c ^ 2 := by rw [h1, ← hΔsq c hcρ]
      have h3 : z - m c = Δ c ∨ z - m c = -Δ c := sq_eq_sq_iff_eq_or_eq_neg.mp h2
      rcases h3 with h3 | h3
      · left
        have : z = m c + Δ c := by linear_combination h3
        rw [this]; ring
      · right
        have : z = m c - Δ c := by linear_combination h3
        rw [this]; ring
    · intro hpair
      have hsq : (z - m c) ^ 2 = G c := by
        rcases hpair with h | h
        · have h1 : (z - m c) ^ 2 = Δ c ^ 2 := by rw [h]; ring_nf
          rw [h1, hΔsq c hcρ]
        · have h1 : (z - m c) ^ 2 = Δ c ^ 2 := by rw [h]; ring_nf
          rw [h1, hΔsq c hcρ]
      exact (hchar c hcρ z hz).mpr hsq

namespace SplitData

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d)

/-- **The midpoint is a fixed point exactly on the collision locus.**  On a disc in which the two
split points are the only fixed points (`S.unique`) and are close enough to the centre that
`m c ± E c/2` and `m c` all lie in it, `S.m c` being fixed forces `S.E c = 0`.  This is the fact
`D c = 0 ↔ c ∈ Z` of `ParSplit.NOTES.md` §5, used to see that `|D c|/√|G c|` is a legitimate
rescaling factor. -/
theorem E_eq_zero_of_fixed_mid {c : ℂ} (hc : c ∈ Metric.ball c₀ S.ρ)
    (hsmall : dist (S.m c) d.z₁ + ‖S.E c‖ / 2 < S.R)
    (hfix : Work.EL.F c (S.m c) = S.m c) : S.E c = 0 := by
  have hmem : S.m c ∈ Metric.ball d.z₁ S.R := by
    rw [Metric.mem_ball]
    have h1 : dist (S.m c) d.z₁ ≤ dist (S.m c) d.z₁ + ‖S.E c‖ / 2 := by
      have := norm_nonneg (S.E c); linarith
    linarith [h1, hsmall]
  have hmid := (S.unique c hc (S.m c) hmem).mp hfix
  have h3 : S.E c / 2 = 0 := by
    rcases hmid with h | h
    · exact add_eq_left.mp h.symm
    · exact sub_eq_self.mp h.symm
  exact (div_eq_zero_iff.mp h3).resolve_right (by norm_num)

end SplitData


end Work.PARIMPL.ParSplit
