import Mathlib
import Submission.Work.EQ.bwdFanSheets
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.countable_zero_analytic_preconnected
import Submission.Work.EQ.isPreconnected_ball_diff_countable
import Submission.Work.EQ.bwdProd_eq_zero_iff
import Submission.Work.EQ.bwdP_fan_radicand_zero_ne

/-! # The degenerate locus of backward chains from a stable fan is countable

`Work.EQ.bwdP_fan_degenerate_countable`: for every stable word `ε` and length bound `j`, only
countably many small parameters `w` have some backward sign list `σ` of length at most `j` along
which the backward image of `fan a h ε w` lands on an isotropic line through `O₁`.

The product `bwdProd a h ε j` of all labelled radicands at levels `≤ j` is analytic off the lower
degenerate locus (`Work.EQ.analyticAt_bwdProd_of_good`, via the local analytic sheets of
`Work.EQ.bwdFanSheets`), so its zero set is discrete; an induction on the level shows that the
degenerate locus is countable. -/

namespace Work.EQ

open Filter _root_.Topology

noncomputable section

/-- **The degenerate locus up to level `n`**: the parameters `w` in the disc of radius `δ` for
which some label `σ` of length at most `n` has a vanishing radicand. -/
def degSet (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (δ : ℝ) (n : ℕ) : Set ℂ :=
  {w : ℂ | ‖w‖ < δ ∧ ∃ σ : List Bool, σ.length ≤ n ∧
    bsq (subO1 a (bwdP a σ (fan a h ε w))) = 0}

/-- **The degenerate locus of backward chains from a stable fan is countable.** For every
stable word `ε` and length bound `j`, only countably many small parameters `w` have some
backward sign list `σ` of length at most `j` along which the backward image of `fan ε w` lands
on an isotropic line through `O₁` (radicand `0`). This is the non-degeneracy input of the
junction step: limits of chain segments are genuine off this set. -/
theorem bwdP_fan_degenerate_countable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ (ε : List Bool) (j : ℕ),
      {w : ℂ | ‖w‖ < δ₂ ∧ ∃ σ : List Bool, σ.length ≤ j ∧
        bsq (subO1 a (bwdP a σ (fan a h ε w))) = 0}.Countable := by
  obtain ⟨Ke, Lam, Q, δf, hKe, hLam, hQ, hδf, hF⟩ := fan_induction ha0 ha1 hh
  refine ⟨δf, hδf, fun ε j => ?_⟩
  have hcount : ∀ n, (degSet a h ε δf n).Countable := by
    intro n
    induction n with
    | zero =>
        rw [show degSet a h ε δf 0 = ∅ from ?_]
        exact Set.countable_empty
        ext w
        simp only [degSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hw
        rintro ⟨σ, hσ, hz⟩
        have hσ0 : σ = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hσ)
        subst hσ0
        simp only [bwdP_nil] at hz
        have hpos := (hF ε w (by
          rw [Metric.mem_ball, dist_zero_right]; exact hw)).2.2.2.2
        have hconv : bsq (subO1 a (fan a h ε w)) =
            ((fan a h ε w).1 + (a / 2 : ℂ)) ^ 2 + (fan a h ε w).2 ^ 2 := by
          simp only [bsq, subO1]
          rw [Complex.ofReal_div]
          norm_num
        have hz' : ((fan a h ε w).1 + (a / 2 : ℂ)) ^ 2 + (fan a h ε w).2 ^ 2 = 0 := by
          rw [← hconv]; exact hz
        rw [hz'] at hpos
        simp at hpos
    | succ n ih =>
        have hnotin : (0 : ℂ) ∉ degSet a h ε δf n := by
          intro h0
          simp only [degSet, Set.mem_ofPred_eq] at h0
          obtain ⟨-, σ, -, hz⟩ := h0
          exact bwdP_fan_radicand_zero_ne ha0 ha1 hh ε σ hz
        have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) δf \ degSet a h ε δf n := by
          refine ⟨?_, hnotin⟩
          rw [Metric.mem_ball, dist_zero_right]
          simpa using hδf
        have h0ne : bwdProd a h ε (n + 1) 0 ≠ 0 := by
          intro hzero
          rw [bwdProd_eq_zero_iff] at hzero
          obtain ⟨σ, -, hz⟩ := hzero
          exact bwdP_fan_radicand_zero_ne ha0 ha1 hh ε σ hz
        have hpre : IsPreconnected (Metric.ball (0 : ℂ) δf \ degSet a h ε δf n) :=
          isPreconnected_ball_diff_countable hδf ih
        have hAn : AnalyticOnNhd ℂ (bwdProd a h ε (n + 1))
            (Metric.ball (0 : ℂ) δf \ degSet a h ε δf n) := by
          intro w₀ hw
          obtain ⟨hwball, hwdeg⟩ := hw
          rw [Metric.mem_ball, dist_zero_right] at hwball
          refine analyticAt_bwdProd_of_good (hfan := fun τ => (hF τ w₀ ?_).1) ?_
          · rw [Metric.mem_ball, dist_zero_right]; exact hwball
          · intro σ hσ hzero
            exact hwdeg (by
              simp only [degSet, Set.mem_ofPred_eq]
              exact ⟨hwball, σ, hσ, hzero⟩)
        have hcnt := countable_zero_analytic_preconnected hpre hAn h0mem h0ne
        have hset : degSet a h ε δf (n + 1) = degSet a h ε δf n ∪
            {z ∈ Metric.ball (0 : ℂ) δf \ degSet a h ε δf n |
              bwdProd a h ε (n + 1) z = 0} := by
          ext w
          simp only [degSet, Set.mem_ofPred_eq, Set.mem_union, Set.mem_sdiff, Metric.mem_ball,
            dist_zero_right]
          constructor
          · rintro ⟨hw, hmem⟩
            by_cases hcase : ∃ σ : List Bool, σ.length ≤ n ∧
                bsq (subO1 a (bwdP a σ (fan a h ε w))) = 0
            · exact Or.inl ⟨hw, hcase⟩
            · exact Or.inr ⟨⟨hw, fun h => hcase h.2⟩, by
                rw [bwdProd_eq_zero_iff]; exact hmem⟩
          · rintro (⟨hw, hmem⟩ | ⟨⟨hwball, hwdeg⟩, hprod⟩)
            · obtain ⟨σ, hσ, hz⟩ := hmem
              exact ⟨hw, σ, Nat.le_trans hσ (Nat.le_succ n), hz⟩
            · refine ⟨hwball, ?_⟩
              rw [bwdProd_eq_zero_iff] at hprod
              exact hprod
        rw [hset]
        exact ih.union hcnt
  simpa [degSet] using hcount j

end

end Work.EQ
