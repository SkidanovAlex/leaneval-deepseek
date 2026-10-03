import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Exist.fatouCoordW_abel
import Submission.Work.FatouCoord.Exist.fatouCoordW_tsum_bound
import Submission.Work.Parab.leftCoord.wMap_large_estimates
import Submission.Work.Parab.leftCoord.coordError_sector
import Submission.Work.Parab.leftCoord.escC
import Submission.Work.Parab.leftCoord.levelData
import Submission.Work.Parab.leftCoord.exists_levelFacts
import Submission.Work.Parab.leftCoord.psiC_asymptotic

/-!
# The Fatou coordinate of the ends of the left chart is asymptotically exact

Shishikura's appendix A.3 (the "ends" of the left coordinate, cf. `Work.Parab.LeftCoordData`)
needs the Fatou coordinate `ψ = fatouCoordW f (1 - a)` of the chart dynamics
`wMap f w = -1 / f (-1/w)` to satisfy, along an orbit `wMap ^[k] x` which stays outside a disc
of radius `|Im x| / 4` and enters the far right half-plane at time `n`,

`ψ (wMap ^[n] x) = n + x - (1 - a) log x + o(1)`  as `|Im x| → ∞`,

uniformly in the index `n`.  Note that the right hand side is *independent of* `n`: the defect
`ψ (wMap ^[n] x) - n - x + (1 - a) log x` telescopes to the sum of the defects
`coordError f (1 - a) (wMap ^[k] x)` along the whole infinite orbit of `x`, so the statement is
really the assertion that this total defect is `o(1)`.

The proof splits the total defect at the first index `J` at which the orbit crosses a level `M`
chosen from `ε`:

* `ψ (wMap ^[n] x) - n = PsiC N (wMap f) ψ x` (`psiC_iterate_ge`), because the real parts stay
  `> N` from the crossing index on, so the iterated Abel equation is available;
* the telescoping identity `PsiC_sub_approx_eq_sum` rewrites
  `PsiC x - approxCoord (1 - a) x` as the sum of the defects up to `J` plus the remainder at
  `wMap ^[J] x`;
* the remainder is `O(1 / Re (wMap ^[J] x)) ≤ O(1/M) < ε/2` (`LevelFacts.rem`), while the finite
  sum is `O((M + ‖x‖) / ‖x‖ ^ 2) < ε/2` because the orbit stays at distance `≥ ‖x‖ / 8` from the
  origin up to step `J`, using the sector estimate `coordError_sector` for the defects — the
  direction of the orbit is controlled by the drift estimate `|Im (wMap ^[k] x) - Im x| ≤ ‖x‖/8`.

That whole analysis is `psiC_asymptotic` (`Work.Parab.leftCoord`), which gives
`PsiC W = W - (1 - a) log W + o(1)` on the sector `-3 |Im W| < Re W` for `W ∈ EscC`; here we only
have to produce the level data (`exists_levelFacts`), the sector form of the defect estimate, and
to convert the conclusion back from `PsiC` to `fatouCoordW`.
-/

namespace Work.Parab.leftCoordData

theorem psi_approx_of_ends {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧ ∀ ε > 0, ∃ R R' : ℝ, ∀ x : ℂ,
      R < |x.im| → -3 * |x.im| < x.re → ∀ n : ℕ,
      (∀ k ≤ n, |x.im| / 4 ≤ ‖(Work.FatouCoord.wMap f)^[k] x‖) →
      N < ((Work.FatouCoord.wMap f)^[n] x).re →
      R' < ((Work.FatouCoord.wMap f)^[n] x).re →
      ‖Work.FatouCoord.fatouCoordW f (1 - a) ((Work.FatouCoord.wMap f)^[n] x) - (n : ℂ)
        - (x - (1 - a) * Complex.log x)‖ < ε := by
  -- the sector form of the defect estimate, and the level data of the Fatou coordinate theory
  obtain ⟨Rcs, Ccs, hRcspos, hRcsr, hCcsnn, hcs_re, hcs_impos, hcs_imneg⟩ :=
    Work.Parab.leftCoord.coordError_sector hb
  obtain ⟨NL, hLevelsL⟩ := Work.Parab.leftCoord.exists_levelFacts hb
  -- one level dominating both the level data and the sector threshold of the defects
  set N : ℝ := max NL (max Rcs 4 + 1) with hNdef
  have hNLN : NL ≤ N := le_max_left _ _
  have hLevels : Work.Parab.leftCoord.LevelFacts f h a r N := hLevelsL.mono hNLN
  have hRcsN : Rcs < N := by
    have h1 : Rcs ≤ max Rcs 4 := le_max_left _ _
    have h2 : max Rcs 4 < max Rcs 4 + 1 := by linarith
    have h3 : max Rcs 4 + 1 ≤ N := le_max_right _ _
    linarith
  -- at that level the defect is `O(1/‖w‖²)` on the three sectors
  have herror : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, N < ‖w‖ →
      (0 < w.re ∨ (0 < w.im ∧ 0 < (Work.FatouCoord.wMap f w).im) ∨
        (w.im < 0 ∧ (Work.FatouCoord.wMap f w).im < 0)) →
      ‖Work.FatouCoord.coordError f (1 - a) w‖ ≤ C / ‖w‖ ^ 2 := by
    refine ⟨Ccs, hCcsnn, fun w hw hsec => ?_⟩
    have hRw : Rcs < ‖w‖ := lt_trans hRcsN hw
    rcases hsec with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hcs_re w hRw h
    · exact hcs_impos w hRw h1 h2
    · exact hcs_imneg w hRw h1 h2
  -- the one-step estimates of the level data
  obtain ⟨K, hKnn, hstep⟩ := hLevels.step
  have hmono : ∀ y : ℂ, N < ‖y‖ → y.re ≤ (Work.FatouCoord.wMap f y).re :=
    fun y hy => by linarith [(hstep y hy).2.2.2]
  have hGN : ∀ y : ℂ, N < y.re → N < (Work.FatouCoord.wMap f y).re := by
    intro y hy
    have hy' : N < ‖y‖ := lt_of_lt_of_le hy (Complex.re_le_norm y)
    have h := (hstep y hy').2.2.2
    linarith
  have habelN : ∀ y : ℂ, N < y.re →
      Work.FatouCoord.fatouCoordW f (1 - a) (Work.FatouCoord.wMap f y)
        = Work.FatouCoord.fatouCoordW f (1 - a) y + 1 :=
    fun y hy => hLevels.abel y hy
  refine ⟨N, hLevels.pos, hLevels.hr, ?_⟩
  intro ε hε
  -- the asymptotic of the closed extension on the sector
  obtain ⟨R, hR⟩ := Work.Parab.leftCoord.psiC_asymptotic hb hLevels herror ε hε
  refine ⟨max R (4 * N), N, ?_⟩
  intro x hxim hsect n hnorm hNn hR'
  have hRlt : R < |x.im| := lt_of_le_of_lt (le_max_left _ _) hxim
  have h4Nlt : 4 * N < |x.im| := lt_of_le_of_lt (le_max_right _ _) hxim
  have hNim : N < |x.im| / 4 := by linarith
  have hxnorm : R < ‖x‖ := lt_of_lt_of_le hRlt (Complex.abs_im_le_norm x)
  -- `x` lies in the closed escaping set, with entry index at most `n`
  have hxesc : x ∈ Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap f) :=
    ⟨n, fun k hk => lt_of_lt_of_le hNim (hnorm k hk), hNn⟩
  have hPsic := hR x hxesc hxnorm hsect
  have hnIdx : Work.Parab.leftCoord.nIdxC N (Work.FatouCoord.wMap f) x ≤ n := by
    by_contra hcon
    push Not at hcon
    have hle := Work.Parab.leftCoord.re_le_of_lt_nIdxC hxesc hcon
    exact absurd hNn (not_lt.mpr hle)
  -- the iterated Abel equation turns `fatouCoordW` at `wMap ^[n] x` into `PsiC x + n`
  have hiter := Work.Parab.leftCoord.psiC_iterate_ge (N := N) (G := Work.FatouCoord.wMap f)
      (ψ := Work.FatouCoord.fatouCoordW f (1 - a)) hGN habelN hmono hxesc hnIdx
  have hgoal : Work.FatouCoord.fatouCoordW f (1 - a) ((Work.FatouCoord.wMap f)^[n] x)
        - (n : ℂ) - (x - (1 - a) * Complex.log x)
      = Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap f)
          (Work.FatouCoord.fatouCoordW f (1 - a)) x
        - (x - (1 - a) * Complex.log x) := by
    rw [hiter]; ring
  rw [hgoal]
  exact hPsic

end Work.Parab.leftCoordData
