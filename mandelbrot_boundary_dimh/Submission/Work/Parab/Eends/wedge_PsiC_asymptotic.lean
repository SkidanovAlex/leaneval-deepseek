import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.leftCoord.escC
import Submission.Work.Parab.leftCoord.levelData
import Submission.Work.Parab.leftCoord.exists_levelFacts
import Submission.Work.Parab.leftCoord.psiC_asymptotic
import Submission.Work.Parab.leftCoord.coordError_sector
import Submission.Work.Parab.leftCoord.sector_mem_EscC
import Submission.Work.Parab.leftCoordData.orbit_ends_control

namespace Work.Parab.Eends

/-- **The end asymptotic of the (closed extension of the) Fatou coordinate in the chart.**

`wMap f w = -1 / f (-1/w)` is the chart dynamics of a parabolic germ `f z = z + z^2 h z`
(`ParabolicBounds f h a r A A'`), and `ψ = fatouCoordW f (1 - a)` is its Fatou coordinate, with
`ψ w = w - (1-a) log w + o(1)` as `Re w → +∞`.  `PsiC N G ψ` is the closed extension
`ψ (G^n w) - n` (`Work.Parab.leftCoord.escC`) with `n` the first index at which `Re > N`.

The claim is that the asymptotic holds on the *whole wedge* `-3|Im w| < Re w` as `|Im w| → ∞`,
uniformly in `Re w`.

Proof route: `Work.Parab.leftCoordData.orbit_ends_control` (with level `N`) keeps the orbit at
distance `≥ |Im w|/4` from the origin while its real part crosses the level `N`, which gives
`w ∈ EscC N (wMap f)` (see also `Work.Parab.leftCoord.sector_mem_EscC`) together with the
summability of the defects; then apply `Work.Parab.leftCoord.psiC_asymptotic` with `LevelFacts`
from `Work.Parab.leftCoord.exists_levelFacts` and the sector defect bound from
`Work.Parab.leftCoord.coordError_sector`. -/
theorem wedge_PsiC_asymptotic {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ N₀ : ℝ, 0 < N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ ε > 0, ∃ T : ℝ, ∀ x : ℂ, T < |x.im| → -3 * |x.im| < x.re →
        ‖Work.Parab.leftCoord.PsiC N (Work.FatouCoord.wMap f)
          (Work.FatouCoord.fatouCoordW f (1 - a)) x - (x - (1 - a) * Complex.log x)‖ < ε := by
  -- the level at which all the analytic estimates are available
  obtain ⟨N₁, hF₁⟩ := Work.Parab.leftCoord.exists_levelFacts hb
  -- the sector bound for the defect
  obtain ⟨R, C, hRpos, _hRr, hCnn, hC1, hC2, hC3⟩ := Work.Parab.leftCoord.coordError_sector hb
  refine ⟨max N₁ R, lt_of_lt_of_le hF₁.pos (le_max_left _ _), ?_⟩
  intro N hN ε hε
  have hN₁N : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hRN : R ≤ N := le_trans (le_max_right _ _) hN
  -- the level facts at the prescribed level
  have hF : Work.Parab.leftCoord.LevelFacts f h a r N := hF₁.mono hN₁N
  -- the defect hypothesis of `psiC_asymptotic`, assembled from the three sector estimates
  have herr : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, N < ‖w‖ →
      (0 < w.re ∨ (0 < w.im ∧ 0 < (Work.FatouCoord.wMap f w).im) ∨
        (w.im < 0 ∧ (Work.FatouCoord.wMap f w).im < 0)) →
      ‖Work.FatouCoord.coordError f (1 - a) w‖ ≤ C / ‖w‖ ^ 2 := by
    refine ⟨C, hCnn, ?_⟩
    intro w hw hsec
    have hRw : R < ‖w‖ := lt_of_le_of_lt hRN hw
    rcases hsec with hre | ⟨him, him'⟩ | ⟨him, him'⟩
    · exact hC1 w hRw hre
    · exact hC2 w hRw him him'
    · exact hC3 w hRw him him'
  -- the asymptotic on the (closed) escaping set
  obtain ⟨R', hR'⟩ :=
    Work.Parab.leftCoord.psiC_asymptotic hb hF herr ε hε
  -- the far wedge lies in the closed escaping set
  obtain ⟨η₀, _hη₀pos, hη₀⟩ := Work.Parab.leftCoord.sector_mem_EscC hb hF
  refine ⟨max R' η₀, ?_⟩
  intro x hxim hsect
  have hR'x : R' < ‖x‖ := by
    have h1 : max R' η₀ < |x.im| := hxim
    have h2 : |x.im| ≤ ‖x‖ := Complex.abs_im_le_norm x
    linarith [le_max_left R' η₀]
  have hηx : η₀ < |x.im| := lt_of_le_of_lt (le_max_right R' η₀) hxim
  have hmem : x ∈ Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap f) := hη₀ x hηx hsect
  simpa only [Work.FatouCoord.approxCoord_apply] using hR' x hmem hR'x hsect

end Work.Parab.Eends
