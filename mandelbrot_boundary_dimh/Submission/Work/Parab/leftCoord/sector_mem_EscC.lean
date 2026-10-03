import Mathlib
import Submission.Work.Parab.leftCoord.levelData
import Submission.Work.Parab.leftCoordData.orbit_ends_control

/-!
# The far left sector lies in the closed escaping set `EscC`

We prove that for a parabolic germ `f z = z + z ^ 2 h z` (`ParabolicBounds f h a r A A'`) there is
a level `η₀ > 0` such that every point `x` of the *far left wedge*
`{η₀ < |Im x|, Re x > -3 |Im x|}` belongs to the closed escaping set
`EscC N (wMap f)` of the chart dynamics, for every level `N` at which the estimates of
`LevelFacts f h a r N` hold.

The point is that the wedge is invariant in the relevant sense: the chart dynamics moves real
parts to the right by at least `1/2` per step while the imaginary part drifts by a bounded amount,
so that an orbit starting deep in the wedge reaches the level `Re = N` while staying far away
from the origin.  This is exactly the content of the (independently proved) estimate
`Work.Parab.leftCoordData.orbit_ends_control`, from which the statement follows by enlarging the
threshold so as to dominate `4 N` as well.
-/

namespace Work.Parab.leftCoord

open Work.FatouCoord

theorem sector_mem_EscC {f h : ℂ → ℂ} {a : ℂ} {r A A' N : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A')
    (hF : Work.Parab.leftCoord.LevelFacts f h a r N) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ x : ℂ, η₀ < |x.im| → -3 * |x.im| < x.re →
      Work.Parab.leftCoord.EscC N (Work.FatouCoord.wMap f) x := by
  obtain ⟨M, C, hMpos, _hCnn, hctrl⟩ :=
    Work.Parab.leftCoordData.orbit_ends_control hb hF.pos
  refine ⟨max M (4 * N + 1), lt_of_lt_of_le hMpos (le_max_left _ _), ?_⟩
  intro x him hre
  have hMlt : M < |x.im| := lt_of_le_of_lt (le_max_left _ _) him
  have h4Nlt : 4 * N + 1 < |x.im| := lt_of_le_of_lt (le_max_right _ _) him
  have him4 : N < |x.im| / 4 := by linarith
  obtain ⟨n, hnP, _hnmin, hnorm, _hnim, _hsum⟩ := hctrl x hMlt hre
  exact ⟨n, fun k hk => lt_of_lt_of_le him4 (hnorm k hk), hnP⟩

end Work.Parab.leftCoord
