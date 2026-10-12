import ChallengeDeps
import Submission.Work.DLRepoint.d4Regime_mono
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.DLRepoint

set_option linter.unusedVariables false

/-- **The regime family from ONE maximal window count** — the bookkeeping that
makes FS `eq:appdellsassumption` a finite datum: the count-`n` regime fields at
EVERY window count `(n+1)/s³ ≤ 9μ` follow from the fields at the single maximal
count `⌊9μs³⌋ - 1` (transported down by `Work.DLRepoint.d4Regime_mono`), since a
window count is `≤ 9μs³` and so `≤ ⌊9μs³⌋` in `ℕ`.

This is what a consumer of `Submission.BoseGases.DLBoxData` uses to fill the
bundle's `hblk` field (`∀ n, ((n+1)/s³ ≤ 9μ) → D4Regime … n`) from one block
bundle: the DL re-point's "regime transport". -/
theorem d4Regime_family_of_max {s μ R0 K_B Ct c₀ cgap : ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hs : 0 < s) (hav : 0 ≤ BoseGases.a v) (hc0 : 0 < c₀)
    (hdil : 2 * c₀ * BoseGases.a v ≤ 1)
    (hfloor : 1 ≤ Nat.floor (9 * μ * s ^ 3))
    (reg : Work.DLRepoint.D4Regime s μ R0 K_B Ct c₀ cgap v
      (Nat.floor (9 * μ * s ^ 3) - 1)) :
    ∀ n : ℕ, ((((n + 1 : ℕ) : ℝ))) / s ^ 3 ≤ 9 * μ →
      Work.DLRepoint.D4Regime s μ R0 K_B Ct c₀ cgap v n := by
  intro n hwin
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  -- the window condition, cleared of the division by `s³ > 0`
  have hle : ((((n + 1 : ℕ) : ℝ))) ≤ 9 * μ * s ^ 3 := (div_le_iff₀ hs3).mp hwin
  -- a natural window count is `≤ ⌊9μs³⌋` ...
  have hnat : n + 1 ≤ Nat.floor (9 * μ * s ^ 3) := Nat.le_floor hle
  -- ... and so `≤ ⌊9μs³⌋ - 1`, where the regime is carried
  have hn : n ≤ Nat.floor (9 * μ * s ^ 3) - 1 := by omega
  exact d4Regime_mono hs hav hc0 hdil hn reg

end Work.DLRepoint
