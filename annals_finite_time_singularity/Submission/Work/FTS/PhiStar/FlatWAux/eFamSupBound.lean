import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Deleg.psiAngBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

/-!
# `Work.FTS.PhiStar.FlatWAux.eFamSupBound` — linear sup bound for the Gegenbauer family

The Dirichlet eigenfunctions of `Lzero` are
`eFam m θ = cos θ · gC (2m+1) (sin θ) = cos θ · C^{(3/2)}_{2m+1}(sin θ)`
(`Work.FTS.PhiStar.Gegenbauer.eFam`).  This file proves that they grow at most *linearly* in
the mode number, uniformly on `Iθ = [0, π/2]`:

`∃ C, 0 < C ∧ ∀ m θ ∈ Iθ, |eFam m θ| ≤ C · (2m+1)`   (here `C = 3`).

**Route.**  The sharp bound on the open interval is the Sturm–Liouville energy estimate
`Work.FTS.PhiStar.Series.Deleg.psiAngBounds`: with `u(x) = (1-x²)·gC (2m+1)(x)` one has
`u'' = -N·gC (2m+1)` for `N = (2m+2)(2m+3)`, whence `u(x)² ≤ N(1-x²)` on `[0,1]` and, after
`x = sin θ`,

  `|eFam m θ| ≤ √((2m+2)(2m+3))`   for `θ ∈ (0, π/2)`.

The two endpoints are trivial (`eFam m 0 = 0` because `gC (2m+1)` is odd, and
`eFam m (π/2) = 0` because `cos (π/2) = 0`), and `(2m+2)(2m+3) ≤ (3(2m+1))²` for `m ≥ 0`
completes the proof with `C = 3`.  Note `√((2m+2)(2m+3)) ~ 2m`, so the linear shape is sharp.
-/

/-- The energy bound of `Work.FTS.PhiStar.Series.Deleg.psiAngBounds`, first conjunct: on the
open interval `(0, π/2)` the family grows at most like `√((2m+2)(2m+3))`. -/
private lemma eFam_abs_le_sqrt_open (m : ℕ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) :=
  (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).1 m θ hθ

theorem eFamSupBound : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
    |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1) := by
  refine ⟨3, by norm_num, fun m θ hθ => ?_⟩
  rw [Work.Spaces.Iθ] at hθ
  obtain ⟨h0, h1⟩ := hθ
  have hkey : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ 3 * (2 * (m : ℝ) + 1) := by
    rcases eq_or_lt_of_le h0 with h | h
    · -- `θ = 0`: the odd Gegenbauer polynomial vanishes
      rw [← h, Work.FTS.PhiStar.Series.eFam_zero_right m, abs_zero]
      positivity
    rcases eq_or_lt_of_le h1 with h' | h'
    · -- `θ = π/2`: the `cos θ` factor vanishes
      rw [h', Work.FTS.PhiStar.Series.eFam_zero_left m, abs_zero]
      positivity
    -- on the open interval, the Sturm–Liouville energy bound
    refine le_trans (eFam_abs_le_sqrt_open m ⟨h, h'⟩) ?_
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hsq : (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3) ≤ (3 * (2 * (m : ℝ) + 1)) ^ 2 := by
      nlinarith [sq_nonneg (m : ℝ), hm]
    calc Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
        ≤ Real.sqrt ((3 * (2 * (m : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = 3 * (2 * (m : ℝ) + 1) := Real.sqrt_sq (by positivity)
  exact hkey

end Work.FTS.PhiStar.FlatWAux
