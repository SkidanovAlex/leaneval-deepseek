/-
# The level-indexed piece family of the lacunary walk, and its pad decomposition

`pieceFam ρ m₀ Lt f i k x` is the single-height increment of height `i+1` at the level `Lt k` of the
lacunary walk.  It is kept in this small module (importing only the two `V^r` bookkeeping lemmas) so
that both `A7Rescue/lowpassVarG.lean` and the delegated `A7Rescue/piecePadDecomp.lean` can use it
without an import cycle.

The main result here, `piecePadDecomp'`, is the head/tail decomposition of the variational norm of the
piece family at the cut `n₀` (the first level above the threshold), with the boundary correction
`3‖a n₀ − a (n₀−1)‖ₑ`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Rescue.variationalNorm_le_pad_add_shift
import Submission.Work.KMTAreas.A7Rescue.variationalNorm_pad_mono_change
import Submission.Work.KMTAreas.A7.LoHelpers

set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Rescue

/-- **The level-indexed piece family of the lacunary walk**: the single-height increment of height
`i+1` at the level `Lt k`.  A top-level `def` so that the elaborator never unfolds the `lpf` terms
(unfolding them inside a `variationalNorm` blows the heartbeat budget). -/
noncomputable def pieceFam (ρ : ℝ) (m₀ : ℕ) (Lt : ℕ → ℕ) (f : ℤ → ℂ) : ℕ → ℕ → ℤ → ℂ :=
  fun i k x => Work.KMTAreas.A7Hi.lpf ρ (i + 1) m₀ (Lt k) f x
    - Work.KMTAreas.A7Hi.lpf ρ i m₀ (Lt k) f x

/-- **The pad decomposition of the piece family.**  Splitting the variational norm of
`k ↦ pieceFam … i k x` at the cut `n₀` gives the clamped head `k ↦ pieceFam … i (min k (n₀−1)) x`,
the shifted tail `k ↦ pieceFam … i (n₀+k) x`, and the boundary correction
`3‖pieceFam … i n₀ x − pieceFam … i (n₀−1) x‖ₑ`. -/
theorem piecePadDecomp' (r : NNReal) (hr : 1 ≤ r) (ρ : ℝ) (m₀ n₀ : ℕ) (Lt : ℕ → ℕ) (f : ℤ → ℂ)
    (hn₀ : 1 ≤ n₀) (i : ℕ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r (fun k : ℕ => pieceFam ρ m₀ Lt f i k x)
      ≤ PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => pieceFam ρ m₀ Lt f i (min k (n₀ - 1)) x)
        + PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => pieceFam ρ m₀ Lt f i (n₀ + k) x)
        + 3 * ‖pieceFam ρ m₀ Lt f i n₀ x - pieceFam ρ m₀ Lt f i (n₀ - 1) x‖ₑ := by
  set a : ℕ → ℂ := fun k => pieceFam ρ m₀ Lt f i k x with ha
  have hsplit := variationalNorm_le_pad_add_shift (r := r) hr a n₀
  have hraise := variationalNorm_pad_mono_change (r := r) hr a (n₀ := n₀) hn₀
  calc PointwiseErgodicTheorems.variationalNorm r a
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun k => a (min k n₀))
          + PointwiseErgodicTheorems.variationalNorm r (fun k => a (n₀ + k)) := hsplit
    _ ≤ (PointwiseErgodicTheorems.variationalNorm r (fun k => a (min k (n₀ - 1)))
            + 3 * ‖a n₀ - a (n₀ - 1)‖ₑ)
          + PointwiseErgodicTheorems.variationalNorm r (fun k => a (n₀ + k)) :=
        add_le_add hraise le_rfl
    _ = PointwiseErgodicTheorems.variationalNorm r (fun k => a (min k (n₀ - 1)))
          + PointwiseErgodicTheorems.variationalNorm r (fun k => a (n₀ + k))
          + 3 * ‖a n₀ - a (n₀ - 1)‖ₑ := by ring
    _ = PointwiseErgodicTheorems.variationalNorm r
            (fun k : ℕ => pieceFam ρ m₀ Lt f i (min k (n₀ - 1)) x)
          + PointwiseErgodicTheorems.variationalNorm r
            (fun k : ℕ => pieceFam ρ m₀ Lt f i (n₀ + k) x)
          + 3 * ‖pieceFam ρ m₀ Lt f i n₀ x - pieceFam ρ m₀ Lt f i (n₀ - 1) x‖ₑ := by
        rw [ha]

end Work.KMTAreas.A7Rescue
