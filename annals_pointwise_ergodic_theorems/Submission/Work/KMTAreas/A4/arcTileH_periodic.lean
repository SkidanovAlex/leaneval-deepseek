/-
# `1`-periodicity of the arc periodization `arcTileH`

`arcTileH u = Σ_m arcBump0 (u - m)` is the periodization of the rescaled bump `arcBump0`; since
the summation index runs over all of `ℤ`, shifting `u` by an integer `k` only permutes the index
(`m ↦ m + k`), so `arcTileH` is `1`-periodic:

`arcTileH (u - k) = arcTileH u` for every `u : ℝ`, `k : ℤ`.

The only ingredient is the reindexing of an infinite sum over `ℤ` by the equivalence
`Equiv.addRight k : ℤ ≃ ℤ`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.arcBumpBasic

namespace Work.KMTAreas.A4

theorem arcTileH_periodic (u : ℝ) (k : ℤ) : Work.KMTAreas.A4.arcTileH (u - (k : ℝ)) = Work.KMTAreas.A4.arcTileH u := by
  unfold arcTileH
  -- shift the summation index: `u - k - m = u - (m + k)`
  simp only [show ∀ m : ℤ,
      arcBump0 (u - (k : ℝ) - (m : ℝ)) = arcBump0 (u - ((m + k : ℤ) : ℝ)) from
    fun m => by congr 1; push_cast; ring]
  -- and reindex the `ℤ`-sum along `m ↦ m + k`
  exact (Equiv.addRight k).tsum_eq (fun m : ℤ => arcBump0 (u - (m : ℝ)))

end Work.KMTAreas.A4
