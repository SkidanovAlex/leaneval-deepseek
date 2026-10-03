import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.KMTAreas.A7.variationalNorm_le_sqSum

/-!
# The chain functional in "sum" form, and the reduction bricks for `chainPiece`

`chainPart r a` is *by definition* a supremum over monotone chains of the `ℓ^r`-norm of the jump
vector.  Its "sum form" (`chainPart_eq_iSup_sum`) rewrites that norm as the `r`-th root of the sum
of the `r`-th powers of the extended norms of the jumps — the form in which all the analytic work is
done.  We also record `chainPart_le_variationalNorm` (the trusted `𝕍^r = supPart + chainPart`).

**Caveat (see `NOTES_A7MixedG_chainPiece_SESSION.md`).**  The index shift in the definition is
`i + 1` for `i : Fin J`, i.e. the **cyclic** successor `(i.val + 1) % J` (`Fin.val_add`).  So the
jump vector is a *cycle* through `N 0, …, N (J-1)`, and in particular
`∑_{i : Fin J} (a (N (i+1)) − a (N i)) = 0` identically.  Any use of "the blocks telescope to
`a_{N(J)} − a_{N(0)}`" or of the `ℓ²`-orthogonality of disjointly supported block operators must
therefore be restricted to chains whose last cyclic jump vanishes (`N J = N (J-1)`), which the
supremum over `J` does contain.
-/

namespace Work.A7MixedG

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **The chain functional in sum form.**  For `2 ≤ r` and any scalar sequence `a : ℕ → ℂ`,
`chainPart r a = ⨆_{J,N} (∑_{i<J} ‖a (N (i+1)) − a (N i)‖^r)^{1/r}`. -/
theorem chainPart_eq_iSup_sum (r : NNReal) (hr : 2 ≤ r) (a : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r a
      = ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
          (∑ i : Fin J, ‖a (N (i + 1)) - a (N i)‖ₑ ^ ((r : ℝ))) ^ (1 / (r : ℝ)) := by
  rw [Work.KMTAreas.A7Hi.chainPart]
  refine iSup_congr fun J => iSup_congr fun N => iSup_congr fun hN => ?_
  rw [Work.KMTAreas.A7.ofReal_norm_toLp r hr J (fun i : Fin J => a (N (i + 1)) - a (N i))]

/-- The chain part is dominated by the variational norm (`𝕍^r = supPart + chainPart`). -/
theorem chainPart_le_variationalNorm (r : NNReal) (a : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r a ≤ PointwiseErgodicTheorems.variationalNorm r a := by
  rw [Work.KMTAreas.A7Hi.variationalNorm_eq_parts]
  exact le_add_of_nonneg_left zero_le

end Work.A7MixedG
