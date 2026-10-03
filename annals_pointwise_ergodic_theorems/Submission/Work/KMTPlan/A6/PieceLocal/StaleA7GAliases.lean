/-
# Restoration of two `Work.KMTAreas.A7G` names used by the packet estimates

The packet estimates `SliceFBound` / `SliceGBound` (the two `(2,2,1)` linear lacunary variational
inputs of the model piece) were written against an earlier state of the `A7G`/`A7Hi` API, in which
`Work.KMTAreas.A7G` carried

* `partMaxD` (the partial-sum maximal function of the annuli of the low-pass walk) — now
  `Work.KMTAreas.A7HiRep.partMaxD` (same formula as `Work.KMTAreas.A7Hi.partSumSup`),
* `supPart_le_first_add_partMaxD` (the telescoping `supPart ≤ ‖T₀‖ + partMaxD`) — now
  `Work.KMTAreas.A7Hi.supPart_le_norm_zero_add_partSumSup`,
* `partMaxD_le_chainPart` (`partMaxD ≤ chainPart 3`, the two-point chain `0 → K`) — now inlined as
  `Work.KMTAreas.A7Hi2.partMaxD_le_chainPart`.

That refactor left `Submission/Work/KMTPlan/A6/PieceBoundedH/sliceFBound.lean` un-compilable
(unknown identifiers) and hence the whole model side unimportable.  This module restores the three
names *at their old signature* (in namespace `Work.KMTAreas.A7G`, as a local copy: the declarations
are new, and clash with nothing currently in the tree), so that a local copy of the packet estimate
compiles unchanged.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassMaximal

namespace Work.KMTAreas.A7G

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- The partial-sum maximal function of the annuli `Δ_k = T_{k+1} − T_k` of the low-pass
Ionescu--Wainger family, in the old `A7G` vocabulary (`= Work.KMTAreas.A7HiRep.partMaxD`
`= Work.KMTAreas.A7Hi.partSumSup`). -/
noncomputable def partMaxD (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) : ℤ → ℝ≥0∞ :=
  Work.KMTAreas.A7HiRep.partMaxD ρ l₁ m₀ f

/-- **The values supremum is dominated by the first value plus the partial-sum maximal
function** (the telescoping `T_K = T_0 + ∑_{i<K}(T_{i+1} − T_i)`), in the old `A7G` signature. -/
lemma supPart_le_first_add_partMaxD (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) (r : NNReal) :
    Work.KMTAreas.A7Hi.supPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 f x‖ₑ + partMaxD ρ l₁ m₀ f x := by
  simpa only [partMaxD, Work.KMTAreas.A7Hi.partSumSup, Work.KMTAreas.A7HiRep.partMaxD] using
    Work.KMTAreas.A7Hi.supPart_le_norm_zero_add_partSumSup r ρ l₁ m₀ f x

/-- **The partial-sum maximal function is dominated by the chain part** of the variational norm of
the low-pass walk (the two-point chain `0 → K`), in the old `A7G` signature. -/
lemma partMaxD_le_chainPart (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    partMaxD ρ l₁ m₀ f x
      ≤ Work.KMTAreas.A7Hi.chainPart 3 (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x) := by
  simpa only [partMaxD] using
    Work.KMTAreas.A7Hi2.partMaxD_le_chainPart ρ l₁ m₀ f x

end Work.KMTAreas.A7G
