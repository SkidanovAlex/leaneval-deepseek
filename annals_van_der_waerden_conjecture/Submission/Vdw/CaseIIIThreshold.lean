import Mathlib
import Submission.Vdw.CaseIIIRegion
import Submission.Commons.Analysis.ExpLog.exists_ceil_rpow_lower_threshold

open Polynomial Asymptotics
open scoped BigOperators
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case III, subcase (ii): the canonical threshold `⌈H^(1/M)⌉` and the region
big-O at `M = 4n`

`CaseIIIRegion.CaseIIISubcase2_isBigO_of_threshold` is abstract over ANY
threshold family `Bfun : ℕ → ℕ` eventually satisfying `n < Bfun H` and
`H ≤ (Bfun H)^M`.  The fleet commons
`Commons.Analysis.ExpLog.exists_ceil_rpow_lower_threshold` provides the
**canonical** family with the third property needed by the eventual
inclusion argument:

* `lowerThreshold M H := Nat.ceil ((H : ℝ) ^ ((1:ℝ)/(M:ℝ)))` — i.e.
  `⌈H^(1/M)⌉₊`;
* `le_pow_lowerThreshold M H` : `H ≤ lowerThreshold M H ^ M` (any `1 ≤ M`);
* `lt_lowerThreshold_of_ge M H` : `M < lowerThreshold M H` once
  `(M+1)^M ≤ H` (so eventually);
* `lowerThreshold_le_of_rpow_le M H p` : `H^(1/M) ≤ p` (real, `p : ℕ`)
  gives `lowerThreshold M H ≤ p` — the property that makes the eventual
  *inclusion* of the Case-III-bad polys (whose admissible primes `p | A`
  exceed `H^(1/(4n))`) into the region with threshold `⌈H^(1/(4n))⌉` work,
  and which the fleet's coarse `B H := H + M + 1` witness does NOT have.

This module instantiates the region big-O at the canonical threshold:

* `caseIII_subcase2_canonical_isBigO n M` : the subcase-(ii) region count at
  threshold `lowerThreshold M` is `O(H^(n-1))` for `3 ≤ n`, `1 ≤ M`,
  `n ≤ M`;
* `caseIII_subcase2_region_isBigO n` : the same at the paper's value
  `M = 4n` (recall `δ/2 = 1/(4n)`, so the admissible primes of subcase (ii)
  are exactly those `p ≥ H^(δ/2)`).

Together with `CaseIIIDDZero.DDzeroBox_isBigO` (the `DD(u_f) = 0` piece) and
the eventual subcase-(i)/Case-I-analogue sieve (still open), this yields the
full Case-III bound.
-/

namespace Submission.Vdw

noncomputable section

/-- The canonical Case-III subcase-(ii) threshold `⌈H^(1/M)⌉₊`. -/
abbrev lowerThr (M : ℕ) : ℕ → ℕ := fun H => Commons.Analysis.ExpLog.lowerThreshold M H

/-- The threshold `⌈H^(1/M)⌉` is eventually above `M` (once
`(M+1)^M ≤ H`). -/
lemma eventually_lt_lowerThr (M : ℕ) (hM : 1 ≤ M) :
    ∀ᶠ H : ℕ in atTop, M < lowerThr M H := by
  rw [Filter.eventually_atTop]
  exact ⟨(M + 1) ^ M, fun H hH => Commons.Analysis.ExpLog.lt_lowerThreshold_of_ge M H hM hH⟩

/-- `H ≤ ⌈H^(1/M)⌉^M` pointwise (for `1 ≤ M`). -/
lemma le_pow_lowerThr (M : ℕ) (hM : 1 ≤ M) (H : ℕ) :
    H ≤ (lowerThr M H) ^ M := by
  exact Commons.Analysis.ExpLog.le_pow_lowerThreshold M H hM

/-- `H^(1/M) ≤ p` (real, `p : ℕ`) gives `⌈H^(1/M)⌉ ≤ p` — the inclusion
property: every prime `p | A_f` with `H^(1/M) ≤ p` is at least the
threshold. -/
lemma lowerThr_le_of_rpow_le (M H p : ℕ)
    (hle : (H : ℝ) ^ ((1 : ℝ) / (M : ℝ)) ≤ (p : ℝ)) : lowerThr M H ≤ p :=
  Commons.Analysis.ExpLog.lowerThreshold_le_of_rpow_le M H p hle

/-- **Case-III subcase (ii) at the canonical threshold.**  For `3 ≤ n`,
`1 ≤ M`, `n ≤ M`: the count of the squarefull-`D_f` subcase-(ii) region at
threshold `B H = ⌈H^(1/M)⌉` is `O(H^(n-1))`.  (For `M = 4n` this is the
paper's `δ/2 = 1/(4n)` value — see `caseIII_subcase2_region_isBigO`.) -/
theorem caseIII_subcase2_canonical_isBigO (n M : ℕ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hnM : n ≤ M) :
    (fun H : ℕ => ((CaseIIISubcase2 n H (lowerThr M H)).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  have hthr : ∀ᶠ H : ℕ in atTop,
      n < lowerThr M H ∧ H ≤ (lowerThr M H) ^ M := by
    filter_upwards [eventually_lt_lowerThr M hM] with H hgt
    exact ⟨lt_of_le_of_lt hnM hgt, le_pow_lowerThr M hM H⟩
  exact CaseIIISubcase2_isBigO_of_threshold n M hn (lowerThr M) hthr

/-- **Case-III subcase (ii), region big-O at the canonical threshold
`⌈H^(1/(4n))⌉`** (the paper's `δ/2 = 1/(4n)`): the subcase-(ii) region count
is `O(H^(n-1))`. -/
theorem caseIII_subcase2_region_isBigO (n : ℕ) (hn : 3 ≤ n) :
    (fun H : ℕ => ((CaseIIISubcase2 n H (lowerThr (4 * n) H)).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  classical
  exact caseIII_subcase2_canonical_isBigO n (4 * n) hn (by omega) (by omega)

end

end Submission.Vdw
