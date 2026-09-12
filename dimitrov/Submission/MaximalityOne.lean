import Mathlib
import Submission.FeketeLim

/-!
# Isolated task: Step-3 s = 1 case -- a segment of length at most L

Self-contained statements (import Submission.FeketeLim).  Prove
`maximality_one` (no unfinished proofs may remain; add helpers freely).

STATEMENT: for `0 ≤ ell ≤ L` (real segment lengths), the Fekete root
limsup of the segment `[0, ell]` is at most `L/4` (so a single spike of
length `≤ L` never exceeds the s = 1 Dubinin bound `L·4^(-1) = L/4`).

PROOF PLAN:
1. Monotonicity in the segment length: for `0 ≤ ell ≤ L`,
   `segment ℝ 0 (ell : ℂ) ⊆ segment ℝ 0 (L : ℂ)` (both are `{t·(·) :
   t ∈ [0,1]}`-style real multiples; prove via `Submission.XTransfer.
   mem_segment_zero_iff`-type membership or the convex-hull definition of
   `segment`), so `feketeNumber (segment ℝ 0 (ell : ℂ)) n ≤ feketeNumber
   (segment ℝ 0 (L : ℂ)) n` for every `n` (configs in the smaller segment
   are configs in the larger; `csSup_le`/`le_csSup` with the defining
   sets of products -- FeketeLim's `feketeNumber` is the sSup over
   configs).
2. The hypothesis `hseg M hM` gives the Fekete root limsup of
   `segment ℝ 0 (M : ℂ)` equals `M/4` for every `0 ≤ M` (this is the
   segment asymptotic, from Submission.SegmentAsymptotic, child L79, and
   is supplied here as a hypothesis).
3. Use monotonicity in `n`: the root-limsup of the smaller segment is `≤`
   the root-limsup of the larger (each term `feketeNumber (smaller)
   (n+1) ≤ feketeNumber (larger) (n+1)`; limsup is monotone), and by
   `hseg` the larger segment's limsup equals `L/4`, so the smaller's
   limsup is `≤ L/4`.  (Show limsup monotonicity via
   `Filter.limsup_le_limsup`-type lemmas or the
   eventually-≤ + limsup characterization; the exponent
   `2/((n+1)n)` is common to both sides.)

NOTES: all ℝ, conditionally-complete lattice lemmas; `Filter.limsup`.
Do NOT change the theorem statement.
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.MaximalityOne

open Filter

/-- A segment of length at most `L` has Fekete root limsup at most `L/4`. -/
theorem maximality_one {ell L : ℝ} (hell : 0 ≤ ell) (hL : 0 ≤ L) (helle : ell ≤ L)
    (hseg : ∀ M : ℝ, 0 ≤ M →
      Filter.limsup (fun n : ℕ =>
        (Submission.FeketeLim.feketeNumber (segment ℝ 0 (M : ℂ)) (n + 1)) ^
          (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop = M / 4) :
    Filter.limsup (fun n : ℕ =>
      (Submission.FeketeLim.feketeNumber (segment ℝ 0 (ell : ℂ)) (n + 1)) ^
        (2 / (((n + 1 : ℝ)) * (n : ℝ)))) Filter.atTop
    ≤ L / 4 := by
  -- The hypothesis `hseg` gives the exact asymptotic for the segment of
  -- length `ell` itself (since `hell : 0 ≤ ell`), namely `ell / 4`,
  -- which is ≤ `L / 4` by `helle : ell ≤ L`.
  rw [hseg ell hell]
  exact div_le_div_of_nonneg_right helle (by norm_num : (0 : ℝ) ≤ 4)

end Submission.MaximalityOne

end
