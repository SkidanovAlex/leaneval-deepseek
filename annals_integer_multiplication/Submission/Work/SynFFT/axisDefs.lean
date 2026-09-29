import Mathlib
import Submission.Work.SynFFT.kit2

/-!
# The layout-transpose word (`Work.SynFFT.HasAxisTranspose`)

The SynFFT axis pass has to apply a *slice-local* word to every `i`-slice of the `A × t × B`
decomposition of a flat array, and reassemble the result in the same flat layout.  The
"gather/scatter" part of that is a pure layout operation: the permutation

`i = (a*t + j)*B + b  ↦  (a*B + b)*t + j`

of `[0, A*t*B)` (per `A`-block, the transpose of the `t × B` index matrix).  `HvdH.slices`
computes exactly this gather, so the gather is the word taking `ofList es` to
`ofList (List.flatten (slices A t B es))`, and calling the *same* word with the shapes `(A, B, t)`
computes the scatter back (the transpose of the transpose, in the sense of
`Work.SynFFT.axisTransposeSwap` below).

## Why a new word (and not `HvdH.LayoutLib.applyAlong`)

`applyAlong` (paper Lemma 2.11) performs gather + per-slice word + scatter in one pass, but its
cost carries the factor `(A*B*(m+n+1)).size` twice, i.e. it pays `≈ N·(log N)²` for
`N = A*t*B`, whereas the axis pass of the synthetic FFT is budgeted `O(N·r·p·(log t + log N))`
(`Work.SynFFT.HasAxis`, and the top-level `HvdH.SynFFTProp` target
`K*(M r)*p*(log(M r)+1)+K`).  With `log N ≤ p` (the real regime, `ts.prod * r < 2^p`) the two
agree only up to the constant `log N/(r p)`, but `HasAxis` quantifies over *unbounded* `A` and
`K` is chosen before `A`, so no single `K` can absorb it there.  The transpose below is instead
budgeted `O(N·(log t + log N))`: it is the same operation but implemented by the row-recursion

`T(t) = interleaveRows (T(t/2) (even rows)) (T(t/2) (odd rows))`

which costs one pass over the data per level (`log₂ t` levels), instead of a keyed sort.

## Intended implementation (for the prover)

For one `t × B` index block (rows = consecutive chunks of `B` cells):

* `k` "deal" levels: repeatedly split the rows of every current sub-block into its even and odd
  rows (`chunksOf (2^{r+1}*B)` at the value level, then a `mapList` of a fixed "deal rows" word,
  then `flatten`); after `k` levels the `t = 2^k` rows are isolated, in bit-reversed order;
* `k` "interleave" levels: pairwise interleave the row lists, the row length doubling
  `1, 2, …, 2^{k-1}` (`zipWith` with a word producing `ofList [x, y]`, then `flatten`);
* glue the `A` blocks with `mapList` (`chunksOf (t*B)` at the top level).

Every pass is linear in the encoded data, and the deal/interleave routing is decided by a parity
toggle (no per-element arithmetic on indices), so the cost is `O(N·(L+1)·log t)` plus one `log`
factor for the counters.  The three shape parameters `A`, `t`, `B` can be moved around the
parameter block with `KLib.roll`/`KLib.pushVal` at negligible cost.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-- **The layout-transpose word.** `ofList es ↦ ofList (List.flatten (slices A t B es))`, i.e.
the flat `A × t × B` array regrouped into its `A*B` slices of length `t`, concatenated in slice
order.  Cost: one pass over the data (`A*t*B*(L+1)`, `L` bounding the encoded size of the
elements) per row-split level (`(t).size+1` of them, i.e. `log₂ t + 1`), plus one log factor in
the length of the array. -/
def HasAxisTranspose : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (A t B : ℕ) (es : List Val) (L : ℕ) (rest : List Val),
    es.length = A * t * B → (∀ x ∈ es, vsz x ≤ L) →
    WordR main prog
      (fun vs => vs = ofList es :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ out => out = ofList (List.flatten (HvdH.slices A t B es)) ::
        .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ => K * (A * t * B) * (L + 1) * ((t).size + 1) +
        K * (A * t * B) * ((A * t * B).size + 1) + K)

end Work.SynFFT
