import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.pbIterGoDefs

/-!
# `Work.Resample.pbIterTight`: the two interface statements of the slice-application word

`Work.Resample.ApplyAlongWord` (in `pbIterGoDefs.lean`) asks for a word constructor `comb` which,
given a word `q` mapping an `m`-slice to an `n`-slice, applies `q` to every slice of a flat
`A × m × B` array in the `slices`/`unslices` layout.  This file isolates the two ingredients of the
obvious construction

`transpose (A,m,B) ;; chunksOf m ;; mapList q ;; flatten ;; transpose (A,B,n)`

(where the final transpose uses
`List.flatten (slices A B n (List.flatten outs)) = unslices A n B outs`):

* `Work.Resample.TransposeWord` — the layout transpose (a verbatim copy of the statement of
  `Work.SynFFT.HasAxisTranspose`, so that either that theorem or the `Layout`-equivalent
  `Work.Layout.applyAlongWord` route can discharge it);
* `Work.Resample.ChunksOfWord` — the chunking word (a verbatim copy of the statement of
  `Work.Layout.chunksOfWord`).

## The construction in detail (for the prover of `pbApplyAlongT`)

Given `hT : TransposeWord` and `hC : ChunksOfWord`, with `q`, `rest`, `m`, `n`, `A`, `B`, `P`, `Q`,
`c`, `L` and `es` as in the statement of `Work.Resample.ApplyAlongWord`:

0. STACK CHOREOGRAPHY (reviewers' caveat, do not skip): the pre of `ApplyAlongWord` has stack 0
   equal to `int A :: int m :: int n :: int B :: ofList es :: rest`, i.e. the array *below* the four
   ints, whereas `TransposeWord` wants `ofList es :: int A :: int t :: int B :: rest`, i.e. the array
   on top.  Roll `ofList es` to the top (and the `int m`/`int n` aside), so that the four ints are
   recovered under the array.  Note that `q`'s spec in `ApplyAlongWord` takes the *same* `rest` on
   every slice, so the ints (and anything not in `rest`) must be parked on another stack while
   `mapList q` runs and restored afterwards; the budget's `K*(isz A + isz m + isz n + isz B)` term
   covers exactly this.
1. `hT` at `(A, m, B)` on `ofList es` (with `int A :: int m :: int n :: int B :: rest` below) sends
   stack 0 to `ofList w₁` where `w₁ = List.flatten (HvdH.slices A m B es)`; the four `int`s stay;
2. `kernelLib.pushVal` at `int m`, then `hC` at `m` and `w₁` (`m ∣ w₁.length` since
   `w₁.length = A*m*B`), sends stack 0 to `ofList (List.range (A*B)).map (fun i => ofList ((w₁.drop (i*m)).take m))`;
3. `kernelLib.mapList` with `q`: the `i`-th chunk is `ofList ((w₁.drop (i*m)).take m)`, which is
   `ofList ((slices A m B es).getD i [])` — this needs the pure lemma
   `(List.flatten (slices A m B es)).drop (i*m)).take m = (slices A m B es).getD i []` for
   `i < A*B`; its length is `m`, and `P` holds for it by hypothesis, so `q` applies with cost `c`
   and produces `outs` with `outs.getD i []` of length `n` and `Q` holding;
4. `Work.Layout.flattenWord` flattens `ofList (outs.map ofList)` to `ofList (List.flatten outs)`;
5. `hT` at `(A, B, n)` on `List.flatten outs` sends stack 0 to
   `ofList (List.flatten (slices A B n (List.flatten outs)))`, which is `ofList (unslices A n B outs)`
   — this needs the pure lemma
   `List.flatten (slices A B n (List.flatten outs)) = unslices A n B outs` (verified numerically for
   many small `A, n, B`; both sides have length `A*B*n` and are `List.range`-maps of `getD`s);
6. the cost is the sum of the four pieces; the transpose terms are bounded by the
   `K * (A*B*(m+n+1)+1) * (L + (A*B*(m+n+1)).size + 1) * ((A*B*(m+n+1)).size + 1)` budget because
   `A*m*B ≤ A*B*(m+n+1)` and `(m).size ≤ (A*B*(m+n+1)).size`, and the `mapList` term is
   `A*B * (c + K' * (m*(L+1) + 1)) + K' ≤ A*B*c + (the budget)` since
   `A*B*m*(L+1) ≤ A*B*(m+n+1)*(L + (A*B*(m+n+1)).size + 1)`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The layout-transpose word: `ofList es ↦ ofList (List.flatten (slices A t B es))`, one pass over
the data per row-split level.  (This is `Work.SynFFT.HasAxisTranspose` verbatim.) -/
def TransposeWord : Prop :=
  ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (A t B : ℕ) (es : List Val) (L : ℕ) (rest : List Val),
    es.length = A * t * B → (∀ x ∈ es, vsz x ≤ L) →
    WordR main prog
      (fun vs => vs = ofList es :: .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ out => out = ofList (List.flatten (slices A t B es)) ::
        .int (A : ℤ) :: .int (t : ℤ) :: .int (B : ℤ) :: rest)
      (fun _ => K * (A * t * B) * (L + 1) * ((t).size + 1) +
        K * (A * t * B) * ((A * t * B).size + 1) + K)

/-- The chunking word: cut `ofList xs` into consecutive chunks of length `m`.  (This is
`Work.Layout.chunksOfWord` verbatim.) -/
def ChunksOfWord : Prop :=
  ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (m : ℕ) (xs : List Val), 1 ≤ m → m ∣ xs.length →
    WordR main p (fun vs => ∃ rest, vs = .int m :: ofList xs :: rest)
      (fun vs out => ∃ rest, vs = .int m :: ofList xs :: rest ∧
        out = ofList ((List.range (xs.length / m)).map fun i => ofList ((xs.drop (i * m)).take m))
          :: rest)
      (fun _ => K * (vsz (ofList xs) + (xs.length / m + 1) * isz m + 1))

end Work.Resample
