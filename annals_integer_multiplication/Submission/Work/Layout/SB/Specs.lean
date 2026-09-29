import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Layout.Shared
import Submission.Work.Layout.Base

/-!
# Sort-based route for `LayoutLib.applyAlong` (paper Lemma 2.11)

Shared vocabulary for the sort-based proof of `Work.Layout.applyAlongWord`:

* `SortSpec`, `ChunksSpec`, `FlattenSpec`, `EnumerateSpec`, `ReplicateSpec` are verbatim copies of
  the corresponding `HvdH.LayoutLib` field STATEMENTS, so that `applyAlong` can be proved *modulo*
  those fields (and the fields plugged in later by `layoutLib`, which owns the whole structure).
* `unlab` strips the key from a labelling record `cons (int k) v`.
* `lab1`/`lab2` are the two labelling maps used by the proof (see `slices`/`unslices`).

The pipeline (all words act on stack 0, other stacks restored):

```
int A :: int m :: int n :: int B :: ofList es :: rest
  --(raw) park params-->  ofList es :: rest            (stack 1 holds n, A, and a copy of B)
  --(raw) build tail  -->  ofList es :: A :: m :: B :: rest
  enumerate ; mapList kw1 ; sortByKey ; strip          -->  ofList (slices A m B es).flatten :: A :: m :: B :: rest
  roll 2 ; dup ; ifZero on m:
     m ≠ 0:  chunksOf m                                -->  ofList (slices A m B es |>.map ofList) :: rest
     m = 0:  replicate (A*B) nil                       -->  ofList (replicate (A*B) nil) :: rest
  mapList q                                            -->  ofList (outs.map ofList) :: rest
  flatten ; enumerate ; mapList kw2 ; sortByKey ; strip-->  ofList (unslices A n B outs) :: rest
```
-/

set_option autoImplicit false

namespace Work.Layout

open HvdH

/-- the `LayoutLib.sortByKey` field statement -/
abbrev SortSpec : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs : List Val),
  (∀ x ∈ xs, ∃ (k : ℕ) (v : Val), x = .cons (.int k) v) → (xs.map pairKey).Nodup →
  WordR main p (fun vs => ∃ rest, vs = ofList xs :: rest)
    (fun vs out => ∃ rest ys, vs = ofList xs :: rest ∧ out = ofList ys :: rest ∧ ys.Perm xs ∧
      ys.Pairwise fun a b => pairKey a < pairKey b)
    (fun _ => K * (vsz (ofList xs) + 1) * (xs.length.size + 1))

/-- the `LayoutLib.chunksOf` field statement -/
abbrev ChunksSpec : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (m : ℕ) (xs : List Val),
  1 ≤ m → m ∣ xs.length →
  WordR main p (fun vs => ∃ rest, vs = .int m :: ofList xs :: rest)
    (fun vs out => ∃ rest, vs = .int m :: ofList xs :: rest ∧
      out = ofList ((List.range (xs.length / m)).map fun i => ofList ((xs.drop (i * m)).take m)) :: rest)
    (fun _ => K * (vsz (ofList xs) + (xs.length / m + 1) * isz m + 1))

/-- the `LayoutLib.flatten` field statement -/
abbrev FlattenSpec : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xss : List (List Val)),
  WordR main p (fun vs => ∃ rest, vs = ofList (xss.map ofList) :: rest)
    (fun vs out => ∃ rest, vs = ofList (xss.map ofList) :: rest ∧ out = ofList xss.flatten :: rest)
    (fun _ => K * (vsz (ofList (xss.map ofList)) + 1))

/-- the `LayoutLib.enumerate` field statement -/
abbrev EnumerateSpec : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (xs : List Val), WordR main p
  (fun vs => ∃ rest, vs = ofList xs :: rest)
  (fun vs out => ∃ rest, vs = ofList xs :: rest ∧
    out = ofList ((List.range xs.length).map fun i : ℕ => Val.cons (.int (i : ℤ)) (xs.getD i .nil)) :: rest)
  (fun _ => K * (vsz (ofList xs) + xs.length * (xs.length.size + 1) + 1))

/-- the `LayoutLib.replicate` field statement -/
abbrev ReplicateSpec : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (k : ℕ) (v : Val), WordR main p
  (fun vs => ∃ rest, vs = .int k :: v :: rest)
  (fun vs out => ∃ rest, vs = .int k :: v :: rest ∧ out = ofList (List.replicate k v) :: rest)
  (fun _ => K * ((k + 1) * (vsz v + 1) + isz k + 1))

/-- strip the key off a labelling record `cons (int k) v` -/
def unlab : Val → Val
  | .cons (.int _) v => v
  | _ => .nil

/-- first labelling: the flat index `i` of `es` becomes the slice-major position `keyIdx1 m B i` -/
def lab1 (m B : ℕ) : Val → Val
  | .cons (.int i) v => .cons (.int ((keyIdx1 m B i.toNat : ℕ) : ℤ)) v
  | x => x

/-- second labelling: the position `f` of the flattened output slices becomes the flat index
`tgtIdx n B (f/n) (f%n)` of the `A × n × B` output array -/
def lab2 (n B : ℕ) : Val → Val
  | .cons (.int f) v => .cons (.int ((tgtIdx n B (f.toNat / n) (f.toNat % n) : ℕ) : ℤ)) v
  | x => x

/-- element word of the first labelling, in the shape required by `KernelLib.mapList`
(the per-element word sees `x :: int m :: int B :: tail`; the caller puts `A` in the tail) -/
abbrev Kw1Spec : Prop := ∃ (p : Cmd) (K : ℕ),
  ∀ (main : Cmd) (m B N Lin : ℕ) (i : ℤ) (v : Val) (tail : List Val),
    0 < m → 0 < B → 0 ≤ i → i.toNat < N → keyIdx1 m B i.toNat < N →
    isz (m : ℤ) ≤ Lin → isz (B : ℤ) ≤ Lin → vsz (.cons (.int i) v) ≤ Lin →
    vsz (Val.cons (.int ((keyIdx1 m B i.toNat : ℕ) : ℤ)) v) ≤ Lin + N.size + 2 ∧
    WordR main p
      (fun vs => vs = .cons (.int i) v :: .int (m : ℤ) :: .int (B : ℤ) :: tail)
      (fun _ out => out = .cons (.int ((keyIdx1 m B i.toNat : ℕ) : ℤ)) v ::
        .int (m : ℤ) :: .int (B : ℤ) :: tail)
      (fun _ => K * (Lin + N.size + 2) * (N.size + 2))

/-- element word of the second labelling (`x :: int n :: int B :: tail`) -/
abbrev Kw2Spec : Prop := ∃ (p : Cmd) (K : ℕ),
  ∀ (main : Cmd) (n B N Lin : ℕ) (f : ℤ) (v : Val) (tail : List Val),
    0 < n → 0 < B → 0 ≤ f → f.toNat < N → tgtIdx n B (f.toNat / n) (f.toNat % n) < N →
    isz (n : ℤ) ≤ Lin → isz (B : ℤ) ≤ Lin → vsz (.cons (.int f) v) ≤ Lin →
    vsz (Val.cons (.int ((tgtIdx n B (f.toNat / n) (f.toNat % n) : ℕ) : ℤ)) v) ≤ Lin + N.size + 2 ∧
    WordR main p
      (fun vs => vs = .cons (.int f) v :: .int (n : ℤ) :: .int (B : ℤ) :: tail)
      (fun _ out => out = .cons (.int ((tgtIdx n B (f.toNat / n) (f.toNat % n) : ℕ) : ℤ)) v ::
        .int (n : ℤ) :: .int (B : ℤ) :: tail)
      (fun _ => K * (Lin + N.size + 2) * (N.size + 2))

/-- the key-stripping word -/
abbrev StripSpec : Prop := ∃ (p : Cmd) (K : ℕ),
  ∀ (main : Cmd) (Lin : ℕ) (k : ℤ) (v : Val) (tail : List Val),
    vsz (.cons (.int k) v) ≤ Lin →
    vsz v ≤ Lin ∧ WordR main p
      (fun vs => vs = .cons (.int k) v :: tail) (fun _ out => out = v :: tail)
      (fun _ => K * (Lin + 1))

/-- the raw prologue of the sort-based `applyAlong`: park `int n` and a copy of `int B` on stack 1
(`int B` on top) and rearrange the value list into `ofList es :: int m :: int B :: int A :: rest` -/
abbrev PrologueSpec : Prop := ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (g : Reg → Glyph)
    (X : Stk → List Glyph) (R : List Glyph) (A m n B : ℕ) (es rest : List Val),
    X 0 = encs (Val.int A :: Val.int m :: Val.int n :: Val.int B :: ofList es :: rest) ++ R →
    ∃ s' N, Ev main prog ⟨g, X⟩ s' N ∧
      N ≤ K * (isz (A : ℤ) + isz (m : ℤ) + isz (n : ℤ) + isz (B : ℤ) + (vsz (ofList es) + 1)) ∧
      s'.stk 0 = encs (ofList es :: Val.int m :: Val.int B :: Val.int A :: rest) ++ R ∧
      s'.stk 1 = (Val.int B).enc ++ (Val.int n).enc ++ X 1 ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = X k)

/-- the raw epilogue of the sort-based `applyAlong`: move the working list aside, fetch the parked
`int B` and `int n` from stack 1, and put them back below the working list -/
abbrev EpilogueSpec : Prop := ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (g : Reg → Glyph)
    (X : Stk → List Glyph) (R : List Glyph) (T1 : List Glyph) (n B : ℕ) (flat : Val)
    (rest : List Val),
    X 0 = encs (flat :: rest) ++ R → X 1 = (Val.int B).enc ++ (Val.int n).enc ++ T1 →
    ∃ s' N, Ev main prog ⟨g, X⟩ s' N ∧
      N ≤ K * ((vsz flat + 1) + isz (n : ℤ) + isz (B : ℤ) + 1) ∧
      s'.stk 0 = encs (flat :: Val.int n :: Val.int B :: rest) ++ R ∧
      s'.stk 1 = T1 ∧
      (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = X k)

/-- the two sort phases of the sort-based `applyAlong` (`phase1`/`phase3` statements) -/
abbrev Phase1Spec : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (A m B N L : ℕ) (es : List Val)
    (rest : List Val),
      0 < m → 0 < B → A * m * B ≤ N → es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      WordR main p
        (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (fun _ out => out = ofList ((slices A m B es).flatten) ::
          .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1))

abbrev Phase3Spec : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (A n B N L : ℕ)
    (outs : List (List Val)) (rest : List Val),
      0 < n → 0 < B → A * B * n ≤ N → outs.length = A * B →
      (∀ s, s < A * B → (outs.getD s []).length = n) →
      (∀ s, s < A * B → ∀ y ∈ outs.getD s [], vsz y ≤ L) →
      WordR main p
        (fun vs => vs = ofList (outs.map ofList) :: .int (n : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ out => out = ofList (unslices A n B outs) :: .int (n : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1))

/-- the `LayoutLib.applyAlong` field statement -/
abbrev ApplyAlongSpec : Prop := ∃ (comb : Cmd → Cmd) (K : ℕ), ∀ (main q : Cmd) (rest : List Val)
    (m n : ℕ) (P : List Val → Prop) (Q : List Val → List Val → Prop) (c L : ℕ),
      (∀ sl : List Val, sl.length = m → P sl → WordR main q (fun vs => vs = ofList sl :: rest)
        (fun _ out => ∃ ol, out = ofList ol :: rest ∧ ol.length = n ∧ Q sl ol ∧ ∀ y ∈ ol, vsz y ≤ L)
        (fun _ => c)) →
      ∀ (A B : ℕ) (es : List Val), es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      (∀ s < A * B, P ((slices A m B es).getD s [])) →
      WordR main (comb q) (fun vs => vs = .int A :: .int m :: .int n :: .int B :: ofList es :: rest)
        (fun _ out => ∃ outs : List (List Val), out = ofList (unslices A n B outs) :: rest ∧
          outs.length = A * B ∧ ∀ s < A * B, (outs.getD s []).length = n ∧
            Q ((slices A m B es).getD s []) (outs.getD s []))
        (fun _ => A * B * c +
          K * (A * B * (m + n + 1) + 1) * (L + (A * B * (m + n + 1)).size + 1) *
            ((A * B * (m + n + 1)).size + 1) + K * (isz A + isz m + isz n + isz B))

/-- the `branchWord` statement (main branch of the sort-based `applyAlong`) -/
abbrev BranchSpec : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (A m B N L : ℕ) (es : List Val)
    (rest : List Val),
      0 < B → A * B ≤ N → A * m * B ≤ N → es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      WordR main p
        (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (fun _ out => ∃ sls : List (List Val), out = ofList (sls.map ofList) :: rest ∧
          sls = slices A m B es)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1))

/-- size facts about `ofList`/`slices` -/
abbrev VszSpec : Prop :=
    (∀ (l : List Val), vsz (ofList l) = (l.map vsz).sum + l.length + 1) ∧
    (∀ (l : List Val) (L : ℕ), (∀ x ∈ l, vsz x ≤ L) → vsz (ofList l) ≤ (l.length + 1) * (L + 1)) ∧
    (∀ (A m B : ℕ) (es : List Val) (L : ℕ), 0 < m → es.length = A * m * B →
      (∀ x ∈ es, vsz x ≤ L) →
      ∀ s, s < A * B → vsz (ofList ((slices A m B es).getD s [])) ≤ (m + 1) * (L + 1)) ∧
    (∀ (A n B : ℕ) (outs : List (List Val)) (L : ℕ), outs.length = A * B →
      (∀ s, s < A * B → (outs.getD s []).length = n) →
      (∀ s, s < A * B → ∀ y ∈ outs.getD s [], vsz y ≤ L) →
      vsz (ofList (outs.map ofList)) ≤ A * B * (n * (L + 1) + 1) + A * B + 1)

/-- the `Forall₂` repackaging used after `mapList q` -/
abbrev Forall2Spec : Prop := ∀ {A B m n : ℕ} (sls : List (List Val))
    (Q : List Val → List Val → Prop) (xs ys : List Val),
    sls.length = A * B → (∀ s, s < A * B → (sls.getD s []).length = m) → xs = sls.map ofList →
    (∀ y ∈ ys, ∃ ol : List Val, y = ofList ol) →
    List.Forall₂ (fun x y => ∃ (sl ol : List Val), x = ofList sl ∧ y = ofList ol ∧
      ol.length = n ∧ Q sl ol) xs ys →
    ∃ outs : List (List Val), ys = outs.map ofList ∧ outs.length = A * B ∧
      (∀ s, s < A * B → (outs.getD s []).length = n) ∧
      ∀ s, s < A * B → Q (sls.getD s []) (outs.getD s [])

/-- the `branchWord2` statement (degenerate `A*B = 0` handled inside) -/
abbrev Branch2Spec : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (A m B N L : ℕ) (es : List Val)
    (rest : List Val),
      A * B ≤ N → A * m * B ≤ N → es.length = A * m * B → (∀ x ∈ es, vsz x ≤ L) →
      WordR main p
        (fun vs => vs = ofList es :: .int (m : ℤ) :: .int (B : ℤ) :: .int (A : ℤ) :: rest)
        (fun _ out => ∃ sls : List (List Val), out = ofList (sls.map ofList) :: rest ∧
          sls = slices A m B es)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1) +
          K * (isz A + isz m + isz B))

/-- the `phase3b` statement (degenerate `n = 0`/`B = 0` handled inside) -/
abbrev Phase3bSpec : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (A n B N L : ℕ)
    (outs : List (List Val)) (rest : List Val),
      A * B ≤ N → A * B * n ≤ N → outs.length = A * B →
      (∀ s, s < A * B → (outs.getD s []).length = n) →
      (∀ s, s < A * B → ∀ y ∈ outs.getD s [], vsz y ≤ L) →
      WordR main p
        (fun vs => vs = ofList (outs.map ofList) :: .int (n : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ out => out = ofList (unslices A n B outs) :: .int (n : ℤ) :: .int (B : ℤ) :: rest)
        (fun _ => K * (N + 1) * (L + N.size + 1) * (N.size + 1))

/-- the `slicesFacts` statement -/
abbrev SlicesSpec : Prop :=
    (∀ (A m B : ℕ) (es : List Val), (slices A m B es).length = A * B) ∧
    (∀ (A m B : ℕ) (es : List Val) (s : ℕ), s < A * B → ((slices A m B es).getD s []).length = m) ∧
    (∀ (A m B : ℕ) (es : List Val), slices A 0 B es = List.replicate (A * B) [])

/-- the `tailRaw` statement (flatten, epilogue, output phase and the final drops) -/
abbrev TailSpec : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (g : Reg → Glyph)
    (X : Stk → List Glyph) (R T1 : List Glyph) (A n B N L : ℕ) (outs : List (List Val))
    (rest : List Val),
      A * B ≤ N → A * B * n ≤ N → outs.length = A * B →
      (∀ s, s < A * B → (outs.getD s []).length = n) →
      (∀ s, s < A * B → ∀ y ∈ outs.getD s [], vsz y ≤ L) →
      vsz (ofList (outs.map ofList)) + 1 ≤ (N + 1) * (L + 1) →
      vsz (ofList (outs.flatten)) + 1 ≤ (N + 1) * (L + 1) →
      X 0 = encs (ofList (outs.map ofList) :: rest) ++ R →
      X 1 = (Val.int B).enc ++ (Val.int n).enc ++ T1 →
      ∃ (s' : State) (N' : ℕ), Ev main p ⟨g, X⟩ s' N' ∧
        N' ≤ K * ((N + 1) * (L + N.size + 1) * (N.size + 1) + (isz (n : ℤ) + isz (B : ℤ)) + 1) ∧
        s'.stk 0 = encs (ofList (unslices A n B outs) :: rest) ++ R ∧
        s'.stk 1 = T1 ∧ (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = X k)

end Work.Layout

namespace Work.Layout

open HvdH

/-- Size of the output of the second sort phase: the list `unslices A n B outs` is flat of length
`A*n*B`, and each entry is an entry of some slice (size `≤ L`) or the default value (size `1`),
so its `ofList` value has size `≤ A*n*B*(L+3)+1`. -/
abbrev UnsliceVszSpec : Prop := ∀ (A n B : ℕ) (outs : List (List Val)) (L : ℕ),
  outs.length = A * B → (∀ s, s < A * B → (outs.getD s []).length = n) →
  (∀ s, s < A * B → ∀ y ∈ outs.getD s [], vsz y ≤ L) →
  vsz (ofList (unslices A n B outs)) ≤ A * n * B * (L + 3) + 1

/-- The corrected `tailRaw` statement: the two size hypotheses are exactly
`s ≤ triple + 1` for `triple = (N+1)*(L+N.size+1)*(N.size+1)`, which is what the tail's cost
budget `K*(triple + (isz n + isz B) + 1)` can afford (the strongest form stated with `(N+1)*(L+1)`
is NOT derivable from `LayoutLib.applyAlong`'s hypotheses: at `A*B = 0`, `L = 0` one has
`vsz (ofList []) = 1 > 0 = N`). -/
abbrev TailSpec2 : Prop := ∃ (p : Cmd) (K : ℕ), ∀ (main : Cmd) (g : Reg → Glyph)
    (X : Stk → List Glyph) (R T1 : List Glyph) (A n B N L : ℕ) (outs : List (List Val))
    (rest : List Val),
      A * B ≤ N → A * B * n ≤ N → outs.length = A * B →
      (∀ s, s < A * B → (outs.getD s []).length = n) →
      (∀ s, s < A * B → ∀ y ∈ outs.getD s [], vsz y ≤ L) →
      vsz (ofList (outs.map ofList)) + 1 ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) + 1 →
      vsz (ofList (unslices A n B outs)) + 1 ≤ (N + 1) * (L + N.size + 1) * (N.size + 1) + 1 →
      X 0 = encs (ofList (outs.map ofList) :: rest) ++ R →
      X 1 = (Val.int B).enc ++ (Val.int n).enc ++ T1 →
      ∃ (s' : State) (N' : ℕ), Ev main p ⟨g, X⟩ s' N' ∧
        N' ≤ K * ((N + 1) * (L + N.size + 1) * (N.size + 1) + (isz (n : ℤ) + isz (B : ℤ)) + 1) ∧
        s'.stk 0 = encs (ofList (unslices A n B outs) :: rest) ++ R ∧
        s'.stk 1 = T1 ∧ (∀ k : Stk, k ≠ 0 → k ≠ 1 → s'.stk k = X k)

end Work.Layout
