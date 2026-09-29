import Mathlib
import Submission.Work.Layout.Shared
import Submission.Work.Layout.sliceIdx
import Submission.Work.SB.keyFacts

namespace Work.SB.Core

/-!
# The relabelled list is the sorted relabelled list

`keyIdx1 m B` is a bijection of `range (A*m*B)` (`Work.SB.keyFacts`), with inverse `invIdx1 m B`
(`Work.Layout.keyIdx1_invIdx1`, `Work.Layout.invIdx1_keyIdx1`).

Consequently the two lists

* `L i   = cons (int (keyIdx1 m B i)) (es.getD i nil)`,  `i < N`,
* `T t   = cons (int t) (es.getD (invIdx1 m B t) nil)`,  `t < N`,

have exactly the same elements (`i ↦ pairKey` in one direction, `t ↦ invIdx1` in the other).
Both are sorted by `pairKey` (for `T` this is just `0 < 1 < ⋯ < N-1`), and `pairKey`-comparison is
irreflexive and antisymmetric, so a `pairKey`-sorted list is determined by its set of elements:
`List.Pairwise.eq_of_mem_iff`.  Hence any `pairKey`-sorted permutation `ys` of `L` equals `T`.
-/

/-- If `f` and `g` are mutually inverse on `{0,…,N-1}` (and preserve that set) then the
`f`-relabelled list and the `g`-relabelled list have the same elements, so a `pairKey`-sorted
permutation of one is the other. -/
theorem sortedLabelledEq_aux (N : ℕ) (f g : ℕ → ℕ)
    (hfN : ∀ i, i < N → f i < N) (hgN : ∀ t, t < N → g t < N)
    (hgf : ∀ t, t < N → f (g t) = t) (hfg : ∀ i, i < N → g (f i) = i)
    (es ys : List HvdH.Val)
    (hperm : ys.Perm ((List.range N).map (fun i =>
      HvdH.Val.cons (HvdH.Val.int ((f i : ℕ) : ℤ)) (es.getD i HvdH.Val.nil))))
    (hsort : ys.Pairwise (fun a b => HvdH.pairKey a < HvdH.pairKey b)) :
    ys = (List.range N).map (fun t =>
      HvdH.Val.cons (HvdH.Val.int ((t : ℕ) : ℤ)) (es.getD (g t) HvdH.Val.nil)) := by
  haveI : Std.Irrefl (fun a b : HvdH.Val => HvdH.pairKey a < HvdH.pairKey b) :=
    ⟨fun a h => absurd h (lt_irrefl (HvdH.pairKey a))⟩
  haveI : Std.Antisymm (fun a b : HvdH.Val => HvdH.pairKey a < HvdH.pairKey b) :=
    ⟨fun a b h1 h2 => absurd h2 (lt_asymm h1)⟩
  refine List.Pairwise.eq_of_mem_iff hsort ?_ ?_
  · -- the `g`-relabelled list is sorted: its keys are `0, 1, …, N-1`
    rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp (fun hab => ?_)
    exact Int.ofNat_lt.mpr hab
  · -- and it has the same elements as the `f`-relabelled list
    intro a
    constructor
    · intro ha
      have haL : a ∈ (List.range N).map (fun i =>
          HvdH.Val.cons (HvdH.Val.int ((f i : ℕ) : ℤ)) (es.getD i HvdH.Val.nil)) :=
        (List.Perm.mem_iff hperm).mp ha
      rcases List.mem_map.mp haL with ⟨i, hi, hia⟩
      have hiN : i < N := List.mem_range.mp hi
      exact List.mem_map.mpr ⟨f i, List.mem_range.mpr (hfN i hiN), by rw [← hia, hfg i hiN]⟩
    · intro ha
      rcases List.mem_map.mp ha with ⟨t, ht, hta⟩
      have htN : t < N := List.mem_range.mp ht
      exact (List.Perm.mem_iff hperm).mpr
        (List.mem_map.mpr ⟨g t, List.mem_range.mpr (hgN t htN), by rw [← hta, hgf t htN]⟩)

theorem sortedLabelledEq (A m B : ℕ) (hm : 0 < m) (hB : 0 < B) (es ys : List HvdH.Val)
    (hlen : es.length = A * m * B)
    (hperm : ys.Perm ((List.range (A * m * B)).map (fun i =>
      HvdH.Val.cons (HvdH.Val.int ((Work.Layout.keyIdx1 m B i : ℕ) : ℤ)) (es.getD i HvdH.Val.nil))))
    (hsort : ys.Pairwise (fun a b => HvdH.pairKey a < HvdH.pairKey b)) :
    ys = (List.range (A * m * B)).map (fun t =>
      HvdH.Val.cons (HvdH.Val.int ((t : ℕ) : ℤ)) (es.getD (Work.Layout.invIdx1 m B t) HvdH.Val.nil)) := by
  obtain ⟨hfN, _⟩ := Work.SB.keyFacts A m B hm hB
  exact sortedLabelledEq_aux (A * m * B) (Work.Layout.keyIdx1 m B) (Work.Layout.invIdx1 m B)
    hfN
    (fun t ht => Work.Layout.invIdx1_lt A m B hm hB t ht)
    (fun t _ => Work.Layout.keyIdx1_invIdx1 m B t hm hB)
    (fun i _ => Work.Layout.invIdx1_keyIdx1 m B i hm hB)
    es ys hperm hsort

end Work.SB.Core
