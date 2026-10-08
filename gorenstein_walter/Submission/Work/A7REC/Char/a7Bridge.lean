/-
Area `A7REC`, file `Char/a7Bridge.lean`: **the p11 bridge** (`Bridge.lean`, `A7BridgeProp`).

Assembly of the three leaves of the bridge:

* B1 `Work.A7REC.a7CharSum`  -- the specialisation `(8/35)·i(x) = Σ_{χ ∈ Irr G} χ(z)²χ(x)/χ(1)`
  of BSW's involution-pair formula `Work.BSW.Char.invPairCount_eq_sum_characters`
  (`Bridge.lean`, proved);
* B2 `Work.A7REC.a7SplitTrivial` -- the principal character contributes `1`
  (`Bridge.lean`, proved);
* B3 `Work.A7REC.Char.a7Reindex` -- reindexing `Σ_{χ ≠ 1}` onto the C1c enumeration `ι`
  (`Char/a7Reindex.lean`, proved).

Feeding B1 at `x = π`, `z`, `zσ` through B2 and B3, and using the involution-pair counts
`i(π) = 4`, `i(z) = 8`, `i(zσ) = 6`, gives the three normalised rational identities

  `1 + Σ_i (b_i - 2a_i)² e_i / f_i = 32/35`,
  `1 + Σ_i (b_i - 2a_i)³     / f_i = 64/35`,
  `1 + Σ_i (b_i - 2a_i)²(a_i + b_i) / f_i = 48/35`

(the `(b-2a)³` of the middle one is the `(b-2a)²·χ(z)` obtained by taking `x = z`), which are
exactly the hypotheses consumed by `A7TableLemmaProp`.

Each conjunct is proved first as the corresponding complex identity (so that `push_cast` can
normalise the rational casts in one go) and then transported back to `ℚ` by
`Rat.cast_injective`.
-/
import Mathlib
import Submission.Work.A7REC.Char.Bridge
import Submission.Work.A7REC.Char.a7Reindex

namespace Work.A7REC.Char

open OddOrder.RepresentationTheory
open scoped Classical

theorem a7Bridge : Work.A7REC.A7BridgeProp := by
  intro G _ _ z π σ hG hz hC hconj hπ hz8 hzσ n ι f e a b hinj hne hzero hf he hzb hzσb
  -- `x = π`, `v = e`: the terms `(b-2a)²·e`.
  have hc1 : (((1 + ∑ i, ((b i - 2 * a i) ^ 2 * e i : ℚ) / (f i : ℚ) : ℚ)) : ℂ)
      = (((32 : ℚ) / 35 : ℚ) : ℂ) := by
    have e1 := Work.A7REC.a7CharSum G z hG hz hC hconj π
    rw [hπ] at e1
    rw [Work.A7REC.a7SplitTrivial G z π] at e1
    rw [a7Reindex G z π n ι f a b e hinj hne hzero hf hzb he] at e1
    have hL : (8 / 35 : ℂ) * ((4 : ℕ) : ℂ) = (((32 : ℚ) / 35 : ℚ) : ℂ) := by norm_num
    rw [hL] at e1
    push_cast at e1 ⊢
    exact e1.symm
  -- `x = z`, `v = b - 2a`: the terms `(b-2a)³`.
  have hc2 : (((1 + ∑ i, ((b i - 2 * a i) ^ 3 : ℚ) / (f i : ℚ) : ℚ)) : ℂ)
      = (((64 : ℚ) / 35 : ℚ) : ℂ) := by
    have e1 := Work.A7REC.a7CharSum G z hG hz hC hconj z
    rw [hz8] at e1
    rw [Work.A7REC.a7SplitTrivial G z z] at e1
    rw [a7Reindex G z z n ι f a b (fun i => b i - 2 * a i) hinj hne hzero hf hzb
      (fun i => by rw [hzb i]; push_cast; ring)] at e1
    have hL : (8 / 35 : ℂ) * ((8 : ℕ) : ℂ) = (((64 : ℚ) / 35 : ℚ) : ℂ) := by norm_num
    rw [hL] at e1
    push_cast at e1 ⊢
    rw [e1]
    exact congrArg (fun t => (1 : ℂ) + t)
      (Finset.sum_congr rfl (fun i _ => by ring))
  -- `x = zσ`, `v = a + b`: the terms `(b-2a)²(a+b)`.
  have hc3 : (((1 + ∑ i, ((b i - 2 * a i) ^ 2 * (a i + b i) : ℚ) / (f i : ℚ) : ℚ)) : ℂ)
      = (((48 : ℚ) / 35 : ℚ) : ℂ) := by
    have e1 := Work.A7REC.a7CharSum G z hG hz hC hconj (z * σ)
    rw [hzσ] at e1
    rw [Work.A7REC.a7SplitTrivial G z (z * σ)] at e1
    rw [a7Reindex G z (z * σ) n ι f a b (fun i => a i + b i) hinj hne hzero hf hzb
      (fun i => by rw [hzσb i]; push_cast; ring)] at e1
    have hL : (8 / 35 : ℂ) * ((6 : ℕ) : ℂ) = (((48 : ℚ) / 35 : ℚ) : ℂ) := by norm_num
    rw [hL] at e1
    push_cast at e1 ⊢
    exact e1.symm
  exact ⟨Rat.cast_injective hc1, Rat.cast_injective hc2, Rat.cast_injective hc3⟩

end Work.A7REC.Char
