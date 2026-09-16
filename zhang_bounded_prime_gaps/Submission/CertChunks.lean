import Submission.CertIvalT

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# Splitting the `I`-evaluation into chunks

The final numeric verification of `certIvalT` is split into `17` chunks of `16` outer indices,
so that each chunk is a small closed `decide`.  Here we prove the (purely combinatorial)
decomposition `certIvalT = ∑_{i<17} chunkI i`.
-/

namespace Commons.NumberTheory.MaynardSieve

theorem sum_map_take_drop {α β : Type*} [AddCommMonoid β] (l : List α) (g : α → β) (n : ℕ) :
    (l.map g).sum = ((l.take n).map g).sum + ((l.drop n).map g).sum := by
  conv_lhs => rw [← List.take_append_drop (i := n) (l := l)]
  rw [List.map_append, List.sum_append]

theorem sum_map_chunks {α β : Type*} [AddCommMonoid β] (g : α → β) :
    ∀ (l : List α) (N : ℕ), l.length ≤ 16 * N →
      (l.map g).sum = ∑ i ∈ Finset.range N, (((l.drop (16 * i)).take 16).map g).sum := by
  intro l N
  induction N generalizing l with
  | zero =>
      intro h
      have hl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [hl]
  | succ N ih =>
      intro h
      rw [Finset.sum_range_succ', sum_map_take_drop l g 16]
      have hlen : (l.drop 16).length ≤ 16 * N := by
        rw [List.length_drop]; omega
      rw [ih (l.drop 16) hlen]
      have hA : ((l.take 16).map g).sum = (((l.drop (16 * 0)).take 16).map g).sum := by simp
      have hS : (∑ i ∈ Finset.range N, ((((l.drop 16).drop (16 * i)).take 16).map g).sum)
          = (∑ i ∈ Finset.range N, (((l.drop (16 * (i + 1))).take 16).map g).sum) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [List.drop_drop, show 16 + 16 * i = 16 * (i + 1) from by omega]
      rw [hA, hS, add_comm]

/-- The `i`-th chunk of the table-based `I`-evaluation. -/
def chunkI (i : ℕ) : ℤ :=
  List.sum ((((cSigs.zip ssumTableL).drop (16 * i)).take 16).map
    (fun q : (List ℕ × List ℤ) × List ℕ => List.sum ((cSigs.zip q.2).map
      (fun r : (List ℕ × List ℤ) × ℕ => termS r.1 q.1 r.2))))

theorem chunkI_def (i : ℕ) : chunkI i = List.sum ((((cSigs.zip ssumTableL).drop (16 * i)).take 16).map
    (fun q : (List ℕ × List ℤ) × List ℕ => List.sum ((cSigs.zip q.2).map
      (fun r : (List ℕ × List ℤ) × ℕ => termS r.1 q.1 r.2)))) := rfl

theorem certIvalT_chunk : certIvalT = ∑ i ∈ Finset.range 17, chunkI i := by
  have h := sum_map_chunks (fun q : (List ℕ × List ℤ) × List ℕ =>
      List.sum ((cSigs.zip q.2).map (fun r : (List ℕ × List ℤ) × ℕ => termS r.1 q.1 r.2)))
    (cSigs.zip ssumTableL) 17 (by rw [List.length_zip, cSigs_length, ssumTableL_length]; norm_num)
  rw [show certIvalT = List.sum ((cSigs.zip ssumTableL).map
      (fun q : (List ℕ × List ℤ) × List ℕ =>
        List.sum ((cSigs.zip q.2).map (fun r : (List ℕ × List ℤ) × ℕ => termS r.1 q.1 r.2))))
      from rfl, h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (chunkI_def i).symm

end Commons.NumberTheory.MaynardSieve
