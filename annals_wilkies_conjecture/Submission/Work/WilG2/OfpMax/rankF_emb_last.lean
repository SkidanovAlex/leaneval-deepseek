import Mathlib
import Submission.Work.WilG2.Sorting

namespace Work.WilG2.OfpMax

theorem rankF_emb_last {m : ℕ} (d : OrderedFinpartition m) (τ : Equiv.Perm (Fin d.length))
    (i : Fin d.length) :
    rankF (fun l => d.emb (τ l) ⟨d.partSize (τ l) - 1, Nat.sub_one_lt_of_lt (d.partSize_pos (τ l))⟩) i
      = (τ i : ℕ) := by
  rw [rankF]
  -- The greatest element of the part `τ l` is strictly increasing as a function of the part
  -- index, so the comparison of greatest elements is exactly the comparison of the indices.
  have hfilter : (Finset.univ.filter fun l =>
        d.emb (τ l) ⟨d.partSize (τ l) - 1, Nat.sub_one_lt_of_lt (d.partSize_pos (τ l))⟩ <
        d.emb (τ i) ⟨d.partSize (τ i) - 1, Nat.sub_one_lt_of_lt (d.partSize_pos (τ i))⟩)
      = Finset.univ.filter fun l => τ l < τ i := by
    apply Finset.filter_congr
    intro l _
    exact d.parts_strictMono.lt_iff_lt
  rw [hfilter]
  -- Reindex the filtered set by the permutation `τ`.
  have hbij : (Finset.univ.filter fun l => τ l < τ i).card
      = (Finset.univ.filter fun k : Fin d.length => k < τ i).card := by
    apply Finset.card_bij (fun l _ => τ l)
    · intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact hl
    · intro a _ b _ hab
      exact τ.injective hab
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact ⟨τ.symm b, by simpa using hb, τ.apply_symm_apply b⟩
  rw [hbij]
  -- The number of `k : Fin d.length` with `k < τ i` is `(τ i : ℕ)`.
  have hlast : (Finset.univ.filter fun k : Fin d.length => k < τ i) = Finset.Iio (τ i) := by
    ext k; simp [Finset.mem_Iio]
  rw [hlast, Fin.card_Iio]

end Work.WilG2.OfpMax
