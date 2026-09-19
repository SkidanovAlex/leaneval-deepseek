import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.NormNum.Ineq
import Submission.Commons.NumberTheory.BombieriVinogradov.lam4_block_bilinear

namespace Commons.NumberTheory.KroneckerSums

theorem sum_fin12_ite_count_eq_sum_dedup (β : List ℕ) (G : ℕ → ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (F : Fin 12 → ℕ) (hGF : ∀ i : Fin 12, G (2 * ((i : ℕ) + 1)) = F i) :
    (∑ i : Fin 12, (if 0 < β.count (2 * ((i : ℕ) + 1)) then F i else 0))
      = (β.dedup.map G).sum := by
  set s : Finset (Fin 12) :=
    Finset.univ.filter (fun i => 2 * ((i : ℕ) + 1) ∈ β.dedup) with hs
  have hmem : ∀ i : Fin 12, (0 < β.count (2 * ((i : ℕ) + 1))) ↔ i ∈ s := by
    intro i
    rw [List.count_pos_iff, hs]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_dedup]
  have hinj : Set.InjOn (fun i : Fin 12 => 2 * ((i : ℕ) + 1)) (↑s : Set (Fin 12)) := by
    intro a _ b _ h
    simp only at h
    have h2 : (a : ℕ) + 1 = (b : ℕ) + 1 := Nat.mul_left_cancel (by norm_num) h
    exact Fin.ext (Nat.add_right_cancel h2)
  have hL : (∑ i : Fin 12, (if 0 < β.count (2 * ((i : ℕ) + 1)) then F i else 0))
      = ∑ i ∈ s, F i := by
    have h1 : (∑ i : Fin 12, (if 0 < β.count (2 * ((i : ℕ) + 1)) then F i else 0))
        = ∑ i : Fin 12, (if i ∈ s then F i else 0) :=
      Finset.sum_congr rfl (fun i _ => if_congr (hmem i) rfl rfl)
    rw [h1, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have himage : β.dedup.toFinset
      = s.image (fun i : Fin 12 => 2 * ((i : ℕ) + 1)) := by
    ext d
    simp only [List.mem_toFinset, Finset.mem_image]
    constructor
    · intro hd
      obtain ⟨i, hi⟩ := hβ d (List.mem_dedup.mp hd)
      refine ⟨i, ?_, hi.symm⟩
      rw [hs, Finset.mem_filter]
      exact ⟨Finset.mem_univ i, hi ▸ hd⟩
    · rintro ⟨i, hi, rfl⟩
      rw [hs] at hi
      exact (Finset.mem_filter.mp hi).2
  have hR : (β.dedup.map G).sum = ∑ i ∈ s, F i := by
    rw [← List.sum_toFinset G (List.nodup_dedup β), himage, Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun i _ => hGF i)
  exact hL.trans hR.symm

end Commons.NumberTheory.KroneckerSums