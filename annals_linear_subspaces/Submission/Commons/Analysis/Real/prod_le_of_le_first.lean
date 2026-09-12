import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

namespace Commons.Analysis.Real

/-- For a finite set `s` and a lower bound `n ≥ 0`, the product of `f` over `s` is at least
`n ^ #s`.  (Real-valued version of `Finset.pow_card_le_prod`, which requires a multiplicative
ordered monoid with `MulLeftMono`; this version only needs `PosMulMono`.) -/
theorem pow_card_le_prod_of_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) {n : ℝ} (hn : 0 ≤ n)
    (h : ∀ x ∈ s, n ≤ f x) : n ^ s.card ≤ s.prod f := by
  calc n ^ s.card = s.prod (fun _ => n) := (Finset.prod_const n).symm
    _ ≤ s.prod f := Finset.prod_le_prod (fun i _ => hn) h

/-- The number of elements of `Fin d` whose value is `< m` is `m`, for `m ≤ d`. -/
theorem card_filter_univ_fin_val_lt (d m : ℕ) (hm : m ≤ d) :
    (Finset.univ.filter (fun i : Fin d => i.val < m)).card = m := by
  have h : (Finset.univ.filter (fun i : Fin d => i.val < m)).card =
      (Finset.range m).card := by
    refine Finset.card_bij
      (fun (i : Fin d) (_ : i ∈ Finset.univ.filter (fun i : Fin d => i.val < m)) => i.val)
      ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij
      exact Fin.ext hij
    · intro b hb
      refine ⟨⟨b, lt_of_lt_of_le (Finset.mem_range.mp hb) hm⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hb⟩
  rwa [Finset.card_range] at h

theorem prod_le_of_le_first {d : ℕ} (lam : Fin d → ℝ) {c C : ℝ} (hc : 0 < c) (hmin : ∀ i, c ≤ lam i) (hmono : Monotone lam) (hprod : ∏ i : Fin d, lam i ≤ C) (k : Fin d) : lam k ^ (d - k.val) * c ^ k.val ≤ C := by
  have hmd : k.val ≤ d := le_of_lt k.isLt
  have hkpos : 0 ≤ lam k := le_of_lt (lt_of_lt_of_le hc (hmin k))
  have hlamnonneg : ∀ i : Fin d, 0 ≤ lam i := fun i => le_of_lt (lt_of_lt_of_le hc (hmin i))
  have ht : (Finset.univ.filter (fun i : Fin d => i.val < k.val)).card = k.val :=
    card_filter_univ_fin_val_lt d k.val hmd
  have hs : (Finset.univ.filter (fun i : Fin d => ¬ i.val < k.val)).card = d - k.val := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d)))
      (p := fun i : Fin d => i.val < k.val)
    rw [ht, Finset.card_univ, Fintype.card_fin] at h
    omega
  have h1 : c ^ k.val ≤ (Finset.univ.filter (fun i : Fin d => i.val < k.val)).prod lam := by
    have h := pow_card_le_prod_of_nonneg
      (Finset.univ.filter (fun i : Fin d => i.val < k.val)) lam (le_of_lt hc) (fun i _ => hmin i)
    rwa [ht] at h
  have h2 : lam k ^ (d - k.val) ≤
      (Finset.univ.filter (fun i : Fin d => ¬ i.val < k.val)).prod lam := by
    have h := pow_card_le_prod_of_nonneg
      (Finset.univ.filter (fun i : Fin d => ¬ i.val < k.val)) lam hkpos
      (fun i hi => hmono (Fin.le_iff_val_le_val.mpr (by have := (Finset.mem_filter.mp hi).2; omega)))
    rwa [hs] at h
  have hsplit : (∏ i : Fin d, lam i) =
      (Finset.univ.filter (fun i : Fin d => i.val < k.val)).prod lam *
      (Finset.univ.filter (fun i : Fin d => ¬ i.val < k.val)).prod lam := by
    have h := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin d))
      (fun i : Fin d => i.val < k.val) lam
    simpa using h.symm
  calc lam k ^ (d - k.val) * c ^ k.val
      = c ^ k.val * lam k ^ (d - k.val) := mul_comm _ _
    _ ≤ (Finset.univ.filter (fun i : Fin d => i.val < k.val)).prod lam *
        (Finset.univ.filter (fun i : Fin d => ¬ i.val < k.val)).prod lam :=
        mul_le_mul h1 h2 (pow_nonneg hkpos _)
          (Finset.prod_nonneg (fun i _ => hlamnonneg i))
    _ = ∏ i : Fin d, lam i := hsplit.symm
    _ ≤ C := hprod

end Commons.Analysis.Real