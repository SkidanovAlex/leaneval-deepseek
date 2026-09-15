import Mathlib

namespace Commons.LinearAlgebra.ZMod

open Finset

/-- Over a field `k`, if `L ≠ 0` and `L'` is not a scalar multiple of `L`, then some `2 × 2`
minor of the matrix with rows `L`, `L'` is nonzero. -/
lemma exists_ne_minor_of_not_smul {k : Type*} [Field k] {t : ℕ} {L L' : Fin t → k}
    (hL : L ≠ 0) (hne : ∀ c : k, L' ≠ c • L) :
    ∃ i j : Fin t, i ≠ j ∧ L i * L' j - L j * L' i ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, L i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hL (funext h)
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  refine hne (L' i / L i) ?_
  have h0 : ∀ j, L i * L' j = L j * L' i := by
    intro j
    by_cases hj : j = i
    · subst hj; ring
    · exact sub_eq_zero.mp (h i j (Ne.symm hj))
  funext j
  have hmul : L' j * L i = L' i * L j := by
    rw [mul_comm (L' j) (L i), h0 j, mul_comm (L j) (L' i)]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, eq_div_iff hi]
  exact hmul

/-- The number of solutions `x : Fin t → ZMod p` of a pair of independent affine linear
equations `∑ j, L j * x j = b`, `∑ j, L' j * x j = b'` is at most `p ^ (t - 2)`: the map
`x ↦ (∑ j, L j * x j, ∑ j, L' j * x j) : (ZMod p)^t → (ZMod p)^2` is surjective when `L` and
`L'` are linearly independent, so each fibre has cardinality `p ^ (t-2)`. -/
theorem pair_affine_hyperplanes_card {p : ℕ} [Fact p.Prime] {t : ℕ} (ht : 2 ≤ t)
    (L L' : Fin t → ZMod p) (hL : L ≠ 0) (hL' : L' ≠ 0)
    (hne : ∀ c : ZMod p, L' ≠ c • L) (b b' : ZMod p) :
    ((Finset.univ : Finset (Fin t → ZMod p)).filter
      (fun x => (∑ j, L j * x j = b) ∧ (∑ j, L' j * x j = b'))).card ≤ p ^ (t - 2) := by
  classical
  have _hL' : L' ≠ 0 := hL'
  obtain ⟨i, j, hij, hD⟩ := exists_ne_minor_of_not_smul (k := ZMod p) hL hne
  set S : Finset (Fin t → ZMod p) :=
    (Finset.univ : Finset (Fin t → ZMod p)).filter
      (fun x => (∑ j, L j * x j = b) ∧ (∑ j, L' j * x j = b')) with hSdef
  let f : (Fin t → ZMod p) → ({k : Fin t // k ≠ i ∧ k ≠ j} → ZMod p) := fun x k => x k.1
  have hkey : ∀ x y : Fin t → ZMod p, x ∈ S → y ∈ S → f x = f y → x = y := by
    intro x y hx hy hxy
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have hxy' : ∀ k : Fin t, k ≠ i → k ≠ j → x k = y k :=
      fun k h1 h2 => congrFun hxy ⟨k, h1, h2⟩
    have hsumL : ∑ k, L k * (x k - y k) = 0 := by
      have heq : ∑ k, L k * (x k - y k) = ∑ k, L k * x k - ∑ k, L k * y k := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => mul_sub (L k) (x k) (y k))
      rw [heq, hx.1, hy.1, sub_self]
    have hsumL' : ∑ k, L' k * (x k - y k) = 0 := by
      have heq : ∑ k, L' k * (x k - y k) = ∑ k, L' k * x k - ∑ k, L' k * y k := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => mul_sub (L' k) (x k) (y k))
      rw [heq, hx.2, hy.2, sub_self]
    have hLij : L i * (x i - y i) + L j * (x j - y j) = 0 := by
      have hsingle :
          ∑ k ∈ ({i, j} : Finset (Fin t)), L k * (x k - y k) = ∑ k, L k * (x k - y k) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        rw [hxy' k hk.1 hk.2, sub_self, mul_zero]
      calc L i * (x i - y i) + L j * (x j - y j)
          = ∑ k ∈ ({i, j} : Finset (Fin t)), L k * (x k - y k) :=
            (Finset.sum_pair (f := fun k => L k * (x k - y k)) hij).symm
        _ = ∑ k, L k * (x k - y k) := hsingle
        _ = 0 := hsumL
    have hL'ij : L' i * (x i - y i) + L' j * (x j - y j) = 0 := by
      have hsingle :
          ∑ k ∈ ({i, j} : Finset (Fin t)), L' k * (x k - y k) = ∑ k, L' k * (x k - y k) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        rw [hxy' k hk.1 hk.2, sub_self, mul_zero]
      calc L' i * (x i - y i) + L' j * (x j - y j)
          = ∑ k ∈ ({i, j} : Finset (Fin t)), L' k * (x k - y k) :=
            (Finset.sum_pair (f := fun k => L' k * (x k - y k)) hij).symm
        _ = ∑ k, L' k * (x k - y k) := hsingle
        _ = 0 := hsumL'
    have hu : x i - y i = 0 := by
      have hDmul : (L i * L' j - L j * L' i) * (x i - y i) = 0 := by
        have hre : (L i * L' j - L j * L' i) * (x i - y i)
            = L' j * (L i * (x i - y i) + L j * (x j - y j))
              - L j * (L' i * (x i - y i) + L' j * (x j - y j)) := by ring
        rw [hre, hLij, hL'ij]
        ring
      rcases mul_eq_zero.mp hDmul with h | h
      · exact absurd h hD
      · exact h
    have hv : x j - y j = 0 := by
      have hDmul : (L i * L' j - L j * L' i) * (x j - y j) = 0 := by
        have hre : (L i * L' j - L j * L' i) * (x j - y j)
            = L i * (L' i * (x i - y i) + L' j * (x j - y j))
              - L' i * (L i * (x i - y i) + L j * (x j - y j)) := by ring
        rw [hre, hLij, hL'ij]
        ring
      rcases mul_eq_zero.mp hDmul with h | h
      · exact absurd h hD
      · exact h
    funext k
    by_cases h1 : k = i
    · subst h1; exact sub_eq_zero.mp hu
    by_cases h2 : k = j
    · subst h2; exact sub_eq_zero.mp hv
    · exact hxy' k h1 h2
  have hinj : Set.InjOn f ↑S := fun x hx y hy hxy => hkey x y hx hy hxy
  have hcardS : Fintype.card {x : Fin t → ZMod p // x ∈ S} = S.card :=
    Fintype.card_ofFinset S (fun x => Iff.rfl)
  have hle : S.card ≤ Fintype.card ({k : Fin t // k ≠ i ∧ k ≠ j} → ZMod p) := by
    rw [← hcardS]
    apply Fintype.card_le_of_injective
      (fun (x : {x : Fin t → ZMod p // x ∈ S})
           (k : {k : Fin t // k ≠ i ∧ k ≠ j}) => x.1 k.1)
    intro x y hxy
    apply Subtype.ext
    exact hinj x.2 y.2 (funext fun k => congrFun hxy k)
  have hcard_sub : Fintype.card {k : Fin t // k ≠ i ∧ k ≠ j} = t - 2 := by
    rw [Fintype.card_subtype]
    have hfilt : (Finset.univ.filter (fun k : Fin t => k ≠ i ∧ k ≠ j)) =
        (Finset.univ.erase i).erase j := by
      rw [← Finset.filter_filter (fun k : Fin t => k ≠ i) (fun k : Fin t => k ≠ j),
          Finset.filter_ne' Finset.univ i,
          Finset.filter_ne' (Finset.univ.erase i) j]
    rw [hfilt, Finset.card_erase_of_mem
          (show j ∈ (Finset.univ : Finset (Fin t)).erase i from
            Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  calc S.card ≤ Fintype.card ({k : Fin t // k ≠ i ∧ k ≠ j} → ZMod p) := hle
    _ = p ^ (t - 2) := by rw [Fintype.card_fun, ZMod.card, hcard_sub]

end Commons.LinearAlgebra.ZMod
