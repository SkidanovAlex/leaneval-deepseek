import Mathlib

namespace Commons.Algebra.BigOperators

open scoped BigOperators

/-- The Weyl-denominator coefficient functional attached to a finite set `S` of vectors:
`D_S(μ) = ∑_{T ⊆ S} (-1)^{|T|} · [∑_{a ∈ T} a = μ]`. -/
def Dcoef {M : Type*} [AddCommGroup M] [DecidableEq M] (S : Finset M) (μ : M) : ℤ :=
  ∑ T ∈ S.powerset, (if (∑ a ∈ T, a) = μ then (-1 : ℤ) ^ T.card else 0)

/-- Splitting the coefficient functional along an element of the finite set:
`D_{insert β S}(μ) = D_S(μ) - D_S(μ - β)` when `β ∉ S`. -/
theorem Dcoef_insert {M : Type*} [AddCommGroup M] [DecidableEq M]
    (S : Finset M) (β : M) (hβ : β ∉ S) (μ : M) :
    Dcoef (insert β S) μ = Dcoef S μ - Dcoef S (μ - β) := by
  unfold Dcoef
  rw [Finset.sum_powerset_insert hβ]
  have hB : (∑ T ∈ S.powerset,
        (if (∑ a ∈ insert β T, a) = μ then (-1 : ℤ) ^ (insert β T).card else 0))
      = -(∑ T ∈ S.powerset, (if (∑ a ∈ T, a) = μ - β then (-1 : ℤ) ^ T.card else 0)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hβT : β ∉ T := fun h => hβ (hT h)
    rw [Finset.sum_insert hβT, Finset.card_insert_of_notMem hβT]
    by_cases hc : (∑ a ∈ T, a) = μ - β
    · rw [if_pos hc, if_pos (by rw [hc, add_sub_cancel])]
      rw [pow_succ]; ring
    · have hcL : ¬ (β + (∑ a ∈ T, a) = μ) :=
        fun h => hc (by rw [eq_sub_iff_add_eq]; rwa [add_comm] at h)
      rw [if_neg hcL, if_neg hc]
      ring
  rw [hB]
  abel

/-- The coefficient functional vanishes on weights of strictly negative height. -/
theorem Dcoef_eq_zero_of_ht_neg {M : Type*} [AddCommGroup M] [DecidableEq M]
    (ht : M →+ ℤ) (S : Finset M) (hS : ∀ a ∈ S, 0 ≤ ht a) (μ : M) (hμ : ht μ < 0) :
    Dcoef S μ = 0 := by
  unfold Dcoef
  apply Finset.sum_eq_zero
  intro T hT
  rw [Finset.mem_powerset] at hT
  apply if_neg
  intro hcond
  have hsum : 0 ≤ ∑ a ∈ T, ht a := Finset.sum_nonneg (fun a ha => hS a (hT ha))
  have hthis : ht (∑ a ∈ T, a) = ∑ a ∈ T, ht a := map_sum ht (fun a => a) T
  rw [hcond] at hthis
  linarith

/-- Telescoping identity `∑_{n=1}^{N} (G n - G (n+1)) = G 1 - G (N+1)`. -/
lemma sum_Icc_one_sub_shift (G : ℕ → ℤ) : ∀ N : ℕ,
    (∑ n ∈ Finset.Icc 1 N, (G n - G (n + 1))) = G 1 - G (N + 1)
  | 0 => by simp
  | (N + 1) => by
      have h := Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega)
        (fun k => G k - G (k + 1))
      rw [h, sum_Icc_one_sub_shift G N]
      ring

/-- Telescoping identity for Weyl-denominator coefficients.  Let `L` be a finset of vectors in an
additive commutative group, `ht` an additive height with `1 ≤ ht a` for `a ∈ L`, and let
`D(ν) = ∑_{T ⊆ L} (-1)^{|T|} [∑_{a ∈ T} a = ν]`.  If `β ∈ L` and `(ht ν).toNat ≤ N` then
`∑_{n=1}^{N} D(ν - n•β) = D'(ν - β)` where `D'` is the same functional for `L.erase β`. -/
theorem Dcoef_erase_telescope {M : Type*} [AddCommGroup M] [DecidableEq M]
    (ht : M →+ ℤ) (L : Finset M) (hL : ∀ a ∈ L, 1 ≤ ht a)
    (β : M) (hβ : β ∈ L) (N : ℕ) (ν : M) (hN : (ht ν).toNat ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, ∑ T ∈ L.powerset,
        (if (∑ a ∈ T, a) = ν - n • β then (-1 : ℤ) ^ T.card else 0))
      = ∑ T ∈ (L.erase β).powerset,
          (if (∑ a ∈ T, a) = ν - β then (-1 : ℤ) ^ T.card else 0) := by
  change (∑ n ∈ Finset.Icc 1 N, Dcoef L (ν - n • β)) = Dcoef (L.erase β) (ν - β)
  have hβS : β ∉ L.erase β := Finset.notMem_erase β L
  have hL_eq : insert β (L.erase β) = L := Finset.insert_erase hβ
  have step : ∀ n : ℕ, Dcoef L (ν - n • β)
      = Dcoef (L.erase β) (ν - n • β) - Dcoef (L.erase β) (ν - (n + 1) • β) := by
    intro n
    rw [show Dcoef L (ν - n • β) = Dcoef (insert β (L.erase β)) (ν - n • β) by rw [hL_eq]]
    rw [Dcoef_insert (L.erase β) β hβS (ν - n • β)]
    congr 1
    rw [succ_nsmul, sub_sub]
  have hzero : Dcoef (L.erase β) (ν - (N + 1) • β) = 0 := by
    apply Dcoef_eq_zero_of_ht_neg ht (L.erase β)
    · intro a ha
      exact le_trans zero_le_one (hL a (Finset.mem_of_mem_erase ha))
    · rw [map_sub, map_nsmul]
      have hν : ht ν ≤ (N : ℤ) := Int.toNat_le.mp hN
      have hβ1 : (1 : ℤ) ≤ ht β := hL β hβ
      have hkey : (N : ℤ) + 1 ≤ (N + 1) • ht β := by
        rw [nsmul_eq_mul]
        have h0 : (0 : ℤ) ≤ ((N + 1 : ℕ) : ℤ) := by positivity
        calc (N : ℤ) + 1 = ((N + 1 : ℕ) : ℤ) * 1 := by push_cast; ring
          _ ≤ ((N + 1 : ℕ) : ℤ) * ht β := mul_le_mul_of_nonneg_left hβ1 h0
      linarith
  rw [show (∑ n ∈ Finset.Icc 1 N, Dcoef L (ν - n • β))
        = ∑ n ∈ Finset.Icc 1 N,
            (Dcoef (L.erase β) (ν - n • β) - Dcoef (L.erase β) (ν - (n + 1) • β))
        from Finset.sum_congr rfl (fun n _ => step n)]
  rw [sum_Icc_one_sub_shift]
  rw [one_nsmul, hzero, sub_zero]

end Commons.Algebra.BigOperators
