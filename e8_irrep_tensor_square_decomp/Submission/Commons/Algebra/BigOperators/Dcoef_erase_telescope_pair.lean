import Mathlib

namespace Commons.Algebra.BigOperators

open scoped BigOperators

private def Dfun {M : Type*} [AddCommGroup M] [DecidableEq M] (S : Finset M) (x : M) : ℤ :=
  ∑ T ∈ S.powerset, (if (∑ a ∈ T, a) = x then (-1 : ℤ) ^ T.card else 0)

private lemma Dfun_insert {M : Type*} [AddCommGroup M] [DecidableEq M]
    (S : Finset M) (β : M) (hβ : β ∉ S) (x : M) :
    Dfun (insert β S) x = Dfun S x - Dfun S (x - β) := by
  unfold Dfun
  rw [Finset.sum_powerset_insert hβ]
  have h2 : (∑ T ∈ S.powerset,
        (if (∑ a ∈ insert β T, a) = x then (-1 : ℤ) ^ (insert β T).card else 0))
      = -(∑ T ∈ S.powerset,
        (if (∑ a ∈ T, a) = x - β then (-1 : ℤ) ^ T.card else 0)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hβT : β ∉ T := fun h => hβ (hT h)
    rw [Finset.sum_insert hβT, Finset.card_insert_of_notMem hβT]
    have hcond : (β + ∑ a ∈ T, a = x) ↔ (∑ a ∈ T, a = x - β) := by
      constructor
      · intro h; rw [← h]; abel
      · intro h; rw [h]; abel
    have hrw : (-1 : ℤ) ^ (T.card + 1) = -((-1 : ℤ) ^ T.card) := by
      rw [pow_succ]; ring
    rw [if_congr hcond hrw rfl]
    by_cases hc : (∑ a ∈ T, a) = x - β
    · simp [hc]
    · simp [hc]
  rw [h2]
  ring

private lemma Dfun_eq_zero_of_ht_neg {M : Type*} [AddCommGroup M] [DecidableEq M]
    (ht : M →+ ℤ) (L : Finset M) (hL : ∀ a ∈ L, 1 ≤ ht a)
    (S : Finset M) (hS : ∀ a ∈ S, a ∈ L) (x : M) (hx : ht x < 0) :
    Dfun S x = 0 := by
  unfold Dfun
  apply Finset.sum_eq_zero
  intro T hT
  rw [Finset.mem_powerset] at hT
  by_cases h : (∑ a ∈ T, a) = x
  · exfalso
    have hht : ht x = ∑ a ∈ T, ht a := by
      rw [← h]; exact map_sum ht (fun a => a) T
    have hnn : 0 ≤ ∑ a ∈ T, ht a :=
      Finset.sum_nonneg (fun a ha => le_trans zero_le_one (hL a (hS a (hT ha))))
    linarith
  · simp [h]

private lemma Dfun_telescope {M : Type*} [AddCommGroup M] [DecidableEq M]
    (ht : M →+ ℤ) (L : Finset M) (hL : ∀ a ∈ L, 1 ≤ ht a)
    (β : M) (hβ : β ∈ L) (ν : M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Dfun L (ν - n • β)
      = Dfun (L.erase β) (ν - β) - Dfun (L.erase β) (ν - (N + 1) • β) := by
  have hkey : ∀ k : ℕ, (ν - k • β) - β = ν - (k + 1) • β := by
    intro k
    rw [add_nsmul, one_smul]
    abel
  induction N with
  | zero =>
    simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    rw [ih]
    have hins : Dfun L (ν - (N + 1) • β)
        = Dfun (L.erase β) (ν - (N + 1) • β) - Dfun (L.erase β) ((ν - (N + 1) • β) - β) := by
      have h := Dfun_insert (L.erase β) β (Finset.notMem_erase β L) (ν - (N + 1) • β)
      rwa [Finset.insert_erase hβ] at h
    rw [hins, hkey (N + 1)]
    abel

private lemma Dcoef_erase_telescope_aux {M : Type*} [AddCommGroup M] [DecidableEq M]
    (ht : M →+ ℤ) (L : Finset M) (hL : ∀ a ∈ L, 1 ≤ ht a)
    (β : M) (hβ : β ∈ L) (N : ℕ) (ν : M) (hN : (ht ν).toNat ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, ∑ T ∈ L.powerset,
        (if (∑ a ∈ T, a) = ν - n • β then (-1 : ℤ) ^ T.card else 0))
      = ∑ T ∈ (L.erase β).powerset,
          (if (∑ a ∈ T, a) = ν - β then (-1 : ℤ) ^ T.card else 0) := by
  show ∑ n ∈ Finset.Icc 1 N, Dfun L (ν - n • β) = Dfun (L.erase β) (ν - β)
  rw [Dfun_telescope ht L hL β hβ ν N]
  have hz : Dfun (L.erase β) (ν - (N + 1) • β) = 0 := by
    apply Dfun_eq_zero_of_ht_neg ht L hL (L.erase β)
      (fun a ha => Finset.mem_of_mem_erase ha) (ν - (N + 1) • β) ?_
    have hle : ht ν ≤ (N : ℤ) := Int.toNat_le.mp hN
    have hb : (1 : ℤ) ≤ ht β := hL β hβ
    have hcast : ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by push_cast; ring
    have hge : ((N + 1 : ℕ) : ℤ) ≤ (N + 1) • ht β := by
      rw [nsmul_eq_mul]
      have : ((N + 1 : ℕ) : ℤ) * (1 : ℤ) ≤ ((N + 1 : ℕ) : ℤ) * ht β :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      simpa using this
    rw [map_sub, map_nsmul]
    linarith
  rw [hz, sub_zero]

/-- Two-fold telescoping identity for Weyl-denominator coefficients (obtained by applying
`Commons.Algebra.BigOperators.Dcoef_erase_telescope` twice).  With `D(ν)` as in that lemma, if
`β ∈ L`, `β' ∈ L.erase β` and `(ht ν).toNat ≤ N` then
`∑_{n,m=1}^{N} D(ν - n•β - m•β') = D''(ν - β - β')`
where `D''` is the functional for `(L.erase β).erase β'`. -/
theorem Dcoef_erase_telescope_pair {M : Type*} [AddCommGroup M] [DecidableEq M]
    (ht : M →+ ℤ) (L : Finset M) (hL : ∀ a ∈ L, 1 ≤ ht a)
    (β β' : M) (hβ : β ∈ L) (hβ' : β' ∈ L.erase β) (N : ℕ) (ν : M)
    (hN : (ht ν).toNat ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, ∑ T ∈ L.powerset,
        (if (∑ a ∈ T, a) = ν - n • β - m • β' then (-1 : ℤ) ^ T.card else 0))
      = ∑ T ∈ ((L.erase β).erase β').powerset,
          (if (∑ a ∈ T, a) = ν - β - β' then (-1 : ℤ) ^ T.card else 0) := by
  show (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, Dfun L (ν - n • β - m • β'))
      = Dfun ((L.erase β).erase β') (ν - β - β')
  have hL' : ∀ a ∈ L.erase β, 1 ≤ ht a := fun a ha => hL a (Finset.mem_of_mem_erase ha)
  have hβ'' : β' ∈ L := Finset.mem_of_mem_erase hβ'
  have hβ'ht : (1 : ℤ) ≤ ht β' := hL β' hβ''
  calc
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, Dfun L (ν - n • β - m • β')
        = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, Dfun L (ν - n • β - m • β') :=
          Finset.sum_comm
    _ = ∑ m ∈ Finset.Icc 1 N, Dfun (L.erase β) ((ν - m • β') - β) := by
          apply Finset.sum_congr rfl
          intro m _
          have hx : (ht (ν - m • β')).toNat ≤ N := by
            apply le_trans _ hN
            apply Int.toNat_le_toNat
            rw [map_sub, map_nsmul]
            have : (0 : ℤ) ≤ m • ht β' := by
              apply nsmul_nonneg
              linarith
            linarith
          rw [show (∑ n ∈ Finset.Icc 1 N, Dfun L (ν - n • β - m • β'))
              = ∑ n ∈ Finset.Icc 1 N, Dfun L ((ν - m • β') - n • β) from by
                apply Finset.sum_congr rfl
                intro n _
                congr 1
                abel]
          exact Dcoef_erase_telescope_aux ht L hL β hβ N (ν - m • β') hx
    _ = ∑ m ∈ Finset.Icc 1 N, Dfun (L.erase β) ((ν - β) - m • β') := by
          apply Finset.sum_congr rfl
          intro m _
          congr 1
          abel
    _ = Dfun ((L.erase β).erase β') (ν - β - β') := by
          apply Dcoef_erase_telescope_aux ht (L.erase β) hL' β' hβ' N (ν - β) ?_
          apply le_trans _ hN
          apply Int.toNat_le_toNat
          rw [map_sub]
          have hb : (1 : ℤ) ≤ ht β := hL β hβ
          linarith

end Commons.Algebra.BigOperators
