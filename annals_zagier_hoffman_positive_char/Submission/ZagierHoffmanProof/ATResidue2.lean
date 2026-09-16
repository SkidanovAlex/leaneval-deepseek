import Submission.ZagierHoffmanProof.ATIndex

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# The residue bound and the reduced-index identity for the descent

This file develops the arithmetic that the increment lemma
`atCoeff (atIndex n (N + e_k)) = R_(n-1-k)^(q^k) * atCoeff (atIndex n N)`
needs (see `Submission/PLAN.md`, SESSION 296):

* `residue_bound`: for a residue vector `res` of the descent from `atIndex n N` (with
  `∑ N_i ≤ q - 2`) and any `1 ≤ k ≤ n-1`, one has `S_res + q^k ≤ atIndex n N`;
* `atIndex_shiftShape`: `atIndex n (N + e_k) = atIndex n N - q^k` for `k < n`;
* `reduce_eq`: the reduced index `(atIndex n N - S_res)/q` is `atIndex (n-1) M` for the tail shape
  `M_j = N_{j+1} + res_{j+1}`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The shape obtained from `N` by replacing the `k`-th digit by `c`. -/
def shiftShape (N : ℕ → ℕ) (k c : ℕ) : ℕ → ℕ := fun i => N i + if i = k then c else 0

@[simp] lemma shiftShape_apply (N : ℕ → ℕ) (k c i : ℕ) :
    shiftShape N k c i = N i + if i = k then c else 0 := rfl

@[simp] lemma shiftShape_zero (N : ℕ → ℕ) (k : ℕ) : shiftShape N k 0 = N := by
  funext i; simp [shiftShape]

lemma shiftShape_one (N : ℕ → ℕ) (k : ℕ) :
    shiftShape N k 1 = fun i => N i + if i = k then 1 else 0 := rfl

omit [Field F] [Finite F] in
lemma sum_shiftShape (n : ℕ) (N : ℕ → ℕ) (k c : ℕ) :
    (∑ i ∈ Finset.range n, shiftShape N k c i)
      = (∑ i ∈ Finset.range n, N i) + (if k < n then c else 0) := by
  rw [Finset.sum_congr rfl (fun i _ => shiftShape_apply N k c i), Finset.sum_add_distrib,
    Finset.sum_ite_eq']
  simp

omit [Field F] [Finite F] in
lemma sum_shiftShape_weighted (n : ℕ) (N : ℕ → ℕ) (k c : ℕ) :
    (∑ i ∈ Finset.range n, shiftShape N k c i * Nat.card F ^ i)
      = (∑ i ∈ Finset.range n, N i * Nat.card F ^ i)
        + (if k < n then c * Nat.card F ^ k else 0) := by
  have h : ∀ i : ℕ, shiftShape N k c i * Nat.card F ^ i
      = N i * Nat.card F ^ i + (if i = k then c * Nat.card F ^ i else 0) := by
    intro i
    rw [shiftShape_apply, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- **The index of a shifted shape.** -/
lemma atIndex_shiftShape (n : ℕ) (N : ℕ → ℕ) (k c : ℕ) (hk : k < n)
    (h : (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) + c * Nat.card F ^ k
      ≤ Nat.card F ^ n - 1) :
    atIndex F n (shiftShape N k c) = atIndex F n N - c * Nat.card F ^ k := by
  rw [atIndex, atIndex, sum_shiftShape_weighted F n N k c, if_pos hk, Nat.sub_sub]
  omega

/-- The index of a shifted shape, in the "one more digit" form. -/
lemma atIndex_shiftShape_one (n : ℕ) (N : ℕ → ℕ) (k : ℕ) (hk : k < n)
    (h : (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) + Nat.card F ^ k
      ≤ Nat.card F ^ n - 1) :
    atIndex F n (shiftShape N k 1) = atIndex F n N - Nat.card F ^ k := by
  rw [atIndex_shiftShape F n N k 1 hk (by simpa using h), one_mul]

/-- The tail sum of a residue vector is bounded by the lowest digit of the shape. -/
lemma tail_sum_le (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) (m : ℕ) (res : Fin (m + 1) → ℕ)
    (hres : res ∈ residueSet F (atIndex F n N) (m + 1)) :
    (∑ i : Fin m, res i.succ) ≤ N 0 := by
  obtain ⟨-, -, hrv, hnc⟩ := (mem_residueSet F).mp hres
  have hzero := residue_zero_entry F n (by omega) N hN m res hres
  have hsum := sum_le_card_sub_one_of_noCarryVec F hrv hnc
  rw [Fin.sum_univ_succ] at hsum
  rw [hzero] at hsum
  have hN0 : N 0 ≤ Nat.card F - 1 :=
    le_trans (Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))) hN
  omega

/-- **The weighted tail bound for the upper digits of the shape.** -/
lemma Tn_le (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 2) :
    (∑ i ∈ Finset.range (n - 1), N (i + 1) * Nat.card F ^ i)
      ≤ (Nat.card F - 2 - N 0) * Nat.card F ^ (n - 2) := by
  have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
  have hstep : ∀ i ∈ Finset.range (n - 1),
      N (i + 1) * Nat.card F ^ i ≤ N (i + 1) * Nat.card F ^ (n - 2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact Nat.mul_le_mul_left _ (pow_le_pow_right₀ hq1 (by omega))
  have hsum2 : (∑ i ∈ Finset.range (n - 1), N (i + 1)) ≤ Nat.card F - 2 - N 0 := by
    have hN0 : N 0 ≤ Nat.card F - 2 :=
      le_trans (Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))) hN
    have hsplit := sum_range_shift_plain n (by omega) N
    omega
  calc (∑ i ∈ Finset.range (n - 1), N (i + 1) * Nat.card F ^ i)
      ≤ ∑ i ∈ Finset.range (n - 1), N (i + 1) * Nat.card F ^ (n - 2) := Finset.sum_le_sum hstep
    _ = (∑ i ∈ Finset.range (n - 1), N (i + 1)) * Nat.card F ^ (n - 2) := by rw [Finset.sum_mul]
    _ ≤ (Nat.card F - 2 - N 0) * Nat.card F ^ (n - 2) := Nat.mul_le_mul_right _ hsum2

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- ★★ **The residue bound**: every residue vector of the descent from `atIndex n N` (with
`∑ N_i ≤ q - 2`) is small enough that `q^k` can be subtracted from the index without changing it. -/
theorem residue_bound (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 2)
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) (m : ℕ) (res : Fin (m + 1) → ℕ)
    (hres : res ∈ residueSet F (atIndex F n N) (m + 1)) :
    (∑ i : Fin (m + 1), res i * Nat.card F ^ (i : ℕ)) + Nat.card F ^ k ≤ atIndex F n N := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hq1 : 1 ≤ Nat.card F := by omega
  have hN1 : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1 := by omega
  have hN0 : N 0 ≤ Nat.card F - 2 :=
    le_trans (Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))) hN
  set Tn := ∑ i ∈ Finset.range (n - 1), N (i + 1) * Nat.card F ^ i with hTn'
  set Tr := ∑ i : Fin m, res i.succ * Nat.card F ^ (i : ℕ) with hTr'
  have hTn : Tn ≤ (Nat.card F - 2 - N 0) * Nat.card F ^ (n - 2) := Tn_le F n hn N hN
  have hTr : Tr ≤ N 0 * Nat.card F ^ (n - 2) := by
    have h1 := tail_weighted_le F n hn N m res hres
    have h2 := tail_sum_le F n hn N hN1 m res hres
    rw [← hTr'] at h1
    refine le_trans h1 ?_
    calc Nat.card F ^ (n - 2) * (∑ i : Fin m, res i.succ)
        ≤ Nat.card F ^ (n - 2) * N 0 := Nat.mul_le_mul_left _ h2
      _ = N 0 * Nat.card F ^ (n - 2) := mul_comm _ _
  have hTnTr : Tn + Tr ≤ (Nat.card F - 2) * Nat.card F ^ (n - 2) := by
    have h1 : Tn + Tr ≤ ((Nat.card F - 2 - N 0) + N 0) * Nat.card F ^ (n - 2) := by
      rw [add_mul]
      exact Nat.add_le_add hTn hTr
    rwa [Nat.sub_add_cancel hN0] at h1
  have hX : atIndex F n N + (N 0 + 1) + Nat.card F * Tn = Nat.card F ^ n :=
    atIndex_add_form F n (by omega) N hN1
  have hX2 : atIndex F n N + ((N 0 + 1) + Nat.card F * Tn) = Nat.card F ^ n := by
    simpa only [add_assoc] using hX
  have hS : (∑ i : Fin (m + 1), res i * Nat.card F ^ (i : ℕ)) = res 0 + Nat.card F * Tr := by
    rw [sum_fin_succ_shift F res, ← hTr']
  have hres0 : res 0 = Nat.card F - 1 - N 0 := residue_zero_entry F n (by omega) N hN1 m res hres
  have hstep1 : res 0 + (N 0 + 1) = Nat.card F := by rw [hres0]; omega
  have hkey : (∑ i : Fin (m + 1), res i * Nat.card F ^ (i : ℕ)) + Nat.card F ^ k
      + ((N 0 + 1) + Nat.card F * Tn) ≤ Nat.card F ^ n := by
    have hrearr : (res 0 + Nat.card F * Tr) + Nat.card F ^ k + ((N 0 + 1) + Nat.card F * Tn)
        = Nat.card F + Nat.card F ^ k + Nat.card F * (Tn + Tr) := by
      calc (res 0 + Nat.card F * Tr) + Nat.card F ^ k + ((N 0 + 1) + Nat.card F * Tn)
          = (res 0 + (N 0 + 1)) + Nat.card F ^ k
              + (Nat.card F * Tr + Nat.card F * Tn) := by ring
        _ = Nat.card F + Nat.card F ^ k + Nat.card F * (Tr + Tn) := by
              rw [hstep1, ← Nat.mul_add]
        _ = Nat.card F + Nat.card F ^ k + Nat.card F * (Tn + Tr) := by rw [add_comm Tr Tn]
    rw [hS, hrearr]
    have hqTnTr : Nat.card F * (Tn + Tr) ≤ (Nat.card F - 2) * Nat.card F ^ (n - 1) := by
      calc Nat.card F * (Tn + Tr) ≤ Nat.card F * ((Nat.card F - 2) * Nat.card F ^ (n - 2)) :=
            Nat.mul_le_mul_left _ hTnTr
        _ = (Nat.card F - 2) * Nat.card F ^ (n - 1) := by
            rw [mul_comm (Nat.card F) ((Nat.card F - 2) * Nat.card F ^ (n - 2)), mul_assoc,
              ← pow_succ, show n - 2 + 1 = n - 1 from by omega]
    have hpowk : Nat.card F ^ k ≤ Nat.card F ^ (n - 1) := pow_le_pow_right₀ hq1 hkn
    have hpow1 : Nat.card F ≤ Nat.card F ^ (n - 1) := by
      calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
        _ ≤ Nat.card F ^ (n - 1) := pow_le_pow_right₀ hq1 (by omega)
    have htwo : Nat.card F + Nat.card F ^ k ≤ 2 * Nat.card F ^ (n - 1) := by
      rw [two_mul]
      exact Nat.add_le_add hpow1 hpowk
    have hfinal : 2 * Nat.card F ^ (n - 1) + (Nat.card F - 2) * Nat.card F ^ (n - 1)
        = Nat.card F ^ n := by
      rw [← add_mul, show 2 + (Nat.card F - 2) = Nat.card F from by omega]
      rw [mul_comm, ← pow_succ, show n - 1 + 1 = n from by omega]
    calc Nat.card F + Nat.card F ^ k + Nat.card F * (Tn + Tr)
        ≤ 2 * Nat.card F ^ (n - 1) + (Nat.card F - 2) * Nat.card F ^ (n - 1) :=
          Nat.add_le_add htwo hqTnTr
      _ = Nat.card F ^ n := hfinal
  have hXle : (N 0 + 1) + Nat.card F * Tn ≤ Nat.card F ^ n := by omega
  have hAeq : atIndex F n N = Nat.card F ^ n - ((N 0 + 1) + Nat.card F * Tn) :=
    Nat.eq_sub_of_add_eq hX2
  rw [hAeq]
  exact (Nat.le_sub_iff_add_le hXle).mpr hkey

end ZagierHoffmanPositiveChar
