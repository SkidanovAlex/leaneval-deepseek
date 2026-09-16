import Submission.ZagierHoffmanProof.ATForm
import Submission.Commons.Data.Nat.geom_pred_mul_sum

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# Index arithmetic for the special-index Anderson–Thakur formula

Elementary (but fiddly) arithmetic facts about `atIndex F n N = q^n - 1 - ∑_i N_i q^i` and about the
residue vectors of the Frobenius descent (`residueSet`, `DescentGen.lean`) that are needed for the
key increment lemma `atCoeff (atIndex n (N+e_k)) = R_{n-1-k}^(q^k) * atCoeff (atIndex n N)`
(see `Submission/PLAN.md`, SESSION 294).
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

lemma sum_range_succ_shift (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ) :
    (∑ i ∈ Finset.range n, N i * Nat.card F ^ i)
      = N 0 + Nat.card F * (∑ i ∈ Finset.range (n - 1), N (i + 1) * Nat.card F ^ i) := by
  rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn).symm]
  rw [Finset.sum_range_succ']
  have hterm : ∀ k : ℕ, N (k + 1) * Nat.card F ^ (k + 1)
      = Nat.card F * (N (k + 1) * Nat.card F ^ k) := by
    intro k; rw [pow_succ]; ring
  rw [show (∑ k ∈ Finset.range (n - 1), N (k + 1) * Nat.card F ^ (k + 1))
      = ∑ k ∈ Finset.range (n - 1), Nat.card F * (N (k + 1) * Nat.card F ^ k)
      from Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [← Finset.mul_sum]
  have hr : n - 1 + 1 - 1 = n - 1 := by omega
  rw [hr, pow_zero, mul_one]
  ring

lemma atIndex_eq (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ) :
    atIndex F n N
      = Nat.card F ^ n - 1 - N 0
        - Nat.card F * (∑ i ∈ Finset.range (n - 1), N (i + 1) * Nat.card F ^ i) := by
  rw [atIndex, sum_range_succ_shift F n hn N]
  omega

variable (F : Type*) [Field F] [Finite F]

/-- Decomposition of the residue sum along the lowest entry. -/
lemma sum_fin_succ_shift {m : ℕ} (res : Fin (m + 1) → ℕ) :
    (∑ i : Fin (m + 1), res i * Nat.card F ^ (i : ℕ))
      = res 0 + Nat.card F * (∑ i : Fin m, res i.succ * Nat.card F ^ (i : ℕ)) := by
  rw [Fin.sum_univ_succ]
  have hterm : ∀ i : Fin m, res i.succ * Nat.card F ^ ((i.succ : Fin (m+1)) : ℕ)
      = Nat.card F * (res i.succ * Nat.card F ^ (i : ℕ)) := by
    intro i
    have h : ((i.succ : Fin (m + 1)) : ℕ) = (i : ℕ) + 1 := rfl
    rw [h, pow_succ]
    ring
  rw [show (∑ i : Fin m, res i.succ * Nat.card F ^ ((i.succ : Fin (m+1)) : ℕ))
      = ∑ i : Fin m, Nat.card F * (res i.succ * Nat.card F ^ (i : ℕ))
      from Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [← Finset.mul_sum]
  rw [show ((0 : Fin (m + 1)) : ℕ) = 0 from rfl, pow_zero, mul_one]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

lemma atIndex_lt_pow (n : ℕ) (N : ℕ → ℕ) : atIndex F n N < Nat.card F ^ n := by
  rw [atIndex]
  have h2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have h1 : 1 ≤ Nat.card F ^ n := by
    have := Nat.one_le_pow n (Nat.card F) (by omega)
    simpa using this
  omega

/-- A residue vector of the descent from `atIndex n N` is supported below `n`. -/
lemma residue_support (n : ℕ) (N : ℕ → ℕ) (Bv : ℕ) (res : Fin Bv → ℕ)
    (hres : res ∈ residueSet F (atIndex F n N) Bv) {i : Fin Bv} (hi : n ≤ (i : ℕ)) :
    res i = 0 := by
  obtain ⟨hle, -, -, -⟩ := (mem_residueSet F).mp hres
  by_contra hne
  have hone : 1 ≤ res i := Nat.one_le_iff_ne_zero.mpr hne
  have h1 : Nat.card F ^ n ≤ res i * Nat.card F ^ (i : ℕ) := by
    calc Nat.card F ^ n ≤ Nat.card F ^ (i : ℕ) :=
          Nat.pow_le_pow_right (by have := carlitz_card_ge_two F; omega) hi
      _ = 1 * Nat.card F ^ (i : ℕ) := (one_mul _).symm
      _ ≤ res i * Nat.card F ^ (i : ℕ) := Nat.mul_le_mul_right _ hone
  have h2 : res i * Nat.card F ^ (i : ℕ) ≤ ∑ j, res j * Nat.card F ^ (j : ℕ) :=
    Finset.single_le_sum (f := fun j : Fin Bv => res j * Nat.card F ^ (j : ℕ))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3 : Nat.card F ^ n ≤ atIndex F n N := le_trans h1 (le_trans h2 hle)
  have h4 := atIndex_lt_pow F n N
  omega

/-- The weighted shape sum is at most `(q-1) q^(n-1)` (a fortiori at most `q^n - 1`). -/
lemma weighted_shape_le (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) :
    (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) ≤ Nat.card F ^ n - 1 := by
  have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
  have hNi : ∀ i ∈ Finset.range n, N i ≤ Nat.card F - 1 := fun i hi =>
    le_trans (Finset.single_le_sum (f := N) (fun j _ => Nat.zero_le _) hi) hN
  calc (∑ i ∈ Finset.range n, N i * Nat.card F ^ i)
      ≤ ∑ i ∈ Finset.range n, (Nat.card F - 1) * Nat.card F ^ i :=
        Finset.sum_le_sum (fun i hi => Nat.mul_le_mul_right _ (hNi i hi))
    _ = (Nat.card F - 1) * (∑ i ∈ Finset.range n, Nat.card F ^ i) := by rw [Finset.mul_sum]
    _ = Nat.card F ^ n - 1 := Commons.Data.Nat.geom_pred_mul_sum (Nat.card F) hq1 n

/-- The index splits as `A + (N 0 + 1) + q * T = q^n`. -/
lemma atIndex_add_form (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) :
    atIndex F n N + (N 0 + 1)
      + Nat.card F * (∑ i ∈ Finset.range (n - 1), N (i + 1) * Nat.card F ^ i)
      = Nat.card F ^ n := by
  have hsplit := sum_range_succ_shift F n hn N
  have hle : (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) ≤ Nat.card F ^ n - 1 :=
    weighted_shape_le F n hn N hN
  have hA : atIndex F n N + (∑ i ∈ Finset.range n, N i * Nat.card F ^ i)
      = Nat.card F ^ n - 1 := by
    rw [atIndex]
    exact Nat.sub_add_cancel hle
  rw [hsplit] at hA
  have hpow1 : 1 ≤ Nat.card F ^ n := Nat.one_le_pow n _ (by have := carlitz_card_ge_two F; omega)
  have hpowsub : Nat.card F ^ n - 1 + 1 = Nat.card F ^ n := Nat.sub_add_cancel hpow1
  omega

/-- A residue vector of the descent from `atIndex n N` has lowest entry `q-1-N 0`. -/
lemma residue_zero_entry (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1)
    (m : ℕ) (res : Fin (m + 1) → ℕ)
    (hres : res ∈ residueSet F (atIndex F n N) (m + 1)) :
    res 0 = Nat.card F - 1 - N 0 := by
  obtain ⟨hle, hdvd, hrv, hnc⟩ := (mem_residueSet F).mp hres
  have hN0 : N 0 ≤ Nat.card F - 1 :=
    le_trans (Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr hn)) hN
  set T' := ∑ i ∈ Finset.range (n - 1), N (i + 1) * Nat.card F ^ i with hT'
  have h1 : (∑ i : Fin (m + 1), res i * Nat.card F ^ (i : ℕ)) ≡ res 0 [MOD Nat.card F] := by
    rw [sum_fin_succ_shift F res]
    have hz : Nat.card F * (∑ i : Fin m, res i.succ * Nat.card F ^ (i : ℕ))
        ≡ 0 [MOD Nat.card F] :=
      Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_mul_right _ _)
    have := Nat.ModEq.add_left (res 0) hz
    simpa using this
  have h2 : atIndex F n N ≡ ∑ i : Fin (m + 1), res i * Nat.card F ^ (i : ℕ) [MOD Nat.card F] :=
    ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm
  have hlow : atIndex F n N ≡ Nat.card F - 1 - N 0 [MOD Nat.card F] := by
    have hAsum : atIndex F n N + (N 0 + 1) + Nat.card F * T' = Nat.card F ^ n := by
      rw [hT']
      exact atIndex_add_form F n hn N hN
    have hpow : Nat.card F ^ n ≡ 0 [MOD Nat.card F] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (Nat.pos_iff_ne_zero.mp hn))
    have hqt : Nat.card F * T' ≡ 0 [MOD Nat.card F] :=
      Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_mul_right _ _)
    have hA : atIndex F n N + (N 0 + 1) ≡ 0 [MOD Nat.card F] := by
      refine Nat.ModEq.add_right_cancel' (Nat.card F * T') ?_
      rw [hAsum, zero_add]
      exact hpow.trans hqt.symm
    have hB : (Nat.card F - 1 - N 0) + (N 0 + 1) ≡ 0 [MOD Nat.card F] := by
      have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
      have hq : (Nat.card F - 1 - N 0) + (N 0 + 1) = Nat.card F := by
        rw [← Nat.add_assoc, Nat.sub_add_cancel hN0, Nat.sub_add_cancel hq1]
      rw [hq]
      exact Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)
    exact Nat.ModEq.add_right_cancel' (N 0 + 1) (hA.trans hB.symm)
  refine Nat.ModEq.eq_of_lt_of_lt (h1.symm.trans (h2.symm.trans hlow)) (hrv 0) ?_
  have hq : 2 ≤ Nat.card F := carlitz_card_ge_two F
  omega


/-- The unweighted version of the shift decomposition. -/
lemma sum_range_shift_plain (n : ℕ) (hn : 1 ≤ n) (N : ℕ → ℕ) :
    (∑ i ∈ Finset.range n, N i) = N 0 + ∑ i ∈ Finset.range (n - 1), N (i + 1) := by
  rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn).symm,
    Finset.sum_range_succ' (f := N) (n := n - 1),
    show n - 1 + 1 - 1 = n - 1 from by omega, add_comm]

/-- Weighted tail bound for the residues, using that they vanish above level `n`. -/
lemma tail_weighted_le (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ) (m : ℕ) (res : Fin (m + 1) → ℕ)
    (hres : res ∈ residueSet F (atIndex F n N) (m + 1)) :
    (∑ i : Fin m, res i.succ * Nat.card F ^ (i : ℕ))
      ≤ Nat.card F ^ (n - 2) * (∑ i : Fin m, res i.succ) := by
  have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
  have hsupp : ∀ j : Fin (m + 1), n ≤ (j : ℕ) → res j = 0 :=
    fun j hj => residue_support F n N (m + 1) res hres hj
  calc (∑ i : Fin m, res i.succ * Nat.card F ^ (i : ℕ))
      ≤ ∑ i : Fin m, res i.succ * Nat.card F ^ (n - 2) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases h : (i : ℕ) + 2 ≤ n
        · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
        · have hzero : res i.succ = 0 := hsupp i.succ (by simp; omega)
          rw [hzero, zero_mul, zero_mul]
    _ = Nat.card F ^ (n - 2) * (∑ i : Fin m, res i.succ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => Nat.mul_comm _ _)


end ZagierHoffmanPositiveChar

