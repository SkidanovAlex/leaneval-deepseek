import Submission.ZagierHoffmanProof.ATReduce

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Polynomial
open scoped BigOperators

/-!
# The increment lemma for the Anderson–Thakur coefficients

For a shape `N` of level `n` (i.e. `N_i = 0` for `i ≥ n`) with `∑_{i<n} N_i ≤ q - 2`, and
`1 ≤ k ≤ n-1`, the *increment lemma* is

  `atCoeff (atIndex n (N + e_k)) = R_(n-1-k)^(q^k) * atCoeff (atIndex n N)`.

It is proved from the Frobenius descent (`atCoeff_descend`), the residue bound (`residue_bound`),
the reduced-index identity (`reduce_eq`) and the increment lemma one level down.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

lemma outer_sum_le (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 2) :
    (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) ≤ (Nat.card F - 2) * Nat.card F ^ (n - 1) := by
  have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
  have hstep : ∀ i ∈ Finset.range n, N i * Nat.card F ^ i ≤ N i * Nat.card F ^ (n - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact Nat.mul_le_mul_left _ (pow_le_pow_right₀ hq1 (by omega))
  calc (∑ i ∈ Finset.range n, N i * Nat.card F ^ i)
      ≤ ∑ i ∈ Finset.range n, N i * Nat.card F ^ (n - 1) := Finset.sum_le_sum hstep
    _ = (∑ i ∈ Finset.range n, N i) * Nat.card F ^ (n - 1) := by rw [Finset.sum_mul]
    _ ≤ (Nat.card F - 2) * Nat.card F ^ (n - 1) := Nat.mul_le_mul_right _ hN

/-- The weighted outer sum of a shape with `∑ N_i ≤ q - 2`, plus `q^k`, stays below `q^n - 1`. -/
lemma shape_weighted_shift_le (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 2) (k : ℕ) (hkn : k ≤ n - 1) :
    (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) + Nat.card F ^ k ≤ Nat.card F ^ n - 1 := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hq1 : 1 ≤ Nat.card F := by omega
  have hw := outer_sum_le F n hn N hN
  have hk : Nat.card F ^ k ≤ Nat.card F ^ (n - 1) := pow_le_pow_right₀ hq1 hkn
  have hone : 1 ≤ Nat.card F ^ (n - 1) := Nat.one_le_pow (n - 1) (Nat.card F) (by omega)
  have hmain : (Nat.card F - 2) * Nat.card F ^ (n - 1) + Nat.card F ^ (n - 1)
      ≤ Nat.card F ^ n - 1 := by
    have hqa : (Nat.card F - 2) * Nat.card F ^ (n - 1) + Nat.card F ^ (n - 1)
        = (Nat.card F - 1) * Nat.card F ^ (n - 1) := by
      nth_rewrite 2 [← Nat.one_mul (Nat.card F ^ (n - 1))]
      rw [← add_mul, show (Nat.card F - 2) + 1 = Nat.card F - 1 from by omega]
    rw [hqa]
    have hsub : (Nat.card F - 1) * Nat.card F ^ (n - 1)
        = Nat.card F * Nat.card F ^ (n - 1) - Nat.card F ^ (n - 1) := by
      rw [Nat.sub_mul, one_mul]
    rw [hsub, ← pow_succ', show n - 1 + 1 = n from by omega]
    omega
  exact le_trans (Nat.add_le_add hw hk) hmain

/-- `2 q^(n-1) - 1 ≤ atIndex n N` for a shape with `∑ N_i ≤ q - 2`. -/
lemma two_pow_le_atIndex (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 2) :
    2 * Nat.card F ^ (n - 1) - 1 ≤ atIndex F n N := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hw := outer_sum_le F n hn N hN
  have hsum : 2 * Nat.card F ^ (n - 1) + (∑ i ∈ Finset.range n, N i * Nat.card F ^ i)
      ≤ Nat.card F ^ n := by
    have h1 : 2 * Nat.card F ^ (n - 1) + (Nat.card F - 2) * Nat.card F ^ (n - 1)
        = Nat.card F ^ n := by
      rw [← add_mul, show 2 + (Nat.card F - 2) = Nat.card F from by omega]
      rw [← pow_succ', show n - 1 + 1 = n from by omega]
    calc 2 * Nat.card F ^ (n - 1) + (∑ i ∈ Finset.range n, N i * Nat.card F ^ i)
        ≤ 2 * Nat.card F ^ (n - 1) + (Nat.card F - 2) * Nat.card F ^ (n - 1) :=
          Nat.add_le_add_left hw _
      _ = Nat.card F ^ n := h1
  have hone : 1 ≤ 2 * Nat.card F ^ (n - 1) := by
    have := Nat.one_le_pow (n - 1) (Nat.card F) (by omega)
    omega
  have hSle : (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) ≤ Nat.card F ^ n - 1 := by
    have h1 : (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) ≤ Nat.card F ^ n :=
      le_trans (Nat.le_add_left _ _) hsum
    omega
  rw [atIndex]
  refine (Nat.le_sub_iff_add_le hSle).mpr ?_
  omega

/-- `q^k ≤ atIndex n N` for a shape with `∑ N_i ≤ q - 2` and `k ≤ n-1`. -/
lemma pow_le_atIndex (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 2) (k : ℕ) (hkn : k ≤ n - 1) :
    Nat.card F ^ k ≤ atIndex F n N := by
  have hq1 : 1 ≤ Nat.card F := by have := carlitz_card_ge_two F; omega
  have hb := two_pow_le_atIndex F n hn N hN
  have hone : 1 ≤ Nat.card F ^ (n - 1) := Nat.one_le_pow (n - 1) (Nat.card F) (by omega)
  have hk : Nat.card F ^ k ≤ Nat.card F ^ (n - 1) := pow_le_pow_right₀ hq1 hkn
  omega

/-- The residue sets of the descent for `atIndex n N` and for `atIndex n (N + e_k)` coincide. -/
lemma mem_residueSet_sub (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 2) (k : ℕ) (hk1 : 1 ≤ k)
    (hkn : k ≤ n - 1) (m : ℕ) (res : Fin (m + 1) → ℕ) :
    res ∈ residueSet F (atIndex F n N - Nat.card F ^ k) (m + 1)
      ↔ res ∈ residueSet F (atIndex F n N) (m + 1) := by
  classical
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hpowA : Nat.card F ^ k ≤ atIndex F n N := pow_le_atIndex F n hn N hN k hkn
  have hiff1 : res ∈ residueSet F (atIndex F n N - Nat.card F ^ k) (m + 1)
      ↔ (∑ i, res i * Nat.card F ^ (i : ℕ)) ≤ atIndex F n N - Nat.card F ^ k
        ∧ Nat.card F ∣ ((atIndex F n N - Nat.card F ^ k) - ∑ i, res i * Nat.card F ^ (i : ℕ))
        ∧ IsResidueVec F res ∧ NoCarryVec F res := mem_residueSet F
  have hiff2 : res ∈ residueSet F (atIndex F n N) (m + 1)
      ↔ (∑ i, res i * Nat.card F ^ (i : ℕ)) ≤ atIndex F n N
        ∧ Nat.card F ∣ (atIndex F n N - ∑ i, res i * Nat.card F ^ (i : ℕ))
        ∧ IsResidueVec F res ∧ NoCarryVec F res := mem_residueSet F
  rw [hiff1, hiff2]
  constructor
  · rintro ⟨hle, hdvd, hrv, hnc⟩
    have hsplit : atIndex F n N - ∑ i, res i * Nat.card F ^ (i : ℕ)
        = ((atIndex F n N - Nat.card F ^ k) - ∑ i, res i * Nat.card F ^ (i : ℕ))
          + Nat.card F ^ k := by
      conv_lhs => rw [← Nat.sub_add_cancel hpowA]
      exact Nat.sub_add_comm hle
    refine ⟨le_trans hle (Nat.sub_le _ _), ?_, hrv, hnc⟩
    obtain ⟨t, ht⟩ := hdvd
    refine ⟨t + Nat.card F ^ (k - 1), ?_⟩
    rw [hsplit, ht, mul_add, ← pow_succ', show k - 1 + 1 = k from by omega]
  · rintro ⟨hle, hdvd, hrv, hnc⟩
    have hmem : res ∈ residueSet F (atIndex F n N) (m + 1) :=
      hiff2.mpr ⟨hle, hdvd, hrv, hnc⟩
    have hb := residue_bound F n hn N hN k hk1 hkn m res hmem
    have hleA : (∑ i, res i * Nat.card F ^ (i : ℕ)) + Nat.card F ^ k ≤ atIndex F n N := hb
    have hle' : (∑ i, res i * Nat.card F ^ (i : ℕ)) ≤ atIndex F n N - Nat.card F ^ k :=
      (Nat.le_sub_iff_add_le hpowA).mpr hleA
    have hsplit : atIndex F n N - ∑ i, res i * Nat.card F ^ (i : ℕ)
        = ((atIndex F n N - Nat.card F ^ k) - ∑ i, res i * Nat.card F ^ (i : ℕ))
          + Nat.card F ^ k := by
      conv_lhs => rw [← Nat.sub_add_cancel hpowA]
      exact Nat.sub_add_comm hle'
    have hqk : Nat.card F ∣ Nat.card F ^ k :=
      dvd_pow_self (Nat.card F) (by omega)
    refine ⟨hle', ?_, hrv, hnc⟩
    have h3 : Nat.card F ∣ (atIndex F n N - ∑ i, res i * Nat.card F ^ (i : ℕ)) - Nat.card F ^ k :=
      Nat.dvd_sub hdvd hqk
    rwa [hsplit, Nat.add_sub_cancel] at h3

/-- `atCoeff` at the index of a shifted shape, in terms of the shifted index. -/
lemma atIndex_shiftShape_eq (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 2) (k : ℕ) (hkn : k ≤ n - 1) :
    atIndex F n (shiftShape N k 1) = atIndex F n N - Nat.card F ^ k :=
  atIndex_shiftShape_one F n N k (by omega) (shape_weighted_shift_le F n hn N hN k hkn)

/-- The residue set of the descent from `atIndex n N` is unchanged by shifting a digit. -/
lemma residueSet_shiftShape (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 2) (k : ℕ) (hk1 : 1 ≤ k)
    (hkn : k ≤ n - 1) (m : ℕ) :
    residueSet F (atIndex F n (shiftShape N k 1)) (m + 1) = residueSet F (atIndex F n N) (m + 1) := by
  rw [atIndex_shiftShape_eq F n hn N hN k hkn]
  ext res
  exact mem_residueSet_sub F n hn N hN k hk1 hkn m res

/-- The tail shape sum is bounded by `∑ N_i`. -/
lemma sum_tailShape_le (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ) (m : ℕ) (hnm : n ≤ m + 1)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) (res : Fin (m + 1) → ℕ)
    (hres : res ∈ residueSet F (atIndex F n N) (m + 1)) :
    (∑ j ∈ Finset.range (n - 1), tailShape N (m + 1) res j) ≤ ∑ i ∈ Finset.range n, N i := by
  rw [sum_tailShape F n m hnm N res hres]
  have hN0 : N 0 ≤ Nat.card F - 1 :=
    le_trans (Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))) hN
  have hN0' : N 0 ≤ ∑ i ∈ Finset.range n, N i :=
    Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have h1 : (∑ j ∈ Finset.range (n - 1), N (j + 1)) = (∑ i ∈ Finset.range n, N i) - N 0 := by
    have hsplit := sum_range_shift_plain n (by omega) N
    omega
  have h2 : (∑ i : Fin m, res i.succ) ≤ N 0 := tail_sum_le F n hn N hN m res hres
  calc (∑ j ∈ Finset.range (n - 1), N (j + 1)) + (∑ i : Fin m, res i.succ)
      = ((∑ i ∈ Finset.range n, N i) - N 0) + (∑ i : Fin m, res i.succ) := by rw [h1]
    _ ≤ ((∑ i ∈ Finset.range n, N i) - N 0) + N 0 := Nat.add_le_add_left h2 _
    _ = ∑ i ∈ Finset.range n, N i := Nat.sub_add_cancel hN0'

omit [Field F] [Finite F] in
/-- The tail shape of a shifted shape is the shifted tail shape. -/
lemma tailShape_shiftShape (N : ℕ → ℕ) (B : ℕ) (res : Fin B → ℕ) (k : ℕ) (hk : 1 ≤ k) :
    tailShape (shiftShape N k 1) B res = shiftShape (tailShape N B res) (k - 1) 1 := by
  funext j
  have key : (if j = k - 1 then (1 : ℕ) else 0) = (if j + 1 = k then 1 else 0) := by
    by_cases h : j + 1 = k
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  rw [tailShape_apply, shiftShape_apply, shiftShape_apply, tailShape_apply, key]
  ring

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- ★★ **The increment lemma for the Anderson–Thakur coefficients**, with the increment lemma one
level down as hypothesis (this is the induction step of the main theorem). -/
theorem atCoeff_increment_of_ih (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ) (k : ℕ) (hk1 : 1 ≤ k)
    (hkn : k ≤ n - 1) (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 2)
    (hih : ∀ M : ℕ → ℕ, (∑ i ∈ Finset.range (n - 1), M i ≤ Nat.card F - 2) →
      atCoeff F (atIndex F (n - 1) (shiftShape M (k - 1) 1))
        = atR F (n - 1 - k) ^ (Nat.card F ^ (k - 1)) * atCoeff F (atIndex F (n - 1) M)) :
    atCoeff F (atIndex F n (shiftShape N k 1))
      = atR F (n - 1 - k) ^ (Nat.card F ^ k) * atCoeff F (atIndex F n N) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hqne : Nat.card F ≠ 0 := by omega
  have hkn' : k < n := by omega
  have hnA : n ≤ atIndex F n N + 1 := le_atIndex_add_one F n hn N hN
  have hRS : residueSet F (atIndex F n N - Nat.card F ^ k) (atIndex F n N + 1)
      = residueSet F (atIndex F n N) (atIndex F n N + 1) := by
    rw [← atIndex_shiftShape_eq F n hn N hN k hkn]
    exact residueSet_shiftShape F n hn N hN k hk1 hkn (atIndex F n N)
  rw [atIndex_shiftShape_eq F n hn N hN k hkn,
    atCoeff_descend F (atIndex F n N - Nat.card F ^ k) (atIndex F n N + 1)
      (by omega : atIndex F n N - Nat.card F ^ k + 1 ≤ atIndex F n N + 1),
    hRS, atCoeff_descend F (atIndex F n N) (atIndex F n N + 1) le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun res hres => ?_)
  have hMsum : (∑ j ∈ Finset.range (n - 1), tailShape N (atIndex F n N + 1) res j)
      ≤ Nat.card F - 2 := by
    refine le_trans (sum_tailShape_le F n hn N (atIndex F n N) hnA (by omega) res hres) ?_
    omega
  have hmemRS : res ∈ residueSet F (atIndex F n (shiftShape N k 1)) (atIndex F n N + 1) := by
    rw [atIndex_shiftShape_eq F n hn N hN k hkn, hRS]
    exact hres
  have hred1 : (atIndex F n N
        - ∑ i : Fin (atIndex F n N + 1), res i * Nat.card F ^ (i : ℕ)) / Nat.card F
      = atIndex F (n - 1) (tailShape N (atIndex F n N + 1) res) :=
    (Nat.eq_div_of_mul_eq_right hqne (reduce_eq F n (atIndex F n N) hn hnA N (by omega) res hres)).symm
  have hred2 : ((atIndex F n N - Nat.card F ^ k)
        - ∑ i : Fin (atIndex F n N + 1), res i * Nat.card F ^ (i : ℕ)) / Nat.card F
      = atIndex F (n - 1) (shiftShape (tailShape N (atIndex F n N + 1) res) (k - 1) 1) := by
    have hNshift : ∑ i ∈ Finset.range n, shiftShape N k 1 i ≤ Nat.card F - 1 := by
      rw [sum_shiftShape, if_pos hkn']
      omega
    have h := reduce_eq F n (atIndex F n N) hn hnA (shiftShape N k 1) hNshift res hmemRS
    rw [atIndex_shiftShape_eq F n hn N hN k hkn,
      tailShape_shiftShape N (atIndex F n N + 1) res k hk1] at h
    exact (Nat.eq_div_of_mul_eq_right hqne h).symm
  rw [hred2, hih (tailShape N (atIndex F n N + 1) res) hMsum, hred1, mul_pow, ← pow_mul,
    show Nat.card F ^ (k - 1) * Nat.card F = Nat.card F ^ k from by
      rw [← pow_succ, show k - 1 + 1 = k from by omega]]
  ring

end ZagierHoffmanPositiveChar
