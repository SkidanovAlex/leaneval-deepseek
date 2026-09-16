import Submission.ZagierHoffmanProof.ATResidue2

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# The reduced index of the Frobenius descent, and the tail shape

`atCoeff_descend` expresses `atCoeff N` as a sum over residue vectors `res` of
`coeff(res) * atCoeff ((N - ∑ res_i q^i)/q)^q`.  For `N = atIndex n N` the tail of a residue vector
determines the *shape* at level `n-1` whose index is the reduced index:

  `(atIndex n N - ∑ res_i q^i)/q = atIndex (n-1) M`,  `M_j = N_{j+1} + res_{j+1}`.

This file proves that (`reduce_eq`), together with the accompanying sum identities.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The (zero-extended) tail of a residue vector, as a sequence of natural numbers. -/
def resTailFn {m : ℕ} (res : Fin (m + 1) → ℕ) : ℕ → ℕ :=
  fun j => if h : j + 1 < m + 1 then res ⟨j + 1, h⟩ else 0

lemma tailFn_apply {m : ℕ} (res : Fin (m + 1) → ℕ) (j : ℕ) :
    resTailFn res j = if h : j + 1 < m + 1 then res ⟨j + 1, h⟩ else 0 := rfl

/-- The tail shape of a residue vector `res : Fin (m+1) → ℕ` for a shape `N`:
`M_j = N_{j+1} + res_{j+1}` (the residue vector is extended by zero). -/
def tailShape (N : ℕ → ℕ) (B : ℕ) (res : Fin B → ℕ) : ℕ → ℕ :=
  fun j => N (j + 1) + if h : j + 1 < B then res ⟨j + 1, h⟩ else 0

lemma tailShape_apply (N : ℕ → ℕ) (B : ℕ) (res : Fin B → ℕ) (j : ℕ) :
    tailShape N B res j = N (j + 1) + if h : j + 1 < B then res ⟨j + 1, h⟩ else 0 := rfl

lemma tailShape_eq (N : ℕ → ℕ) (m : ℕ) (res : Fin (m + 1) → ℕ) :
    tailShape N (m + 1) res = fun j => N (j + 1) + resTailFn res j := rfl

/-- The Fin-sum of the tail is the range-sum of the tail sequence. -/
lemma sum_tail_fin_eq_range (m : ℕ) (res : Fin (m + 1) → ℕ) :
    (∑ i : Fin m, res i.succ * Nat.card F ^ (i : ℕ))
      = ∑ j ∈ Finset.range m, resTailFn res j * Nat.card F ^ j := by
  have hsummand : ∀ i : Fin m,
      res i.succ * Nat.card F ^ (i : ℕ) = resTailFn res (i : ℕ) * Nat.card F ^ (i : ℕ) := by
    intro i
    rw [tailFn_apply, dif_pos (by have := i.isLt; omega : (i : ℕ) + 1 < m + 1)]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hsummand i),
    Fin.sum_univ_eq_sum_range (f := fun j => resTailFn res j * Nat.card F ^ j) m]

/-- The weighted sum of the tail shape is the weighted sum of the upper digits plus the weighted
tail sum. -/
lemma sum_tailShape_weighted (n m : ℕ) (hnm : n ≤ m + 1) (N : ℕ → ℕ) (res : Fin (m + 1) → ℕ)
    (hres : res ∈ residueSet F (atIndex F n N) (m + 1)) :
    (∑ j ∈ Finset.range (n - 1), tailShape N (m + 1) res j * Nat.card F ^ j)
      = (∑ j ∈ Finset.range (n - 1), N (j + 1) * Nat.card F ^ j)
        + (∑ i : Fin m, res i.succ * Nat.card F ^ (i : ℕ)) := by
  have hstep : (∑ j ∈ Finset.range (n - 1), tailShape N (m + 1) res j * Nat.card F ^ j)
      = (∑ j ∈ Finset.range (n - 1), N (j + 1) * Nat.card F ^ j)
        + (∑ j ∈ Finset.range (n - 1), resTailFn res j * Nat.card F ^ j) := by
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [tailShape_eq, add_mul])]
    rw [Finset.sum_add_distrib]
  rw [hstep, sum_tail_fin_eq_range]
  congr 1
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    have hnm' : n - 1 ≤ m := by omega
    exact lt_of_lt_of_le hj hnm'
  · intro j hj hjn
    rw [Finset.mem_range] at hj hjn
    have hjm : j + 1 < m + 1 := by omega
    rw [tailFn_apply, dif_pos hjm,
      residue_support F n N (m + 1) res hres (i := ⟨j + 1, hjm⟩) (by omega : n ≤ j + 1),
      zero_mul]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

omit [Field F] [Finite F] in
/-- The unweighted tail sum. -/
lemma sum_tailFn_eq (m : ℕ) (res : Fin (m + 1) → ℕ) :
    (∑ i : Fin m, res i.succ) = ∑ j ∈ Finset.range m, resTailFn res j := by
  have hsummand : ∀ i : Fin m, res i.succ = resTailFn res (i : ℕ) := by
    intro i
    rw [tailFn_apply, dif_pos (by have := i.isLt; omega : (i : ℕ) + 1 < m + 1)]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hsummand i),
    Fin.sum_univ_eq_sum_range (f := fun j => resTailFn res j) m]

variable (F : Type*) [Field F] [Finite F]

/-- ★★ **The reduced index is the index of the tail shape.** -/
theorem reduce_eq (n m : ℕ) (hn : 2 ≤ n) (hnm : n ≤ m + 1) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 1) (res : Fin (m + 1) → ℕ)
    (hres : res ∈ residueSet F (atIndex F n N) (m + 1)) :
    Nat.card F * atIndex F (n - 1) (tailShape N (m + 1) res)
      = atIndex F n N - ∑ i : Fin (m + 1), res i * Nat.card F ^ (i : ℕ) := by
  obtain ⟨hle, -, hrv, hnc⟩ := (mem_residueSet F).mp hres
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hq1 : 1 ≤ Nat.card F := by omega
  set M := tailShape N (m + 1) res with hM
  set Tn := ∑ j ∈ Finset.range (n - 1), N (j + 1) * Nat.card F ^ j with hTn
  set Tr := ∑ i : Fin m, res i.succ * Nat.card F ^ (i : ℕ) with hTr
  -- the weighted sum of the tail shape
  have hSM : (∑ j ∈ Finset.range (n - 1), M j * Nat.card F ^ j) = Tn + Tr := by
    rw [hM, hTn, hTr]
    exact sum_tailShape_weighted F n m hnm N res hres
  -- the unweighted sum of the tail shape is at most `q - 1`
  have hsumM_le : (∑ j ∈ Finset.range (n - 1), M j) ≤ Nat.card F - 1 := by
    have hstep : (∑ j ∈ Finset.range (n - 1), M j)
        = (∑ j ∈ Finset.range (n - 1), N (j + 1))
          + (∑ j ∈ Finset.range (n - 1), resTailFn res j) := by
      rw [hM, Finset.sum_congr rfl (fun j _ => by rw [tailShape_eq]), Finset.sum_add_distrib]
    have hN0 : N 0 ≤ Nat.card F - 1 :=
      le_trans (Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))) hN
    have hNsum : (∑ j ∈ Finset.range (n - 1), N (j + 1)) ≤ Nat.card F - 1 - N 0 := by
      have hsplit := sum_range_shift_plain n (by omega) N
      omega
    have htailsum : (∑ j ∈ Finset.range (n - 1), resTailFn res j) ≤ N 0 := by
      have h1 : (∑ j ∈ Finset.range (n - 1), resTailFn res j) ≤ ∑ j ∈ Finset.range m, resTailFn res j := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => Nat.zero_le _)
        intro j hj
        rw [Finset.mem_range] at hj ⊢
        omega
      rw [← sum_tailFn_eq] at h1
      exact le_trans h1 (tail_sum_le F n hn N hN m res hres)
    rw [hstep]
    have hfin : (Nat.card F - 1 - N 0) + N 0 ≤ Nat.card F - 1 := by
      rw [Nat.sub_add_cancel hN0]
    exact le_trans (Nat.add_le_add hNsum htailsum) hfin
  -- the base identity at level `n-1`
  have hbase : atIndex F (n - 1) M + (1 + (∑ j ∈ Finset.range (n - 1), M j * Nat.card F ^ j))
      = Nat.card F ^ (n - 1) := by
    have hle' : (∑ j ∈ Finset.range (n - 1), M j * Nat.card F ^ j) ≤ Nat.card F ^ (n - 1) - 1 :=
      weighted_shape_le F (n - 1) (by omega) M hsumM_le
    have hpow : 1 ≤ Nat.card F ^ (n - 1) := Nat.one_le_pow (n - 1) (Nat.card F) (by omega)
    rw [atIndex]
    omega
  -- `h1`
  have h1 : Nat.card F * atIndex F (n - 1) M + Nat.card F * (1 + (Tn + Tr)) = Nat.card F ^ n := by
    have h := congrArg (fun x => Nat.card F * x) hbase
    rw [mul_add] at h
    rw [hSM] at h
    rw [h, mul_comm, ← pow_succ, show n - 1 + 1 = n from by omega]
  -- the descent identity for the shape
  have hX2 : atIndex F n N + ((N 0 + 1) + Nat.card F * Tn) = Nat.card F ^ n := by
    simpa only [add_assoc] using atIndex_add_form F n (by omega) N hN
  have hS : (∑ i : Fin (m + 1), res i * Nat.card F ^ (i : ℕ)) = res 0 + Nat.card F * Tr := by
    rw [sum_fin_succ_shift F res, ← hTr]
  have hres0 : res 0 = Nat.card F - 1 - N 0 := residue_zero_entry F n (by omega) N hN m res hres
  have hres0' : res 0 + (N 0 + 1) = Nat.card F := by
    have hN0 : N 0 ≤ Nat.card F - 1 :=
      le_trans (Finset.single_le_sum (f := N) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))) hN
    rw [hres0]; omega
  have hSres_le : res 0 + Nat.card F * Tr ≤ atIndex F n N := by rw [← hS]; exact hle
  have hcancel : (atIndex F n N - (res 0 + Nat.card F * Tr)) + (res 0 + Nat.card F * Tr)
      = atIndex F n N := Nat.sub_add_cancel hSres_le
  -- `h2`
  have h2 : (atIndex F n N - ∑ i : Fin (m + 1), res i * Nat.card F ^ (i : ℕ))
      + Nat.card F * (1 + (Tn + Tr)) = Nat.card F ^ n := by
    rw [hS]
    have hkey : (atIndex F n N - (res 0 + Nat.card F * Tr)) + (res 0 + (N 0 + 1))
        + Nat.card F * Tr + Nat.card F * Tn = Nat.card F ^ n := by
      calc (atIndex F n N - (res 0 + Nat.card F * Tr)) + (res 0 + (N 0 + 1))
            + Nat.card F * Tr + Nat.card F * Tn
          = (atIndex F n N - (res 0 + Nat.card F * Tr)) + (res 0 + Nat.card F * Tr)
            + ((N 0 + 1) + Nat.card F * Tn) := by ring
        _ = atIndex F n N + ((N 0 + 1) + Nat.card F * Tn) := by rw [hcancel]
        _ = Nat.card F ^ n := hX2
    rw [← hkey]
    rw [hres0']
    ring
  exact Nat.add_right_cancel (h1.trans h2.symm)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The unweighted sum of the tail shape. -/
lemma sum_tailShape (n m : ℕ) (hnm : n ≤ m + 1) (N : ℕ → ℕ) (res : Fin (m + 1) → ℕ)
    (hres : res ∈ residueSet F (atIndex F n N) (m + 1)) :
    (∑ j ∈ Finset.range (n - 1), tailShape N (m + 1) res j)
      = (∑ j ∈ Finset.range (n - 1), N (j + 1)) + (∑ i : Fin m, res i.succ) := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [tailShape_eq]), Finset.sum_add_distrib]
  congr 1
  rw [sum_tailFn_eq]
  refine Finset.sum_subset ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    have hnm' : n - 1 ≤ m := by omega
    exact lt_of_lt_of_le hj hnm'
  · intro j hj hjn
    rw [Finset.mem_range] at hj hjn
    have hjm : j + 1 < m + 1 := by omega
    rw [tailFn_apply, dif_pos hjm,
      residue_support F n N (m + 1) res hres (i := ⟨j + 1, hjm⟩) (by omega : n ≤ j + 1)]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- `atIndex n N + 1 ≥ n` for `2 ≤ n` and `∑ N_i ≤ q - 2`. -/
lemma le_atIndex_add_one (n : ℕ) (hn : 2 ≤ n) (N : ℕ → ℕ)
    (hN : ∑ i ∈ Finset.range n, N i ≤ Nat.card F - 2) : n ≤ atIndex F n N + 1 := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  have hq1 : 1 ≤ Nat.card F := by omega
  have hw : (∑ i ∈ Finset.range n, N i * Nat.card F ^ i)
      ≤ (Nat.card F - 1) * Nat.card F ^ (n - 1) := by
    have hstep : ∀ i ∈ Finset.range n, N i * Nat.card F ^ i ≤ N i * Nat.card F ^ (n - 1) := by
      intro i hi
      rw [Finset.mem_range] at hi
      exact Nat.mul_le_mul_left _ (pow_le_pow_right₀ hq1 (by omega))
    have hNi : ∀ i ∈ Finset.range n, N i ≤ Nat.card F - 1 := fun i hi =>
      le_trans (Finset.single_le_sum (f := N) (fun j _ => Nat.zero_le _) hi) (by omega)
    calc (∑ i ∈ Finset.range n, N i * Nat.card F ^ i)
        ≤ ∑ i ∈ Finset.range n, N i * Nat.card F ^ (n - 1) := Finset.sum_le_sum hstep
      _ = (∑ i ∈ Finset.range n, N i) * Nat.card F ^ (n - 1) := by rw [Finset.sum_mul]
      _ ≤ (Nat.card F - 1) * Nat.card F ^ (n - 1) := by
          refine Nat.mul_le_mul_right _ ?_
          have hq1' : 1 ≤ Nat.card F := hq1
          omega
  have hS : (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) + Nat.card F ^ (n - 1) ≤ Nat.card F ^ n := by
    have hqa : (Nat.card F - 1) * Nat.card F ^ (n - 1) + Nat.card F ^ (n - 1)
        = Nat.card F ^ n := by
      rw [show (Nat.card F - 1) * Nat.card F ^ (n - 1) + Nat.card F ^ (n - 1)
          = Nat.card F * Nat.card F ^ (n - 1) from by
        nth_rewrite 2 [← Nat.one_mul (Nat.card F ^ (n - 1))]
        rw [← add_mul, show (Nat.card F - 1) + 1 = Nat.card F from by omega]]
      rw [← pow_succ', show n - 1 + 1 = n from by omega]
    exact le_trans (Nat.add_le_add_right hw _) (le_of_eq hqa)
  have hSle : (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) ≤ Nat.card F ^ n :=
    le_trans (Nat.le_add_right _ _) hS
  have hpowle : Nat.card F ^ (n - 1) ≤ atIndex F n N + 1 := by
    have h1 : 1 ≤ Nat.card F ^ (n - 1) := Nat.one_le_pow (n - 1) (Nat.card F) (by omega)
    have h2 : Nat.card F ^ n - 1 - (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) + 1
        = Nat.card F ^ n - (∑ i ∈ Finset.range n, N i * Nat.card F ^ i) := by omega
    rw [atIndex, h2]
    exact (Nat.le_sub_iff_add_le hSle).mpr (by rw [add_comm]; exact hS)
  have h2pow : n ≤ Nat.card F ^ (n - 1) := by
    have h3 : n - 1 < 2 ^ (n - 1) := Nat.lt_two_pow_self (n := n - 1)
    have h4 : n ≤ 2 ^ (n - 1) := by omega
    have h5 : 2 ^ (n - 1) ≤ Nat.card F ^ (n - 1) := Nat.pow_le_pow_left hq2 _
    omega
  omega

end ZagierHoffmanPositiveChar
