import Mathlib
import Submission.Work.Pi6.SQM.Cup3CobSetup
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial
namespace Work.Pi6.SQM

@[simp] lemma L3k_mkL {n m : ℕ} (k a b c : ℕ) (hk : k < (n + m - 3) + 2) (ha : a < n - 2)
    (hb : b < m - 2) (hc : c < n - 2) (h : a + c + 3 ≤ n) :
    L3k (mkL n m k a b c hk ha hb hc h) = ⟨k, hk⟩ := rfl
@[simp] lemma L3a_mkL {n m : ℕ} (k a b c : ℕ) (hk : k < (n + m - 3) + 2) (ha : a < n - 2)
    (hb : b < m - 2) (hc : c < n - 2) (h : a + c + 3 ≤ n) :
    L3a (mkL n m k a b c hk ha hb hc h) = ⟨a, ha⟩ := rfl
@[simp] lemma L3b_mkL {n m : ℕ} (k a b c : ℕ) (hk : k < (n + m - 3) + 2) (ha : a < n - 2)
    (hb : b < m - 2) (hc : c < n - 2) (h : a + c + 3 ≤ n) :
    L3b (mkL n m k a b c hk ha hb hc h) = ⟨b, hb⟩ := rfl
@[simp] lemma L3c_mkL {n m : ℕ} (k a b c : ℕ) (hk : k < (n + m - 3) + 2) (ha : a < n - 2)
    (hb : b < m - 2) (hc : c < n - 2) (h : a + c + 3 ≤ n) :
    L3c (mkL n m k a b c hk ha hb hc h) = ⟨c, hc⟩ := rfl
@[simp] lemma C3a_mkT3 {n m : ℕ} (a b c j : ℕ) (ha : a < n - 1) (hb : b < m - 2)
    (hc : c < n - 1) (hj : j < n + 2) (h : a + c + 3 ≤ n + 1) :
    C3a (mkT3 n m a b c j ha hb hc hj h) = ⟨a, ha⟩ := rfl
@[simp] lemma C3b_mkT3 {n m : ℕ} (a b c j : ℕ) (ha : a < n - 1) (hb : b < m - 2)
    (hc : c < n - 1) (hj : j < n + 2) (h : a + c + 3 ≤ n + 1) :
    C3b (mkT3 n m a b c j ha hb hc hj h) = ⟨b, hb⟩ := rfl
@[simp] lemma C3c_mkT3 {n m : ℕ} (a b c j : ℕ) (ha : a < n - 1) (hb : b < m - 2)
    (hc : c < n - 1) (hj : j < n + 2) (h : a + c + 3 ≤ n + 1) :
    C3c (mkT3 n m a b c j ha hb hc hj h) = ⟨c, hc⟩ := rfl
@[simp] lemma C3j_mkT3 {n m : ℕ} (a b c j : ℕ) (ha : a < n - 1) (hb : b < m - 2)
    (hc : c < n - 1) (hj : j < n + 2) (h : a + c + 3 ≤ n + 1) :
    C3j (mkT3 n m a b c j ha hb hc hj h) = ⟨j, hj⟩ := rfl
@[simp] lemma C4a_mkT4 {n m : ℕ} (a b c j : ℕ) (ha : a < n - 2) (hb : b < m - 1)
    (hc : c < n - 2) (hj : j < m + 2) (h : a + c + 3 ≤ n) :
    C4a (mkT4 n m a b c j ha hb hc hj h) = ⟨a, ha⟩ := rfl
@[simp] lemma C4b_mkT4 {n m : ℕ} (a b c j : ℕ) (ha : a < n - 2) (hb : b < m - 1)
    (hc : c < n - 2) (hj : j < m + 2) (h : a + c + 3 ≤ n) :
    C4b (mkT4 n m a b c j ha hb hc hj h) = ⟨b, hb⟩ := rfl
@[simp] lemma C4c_mkT4 {n m : ℕ} (a b c j : ℕ) (ha : a < n - 2) (hb : b < m - 1)
    (hc : c < n - 2) (hj : j < m + 2) (h : a + c + 3 ≤ n) :
    C4c (mkT4 n m a b c j ha hb hc hj h) = ⟨c, hc⟩ := rfl
@[simp] lemma C4j_mkT4 {n m : ℕ} (a b c j : ℕ) (ha : a < n - 2) (hb : b < m - 1)
    (hc : c < n - 2) (hj : j < m + 2) (h : a + c + 3 ≤ n) :
    C4j (mkT4 n m a b c j ha hb hc hj h) = ⟨j, hj⟩ := rfl
@[simp] lemma L3k_lit {n m : ℕ} (k : Fin ((n + m - 3) + 2)) (a : Fin (n - 2)) (b : Fin (m - 2))
    (c : Fin (n - 2)) (h : a.val + c.val + 3 ≤ n) :
    L3k (⟨(k, (a, b, c)), h⟩ : L3Idx n m) = k := rfl
@[simp] lemma L3a_lit {n m : ℕ} (k : Fin ((n + m - 3) + 2)) (a : Fin (n - 2)) (b : Fin (m - 2))
    (c : Fin (n - 2)) (h : a.val + c.val + 3 ≤ n) :
    L3a (⟨(k, (a, b, c)), h⟩ : L3Idx n m) = a := rfl
@[simp] lemma L3b_lit {n m : ℕ} (k : Fin ((n + m - 3) + 2)) (a : Fin (n - 2)) (b : Fin (m - 2))
    (c : Fin (n - 2)) (h : a.val + c.val + 3 ≤ n) :
    L3b (⟨(k, (a, b, c)), h⟩ : L3Idx n m) = b := rfl
@[simp] lemma L3c_lit {n m : ℕ} (k : Fin ((n + m - 3) + 2)) (a : Fin (n - 2)) (b : Fin (m - 2))
    (c : Fin (n - 2)) (h : a.val + c.val + 3 ≤ n) :
    L3c (⟨(k, (a, b, c)), h⟩ : L3Idx n m) = c := rfl
@[simp] lemma C3a_lit {n m : ℕ} (a : Fin (n - 1)) (b : Fin (m - 2)) (c : Fin (n - 1))
    (j : Fin (n + 2)) (h : a.val + c.val + 3 ≤ n + 1) :
    C3a (⟨(a, (b, c, j)), h⟩ : T3Idx n m) = a := rfl
@[simp] lemma C3b_lit {n m : ℕ} (a : Fin (n - 1)) (b : Fin (m - 2)) (c : Fin (n - 1))
    (j : Fin (n + 2)) (h : a.val + c.val + 3 ≤ n + 1) :
    C3b (⟨(a, (b, c, j)), h⟩ : T3Idx n m) = b := rfl
@[simp] lemma C3c_lit {n m : ℕ} (a : Fin (n - 1)) (b : Fin (m - 2)) (c : Fin (n - 1))
    (j : Fin (n + 2)) (h : a.val + c.val + 3 ≤ n + 1) :
    C3c (⟨(a, (b, c, j)), h⟩ : T3Idx n m) = c := rfl
@[simp] lemma C3j_lit {n m : ℕ} (a : Fin (n - 1)) (b : Fin (m - 2)) (c : Fin (n - 1))
    (j : Fin (n + 2)) (h : a.val + c.val + 3 ≤ n + 1) :
    C3j (⟨(a, (b, c, j)), h⟩ : T3Idx n m) = j := rfl
@[simp] lemma C4a_lit {n m : ℕ} (a : Fin (n - 2)) (b : Fin (m - 1)) (c : Fin (n - 2))
    (j : Fin (m + 2)) (h : a.val + c.val + 3 ≤ n) :
    C4a (⟨(a, (b, c, j)), h⟩ : T4Idx n m) = a := rfl
@[simp] lemma C4b_lit {n m : ℕ} (a : Fin (n - 2)) (b : Fin (m - 1)) (c : Fin (n - 2))
    (j : Fin (m + 2)) (h : a.val + c.val + 3 ≤ n) :
    C4b (⟨(a, (b, c, j)), h⟩ : T4Idx n m) = b := rfl
@[simp] lemma C4c_lit {n m : ℕ} (a : Fin (n - 2)) (b : Fin (m - 1)) (c : Fin (n - 2))
    (j : Fin (m + 2)) (h : a.val + c.val + 3 ≤ n) :
    C4c (⟨(a, (b, c, j)), h⟩ : T4Idx n m) = c := rfl
@[simp] lemma C4j_lit {n m : ℕ} (a : Fin (n - 2)) (b : Fin (m - 1)) (c : Fin (n - 2))
    (j : Fin (m + 2)) (h : a.val + c.val + 3 ≤ n) :
    C4j (⟨(a, (b, c, j)), h⟩ : T4Idx n m) = j := rfl

lemma L3Idx_eq {n m : ℕ} {p q : L3Idx n m}
    (h1 : (L3k p).val = (L3k q).val) (h2 : (L3a p).val = (L3a q).val)
    (h3 : (L3b p).val = (L3b q).val) (h4 : (L3c p).val = (L3c q).val) : p = q :=
  Subtype.ext (Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Prod.ext (Fin.ext h3) (Fin.ext h4))))
lemma T3Idx_eq {n m : ℕ} {p q : T3Idx n m}
    (h1 : (C3a p).val = (C3a q).val) (h2 : (C3b p).val = (C3b q).val)
    (h3 : (C3c p).val = (C3c q).val) (h4 : (C3j p).val = (C3j q).val) : p = q :=
  Subtype.ext (Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Prod.ext (Fin.ext h3) (Fin.ext h4))))
lemma T4Idx_eq {n m : ℕ} {p q : T4Idx n m}
    (h1 : (C4a p).val = (C4a q).val) (h2 : (C4b p).val = (C4b q).val)
    (h3 : (C4c p).val = (C4c q).val) (h4 : (C4j p).val = (C4j q).val) : p = q :=
  Subtype.ext (Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Prod.ext (Fin.ext h3) (Fin.ext h4))))
lemma T1Idx_eq {n m : ℕ} {p q : T1Idx n m} (h1 : p.1.val = q.1.val) (h2 : p.2.val = q.2.val) :
    p = q := Prod.ext (Fin.ext h1) (Fin.ext h2)
lemma T2Idx_eq {n m : ℕ} {p q : T2Idx n m} (h1 : p.1.val = q.1.val) (h2 : p.2.val = q.2.val) :
    p = q := Prod.ext (Fin.ext h1) (Fin.ext h2)

lemma sumL_eq {n m : ℕ} {p q : L3Idx n m}
    (h1 : (L3k p).val = (L3k q).val) (h2 : (L3a p).val = (L3a q).val)
    (h3 : (L3b p).val = (L3b q).val) (h4 : (L3c p).val = (L3c q).val) :
    (Sum.inl p : Idx3 n m) = Sum.inl q := congrArg (fun r => (Sum.inl r : Idx3 n m)) (L3Idx_eq h1 h2 h3 h4)
lemma sumC3_eq {n m : ℕ} {p q : T3Idx n m}
    (h1 : (C3a p).val = (C3a q).val) (h2 : (C3b p).val = (C3b q).val)
    (h3 : (C3c p).val = (C3c q).val) (h4 : (C3j p).val = (C3j q).val) :
    (Sum.inr (Sum.inl p) : Idx3 n m) = Sum.inr (Sum.inl q) :=
  congrArg (fun r => (Sum.inr (Sum.inl r) : Idx3 n m)) (T3Idx_eq h1 h2 h3 h4)
lemma sumC4_eq {n m : ℕ} {p q : T4Idx n m}
    (h1 : (C4a p).val = (C4a q).val) (h2 : (C4b p).val = (C4b q).val)
    (h3 : (C4c p).val = (C4c q).val) (h4 : (C4j p).val = (C4j q).val) :
    (Sum.inr (Sum.inr (Sum.inl p)) : Idx3 n m) = Sum.inr (Sum.inr (Sum.inl q)) :=
  congrArg (fun r => (Sum.inr (Sum.inr (Sum.inl r)) : Idx3 n m)) (T4Idx_eq h1 h2 h3 h4)
lemma sumT1_eq {n m : ℕ} {p q : T1Idx n m} (h1 : p.1.val = q.1.val) (h2 : p.2.val = q.2.val) :
    (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))) : Idx3 n m) = Sum.inr (Sum.inr (Sum.inr (Sum.inl q))) :=
  congrArg (fun r => (Sum.inr (Sum.inr (Sum.inr (Sum.inl r))) : Idx3 n m)) (T1Idx_eq h1 h2)
lemma sumT2_eq {n m : ℕ} {p q : T2Idx n m} (h1 : p.1.val = q.1.val) (h2 : p.2.val = q.2.val) :
    (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))) : Idx3 n m) = Sum.inr (Sum.inr (Sum.inr (Sum.inr q))) :=
  congrArg (fun r => (Sum.inr (Sum.inr (Sum.inr (Sum.inr r))) : Idx3 n m)) (T2Idx_eq h1 h2)

/-- normalization for a single goal -/
syntax "cupN" : tactic
macro_rules
  | `(tactic|cupN) => `(tactic|
      (simp only [L3k_mkL, L3a_mkL, L3b_mkL, L3c_mkL, C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3,
         C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, mkT1, mkT2, Fin.val_mk]))

syntax "cupN2" : tactic
macro_rules
  | `(tactic|cupN2) => `(tactic|
      (simp only [L3a, L3b, L3c, L3k, C3a, C3b, C3c, C3j, C4a, C4b, C4c, C4j,
         mkT1, mkT2, mkT3, mkT4, mkL, Fin.val_mk]))

syntax "cupClose1" : tactic
macro_rules
  | `(tactic|cupClose1) => `(tactic|
      (first
       | (refine sumL_eq ?_ ?_ ?_ ?_ <;> (first | (cupN <;> omega) | (omega; done)))
       | (refine sumC3_eq ?_ ?_ ?_ ?_ <;> (first | (cupN <;> omega) | (omega; done)))
       | (refine sumC4_eq ?_ ?_ ?_ ?_ <;> (first | (cupN <;> omega) | (omega; done)))
       | (refine sumT1_eq ?_ ?_ <;> (first | (cupN <;> omega) | (omega; done)))
       | (refine sumT2_eq ?_ ?_ <;> (first | (cupN <;> omega) | (omega; done)))
       | (exfalso; (first | omega | contradiction | (simp_all; done)))
       | (simp_all; done)
       | (omega; done)))

lemma swapL_case (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : L3Idx n m) :
    cup3Swap n m hn hm (cup3Swap n m hn hm (Sum.inl p)) = Sum.inl p := by
  simp only [cup3Swap_inl]
  simp only [swapL]
  by_cases h1 : (L3k p).val ≤ (L3a p).val
  · rw [dif_pos h1]
    have hA := (L3a p).isLt
    have hB := (L3b p).isLt
    have hC := (L3c p).isLt
    have hK := (L3k p).isLt
    have hH := L3h p
    simp only [idxC3, cup3Swap_C3, swapC3]
    by_cases g1 : (C3j (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
    · rw [dif_pos g1]
      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
      cupClose1
    · rw [dif_neg g1]
      by_cases g2 : (C3j (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
      · rw [dif_pos g2]
        by_cases g3 : 1 ≤ (C3a (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g3]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
          cupClose1
        · rw [dif_neg g3]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
          cupClose1
      · rw [dif_neg g2]
        by_cases g4 : (C3j (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
        · rw [dif_pos g4]
          by_cases g5 : 1 ≤ (C3c (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g5]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
            cupClose1
          · rw [dif_neg g5]
            by_cases g6 : (C3b (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
            · rw [dif_pos g6]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
              cupClose1
            · rw [dif_neg g6]
              by_cases g7 : (C3a (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
              · rw [dif_pos g7]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                cupClose1
              · rw [dif_neg g7]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                cupClose1
        · rw [dif_neg g4]
          by_cases g8 : (C3j (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
          · rw [dif_pos g8]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
            cupClose1
          · rw [dif_neg g8]
            by_cases g9 : (C3j (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
            · rw [dif_pos g9]
              by_cases g10 : 1 ≤ (C3c (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g10]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                cupClose1
              · rw [dif_neg g10]
                by_cases g11 : 1 ≤ (C3b (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g11]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                  cupClose1
                · rw [dif_neg g11]
                  by_cases g12 : 1 ≤ (C3a (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g12]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                    cupClose1
                  · rw [dif_neg g12]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                    cupClose1
            · rw [dif_neg g9]
              by_cases g13 : (C3j (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
              · rw [dif_pos g13]
                by_cases g14 : (C3a (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val + 1) ((L3b p).val) ((L3c p).val) ((L3k p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                · rw [dif_pos g14]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                  cupClose1
                · rw [dif_neg g14]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                  cupClose1
              · rw [dif_neg g13]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                cupClose1
  · rw [dif_neg h1]
    by_cases h2 : (L3k p).val ≤ (L3a p).val + (L3b p).val + 1
    · rw [dif_pos h2]
      have hA := (L3a p).isLt
      have hB := (L3b p).isLt
      have hC := (L3c p).isLt
      have hK := (L3k p).isLt
      have hH := L3h p
      simp only [idxC4, cup3Swap_C4, swapC4]
      by_cases g1 : (C4j (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
      · rw [dif_pos g1]
        by_cases g2 : 1 ≤ (C4b (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g2]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
          cupClose1
        · rw [dif_neg g2]
          by_cases g3 : 1 ≤ (C4c (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g3]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
            cupClose1
          · rw [dif_neg g3]
            by_cases g4 : m = 2
            · rw [dif_pos g4]
              by_cases g5 : (C4a (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
              · rw [dif_pos g5]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                cupClose1
              · rw [dif_neg g5]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                cupClose1
            · rw [dif_neg g4]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
              cupClose1
      · rw [dif_neg g1]
        by_cases g6 : (C4j (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g6]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
          cupClose1
        · rw [dif_neg g6]
          by_cases g7 : (C4j (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
          · rw [dif_pos g7]
            by_cases g8 : 1 ≤ (C4b (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g8]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
              cupClose1
            · rw [dif_neg g8]
              by_cases g9 : 1 ≤ (C4a (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g9]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                cupClose1
              · rw [dif_neg g9]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                cupClose1
          · rw [dif_neg g7]
            by_cases g10 : (C4j (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
            · rw [dif_pos g10]
              by_cases g11 : (C4b (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
              · rw [dif_pos g11]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                cupClose1
              · rw [dif_neg g11]
                by_cases g12 : (C4a (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                · rw [dif_pos g12]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                  cupClose1
                · rw [dif_neg g12]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                  cupClose1
            · rw [dif_neg g10]
              by_cases g13 : (C4j (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
              · rw [dif_pos g13]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                cupClose1
              · rw [dif_neg g13]
                by_cases g14 : (C4b (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                · rw [dif_pos g14]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                  cupClose1
                · rw [dif_neg g14]
                  by_cases g15 : 1 ≤ (C4c (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g15]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                    cupClose1
                  · rw [dif_neg g15]
                    by_cases g16 : m = 2
                    · rw [dif_pos g16]
                      by_cases g17 : (C4a (mkT4 n m ((L3a p).val) ((L3b p).val + 1) ((L3c p).val) ((L3k p).val - (L3a p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                      · rw [dif_pos g17]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                        cupClose1
                      · rw [dif_neg g17]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                        cupClose1
                    · rw [dif_neg g16]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                      cupClose1
    · rw [dif_neg h2]
      by_cases h3 : (L3k p).val ≤ (L3a p).val + (L3b p).val + (L3c p).val + 2
      · rw [dif_pos h3]
        have hA := (L3a p).isLt
        have hB := (L3b p).isLt
        have hC := (L3c p).isLt
        have hK := (L3k p).isLt
        have hH := L3h p
        simp only [idxC3, cup3Swap_C3, swapC3]
        by_cases g1 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g1]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          cupClose1
        · rw [dif_neg g1]
          by_cases g2 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g2]
            by_cases g3 : 1 ≤ (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g3]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              cupClose1
            · rw [dif_neg g3]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              cupClose1
          · rw [dif_neg g2]
            by_cases g4 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
            · rw [dif_pos g4]
              by_cases g5 : 1 ≤ (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g5]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                cupClose1
              · rw [dif_neg g5]
                by_cases g6 : (C3b (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
                · rw [dif_pos g6]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  cupClose1
                · rw [dif_neg g6]
                  by_cases g7 : (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                  · rw [dif_pos g7]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    cupClose1
                  · rw [dif_neg g7]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    cupClose1
            · rw [dif_neg g4]
              by_cases g8 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
              · rw [dif_pos g8]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                cupClose1
              · rw [dif_neg g8]
                by_cases g9 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                · rw [dif_pos g9]
                  by_cases g10 : 1 ≤ (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g10]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    cupClose1
                  · rw [dif_neg g10]
                    by_cases g11 : 1 ≤ (C3b (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g11]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      cupClose1
                    · rw [dif_neg g11]
                      by_cases g12 : 1 ≤ (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g12]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                        cupClose1
                      · rw [dif_neg g12]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                        cupClose1
                · rw [dif_neg g9]
                  by_cases g13 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                  · rw [dif_pos g13]
                    by_cases g14 : (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val + 1) ((L3k p).val - (L3b p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                    · rw [dif_pos g14]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      cupClose1
                    · rw [dif_neg g14]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      cupClose1
                  · rw [dif_neg g13]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    cupClose1
      · rw [dif_neg h3]
        by_cases h4 : (L3k p).val ≤ (L3a p).val + (L3c p).val + m
        · rw [dif_pos h4]
          have hA := (L3a p).isLt
          have hB := (L3b p).isLt
          have hC := (L3c p).isLt
          have hK := (L3k p).isLt
          have hH := L3h p
          simp only [idxC4, cup3Swap_C4, swapC4]
          by_cases g1 : (C4j (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
          · rw [dif_pos g1]
            by_cases g2 : 1 ≤ (C4b (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g2]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              cupClose1
            · rw [dif_neg g2]
              by_cases g3 : 1 ≤ (C4c (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
              · rw [dif_neg g3]
                by_cases g4 : m = 2
                · rw [dif_pos g4]
                  by_cases g5 : (C4a (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                  · rw [dif_pos g5]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    cupClose1
                  · rw [dif_neg g5]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    cupClose1
                · rw [dif_neg g4]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  cupClose1
          · rw [dif_neg g1]
            by_cases g6 : (C4j (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g6]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
              cupClose1
            · rw [dif_neg g6]
              by_cases g7 : (C4j (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
              · rw [dif_pos g7]
                by_cases g8 : 1 ≤ (C4b (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g8]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  cupClose1
                · rw [dif_neg g8]
                  by_cases g9 : 1 ≤ (C4a (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g9]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    cupClose1
                  · rw [dif_neg g9]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    cupClose1
              · rw [dif_neg g7]
                by_cases g10 : (C4j (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                · rw [dif_pos g10]
                  by_cases g11 : (C4b (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                  · rw [dif_pos g11]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    cupClose1
                  · rw [dif_neg g11]
                    by_cases g12 : (C4a (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                    · rw [dif_pos g12]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                      cupClose1
                    · rw [dif_neg g12]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                      cupClose1
                · rw [dif_neg g10]
                  by_cases g13 : (C4j (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                  · rw [dif_pos g13]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    cupClose1
                  · rw [dif_neg g13]
                    by_cases g14 : (C4b (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                    · rw [dif_pos g14]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      cupClose1
                    · rw [dif_neg g14]
                      by_cases g15 : 1 ≤ (C4c (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g15]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        cupClose1
                      · rw [dif_neg g15]
                        by_cases g16 : m = 2
                        · rw [dif_pos g16]
                          by_cases g17 : (C4a (mkT4 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - (L3a p).val - (L3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                          · rw [dif_pos g17]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                            cupClose1
                          · rw [dif_neg g17]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                            cupClose1
                        · rw [dif_neg g16]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                          cupClose1
        · rw [dif_neg h4]
          have hA := (L3a p).isLt
          have hB := (L3b p).isLt
          have hC := (L3c p).isLt
          have hK := (L3k p).isLt
          have hH := L3h p
          simp only [idxC3, cup3Swap_C3, swapC3]
          by_cases g1 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g1]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            cupClose1
          · rw [dif_neg g1]
            by_cases g2 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g2]
              by_cases g3 : 1 ≤ (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
              · rw [dif_neg g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
            · rw [dif_neg g2]
              by_cases g4 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
              · rw [dif_pos g4]
                by_cases g5 : 1 ≤ (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g5]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  cupClose1
                · rw [dif_neg g5]
                  by_cases g6 : (C3b (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
                  · rw [dif_pos g6]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    cupClose1
                  · rw [dif_neg g6]
                    by_cases g7 : (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                    · rw [dif_pos g7]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      cupClose1
                    · rw [dif_neg g7]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      cupClose1
              · rw [dif_neg g4]
                by_cases g8 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                · rw [dif_pos g8]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  cupClose1
                · rw [dif_neg g8]
                  by_cases g9 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                  · rw [dif_pos g9]
                    by_cases g10 : 1 ≤ (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g10]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      cupClose1
                    · rw [dif_neg g10]
                      by_cases g11 : 1 ≤ (C3b (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g11]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        cupClose1
                      · rw [dif_neg g11]
                        by_cases g12 : 1 ≤ (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                        · rw [dif_neg g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                  · rw [dif_neg g9]
                    by_cases g13 : (C3j (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                    · rw [dif_pos g13]
                      by_cases g14 : (C3a (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((L3a p).val) ((L3b p).val) ((L3c p).val) ((L3k p).val - m + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                      · rw [dif_pos g14]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        cupClose1
                      · rw [dif_neg g14]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        cupClose1
                    · rw [dif_neg g13]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      cupClose1

lemma swapC3_case (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T3Idx n m) :
    cup3Swap n m hn hm (cup3Swap n m hn hm (Sum.inr (Sum.inl p))) = Sum.inr (Sum.inl p) := by
  simp only [cup3Swap_C3]
  simp only [swapC3]
  by_cases h1 : (C3j p).val + 1 ≤ (C3a p).val
  · rw [dif_pos h1]
    have hA := (C3a p).isLt
    have hB := (C3b p).isLt
    have hC := (C3c p).isLt
    have hJ := (C3j p).isLt
    have hH := C3h p
    simp only [idxL, cup3Swap_inl, swapL]
    by_cases g1 : (L3k (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
    · rw [dif_pos g1]
      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
      cupClose1
    · rw [dif_neg g1]
      by_cases g2 : (L3k (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3b (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
      · rw [dif_pos g2]
        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
        cupClose1
      · rw [dif_neg g2]
        by_cases g3 : (L3k (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3b (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3c (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
        · rw [dif_pos g3]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
          cupClose1
        · rw [dif_neg g3]
          by_cases g4 : (L3k (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3c (mkL n m ((C3j p).val) ((C3a p).val - 1) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + m
          · rw [dif_pos g4]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
            cupClose1
          · rw [dif_neg g4]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
            cupClose1
  · rw [dif_neg h1]
    by_cases h2 : (C3j p).val = (C3a p).val
    · rw [dif_pos h2]
      by_cases h3 : 1 ≤ (C3a p).val
      · rw [dif_pos h3]
        have hA := (C3a p).isLt
        have hB := (C3b p).isLt
        have hC := (C3c p).isLt
        have hJ := (C3j p).isLt
        have hH := C3h p
        simp only [idxC4, cup3Swap_C4, swapC4]
        by_cases g1 : (C4j (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
        · rw [dif_pos g1]
          by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g2]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            cupClose1
          · rw [dif_neg g2]
            by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g3]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              cupClose1
            · rw [dif_neg g3]
              by_cases g4 : m = 2
              · rw [dif_pos g4]
                by_cases g5 : (C4a (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                · rw [dif_pos g5]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  cupClose1
                · rw [dif_neg g5]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  cupClose1
              · rw [dif_neg g4]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                cupClose1
        · rw [dif_neg g1]
          by_cases g6 : (C4j (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g6]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
            cupClose1
          · rw [dif_neg g6]
            by_cases g7 : (C4j (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
            · rw [dif_pos g7]
              by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g8]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                cupClose1
              · rw [dif_neg g8]
                by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g9]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  cupClose1
                · rw [dif_neg g9]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  cupClose1
            · rw [dif_neg g7]
              by_cases g10 : (C4j (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
              · rw [dif_pos g10]
                by_cases g11 : (C4b (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                · rw [dif_pos g11]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                  cupClose1
                · rw [dif_neg g11]
                  by_cases g12 : (C4a (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                  · rw [dif_pos g12]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                    cupClose1
                  · rw [dif_neg g12]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                    cupClose1
              · rw [dif_neg g10]
                by_cases g13 : (C4j (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                · rw [dif_pos g13]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  cupClose1
                · rw [dif_neg g13]
                  by_cases g14 : (C4b (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                  · rw [dif_pos g14]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                    cupClose1
                  · rw [dif_neg g14]
                    by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g15]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                      cupClose1
                    · rw [dif_neg g15]
                      by_cases g16 : m = 2
                      · rw [dif_pos g16]
                        by_cases g17 : (C4a (mkT4 n m ((C3a p).val - 1) ((C3b p).val + 1) ((C3c p).val) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                        · rw [dif_pos g17]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                          cupClose1
                        · rw [dif_neg g17]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                          cupClose1
                      · rw [dif_neg g16]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                        cupClose1
      · rw [dif_neg h3]
        have hA := (C3a p).isLt
        have hB := (C3b p).isLt
        have hC := (C3c p).isLt
        have hJ := (C3j p).isLt
        have hH := C3h p
        simp only [idxT2, cup3Swap_T2, swapT2]
        by_cases g1 : 1 ≤ (mkT2 n m ((C3b p).val + 1) ((C3c p).val) (by omega) (by omega)).1.val
        · rw [dif_pos g1]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          cupClose1
        · rw [dif_neg g1]
          by_cases g2 : 1 ≤ (mkT2 n m ((C3b p).val + 1) ((C3c p).val) (by omega) (by omega)).2.val
          · rw [dif_pos g2]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            cupClose1
          · rw [dif_neg g2]
            by_cases g3 : m = 2
            · rw [dif_pos g3]
              by_cases g4 : n = 2
              · rw [dif_pos g4]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                cupClose1
              · rw [dif_neg g4]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                cupClose1
            · rw [dif_neg g3]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              cupClose1
    · rw [dif_neg h2]
      by_cases h3 : (C3j p).val = (C3a p).val + 1
      · rw [dif_pos h3]
        by_cases h4 : 1 ≤ (C3c p).val
        · rw [dif_pos h4]
          have hA := (C3a p).isLt
          have hB := (C3b p).isLt
          have hC := (C3c p).isLt
          have hJ := (C3j p).isLt
          have hH := C3h p
          simp only [idxC4, cup3Swap_C4, swapC4]
          by_cases g1 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
          · rw [dif_pos g1]
            by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g2]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              cupClose1
            · rw [dif_neg g2]
              by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
              · rw [dif_neg g3]
                by_cases g4 : m = 2
                · rw [dif_pos g4]
                  by_cases g5 : (C4a (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                  · rw [dif_pos g5]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    cupClose1
                  · rw [dif_neg g5]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    cupClose1
                · rw [dif_neg g4]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  cupClose1
          · rw [dif_neg g1]
            by_cases g6 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g6]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
              cupClose1
            · rw [dif_neg g6]
              by_cases g7 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
              · rw [dif_pos g7]
                by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g8]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  cupClose1
                · rw [dif_neg g8]
                  by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g9]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    cupClose1
                  · rw [dif_neg g9]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    cupClose1
              · rw [dif_neg g7]
                by_cases g10 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                · rw [dif_pos g10]
                  by_cases g11 : (C4b (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                  · rw [dif_pos g11]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    cupClose1
                  · rw [dif_neg g11]
                    by_cases g12 : (C4a (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                    · rw [dif_pos g12]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                      cupClose1
                    · rw [dif_neg g12]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                      cupClose1
                · rw [dif_neg g10]
                  by_cases g13 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                  · rw [dif_pos g13]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    cupClose1
                  · rw [dif_neg g13]
                    by_cases g14 : (C4b (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                    · rw [dif_pos g14]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      cupClose1
                    · rw [dif_neg g14]
                      by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g15]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        cupClose1
                      · rw [dif_neg g15]
                        by_cases g16 : m = 2
                        · rw [dif_pos g16]
                          by_cases g17 : (C4a (mkT4 n m ((C3a p).val) ((C3b p).val + 1) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                          · rw [dif_pos g17]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                            cupClose1
                          · rw [dif_neg g17]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                            cupClose1
                        · rw [dif_neg g16]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                          cupClose1
        · rw [dif_neg h4]
          by_cases h5 : (C3b p).val + 4 ≤ m
          · rw [dif_pos h5]
            have hA := (C3a p).isLt
            have hB := (C3b p).isLt
            have hC := (C3c p).isLt
            have hJ := (C3j p).isLt
            have hH := C3h p
            simp only [idxC3, cup3Swap_C3, swapC3]
            by_cases g1 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g1]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              cupClose1
            · rw [dif_neg g1]
              by_cases g2 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g2]
                by_cases g3 : 1 ≤ (C3a (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g3]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  cupClose1
                · rw [dif_neg g3]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  cupClose1
              · rw [dif_neg g2]
                by_cases g4 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                · rw [dif_pos g4]
                  by_cases g5 : 1 ≤ (C3c (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g5]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    cupClose1
                  · rw [dif_neg g5]
                    by_cases g6 : (C3b (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
                    · rw [dif_pos g6]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      cupClose1
                    · rw [dif_neg g6]
                      by_cases g7 : (C3a (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                      · rw [dif_pos g7]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        cupClose1
                      · rw [dif_neg g7]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        cupClose1
                · rw [dif_neg g4]
                  by_cases g8 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                  · rw [dif_pos g8]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    cupClose1
                  · rw [dif_neg g8]
                    by_cases g9 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                    · rw [dif_pos g9]
                      by_cases g10 : 1 ≤ (C3c (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g10]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        cupClose1
                      · rw [dif_neg g10]
                        by_cases g11 : 1 ≤ (C3b (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g11]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          cupClose1
                        · rw [dif_neg g11]
                          by_cases g12 : 1 ≤ (C3a (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                          · rw [dif_pos g12]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                            cupClose1
                          · rw [dif_neg g12]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                            cupClose1
                    · rw [dif_neg g9]
                      by_cases g13 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                      · rw [dif_pos g13]
                        by_cases g14 : (C3a (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C3a p).val) ((C3b p).val + 1) 0 ((C3a p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                        · rw [dif_pos g14]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          cupClose1
                        · rw [dif_neg g14]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          cupClose1
                      · rw [dif_neg g13]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        cupClose1
          · rw [dif_neg h5]
            by_cases h6 : (C3a p).val + 3 ≤ n
            · rw [dif_pos h6]
              have hA := (C3a p).isLt
              have hB := (C3b p).isLt
              have hC := (C3c p).isLt
              have hJ := (C3j p).isLt
              have hH := C3h p
              simp only [idxC4, cup3Swap_C4, swapC4]
              by_cases g1 : (C4j (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
              · rw [dif_pos g1]
                by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g2]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  cupClose1
                · rw [dif_neg g2]
                  by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g3]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    cupClose1
                  · rw [dif_neg g3]
                    by_cases g4 : m = 2
                    · rw [dif_pos g4]
                      by_cases g5 : (C4a (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                      · rw [dif_pos g5]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        cupClose1
                      · rw [dif_neg g5]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        cupClose1
                    · rw [dif_neg g4]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      cupClose1
              · rw [dif_neg g1]
                by_cases g6 : (C4j (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g6]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  cupClose1
                · rw [dif_neg g6]
                  by_cases g7 : (C4j (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                  · rw [dif_pos g7]
                    by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g8]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      cupClose1
                    · rw [dif_neg g8]
                      by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g9]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        cupClose1
                      · rw [dif_neg g9]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        cupClose1
                  · rw [dif_neg g7]
                    by_cases g10 : (C4j (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                    · rw [dif_pos g10]
                      by_cases g11 : (C4b (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                      · rw [dif_pos g11]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        cupClose1
                      · rw [dif_neg g11]
                        by_cases g12 : (C4a (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                        · rw [dif_pos g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                        · rw [dif_neg g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                    · rw [dif_neg g10]
                      by_cases g13 : (C4j (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                      · rw [dif_pos g13]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        cupClose1
                      · rw [dif_neg g13]
                        by_cases g14 : (C4b (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                        · rw [dif_pos g14]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          cupClose1
                        · rw [dif_neg g14]
                          by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                          · rw [dif_pos g15]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            cupClose1
                          · rw [dif_neg g15]
                            by_cases g16 : m = 2
                            · rw [dif_pos g16]
                              by_cases g17 : (C4a (mkT4 n m ((C3a p).val) (m - 2) 0 (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                              · rw [dif_pos g17]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                cupClose1
                              · rw [dif_neg g17]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                cupClose1
                            · rw [dif_neg g16]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                              cupClose1
            · rw [dif_neg h6]
              have hA := (C3a p).isLt
              have hB := (C3b p).isLt
              have hC := (C3c p).isLt
              have hJ := (C3j p).isLt
              have hH := C3h p
              simp only [idxT1, cup3Swap_T1, swapT1]
              by_cases g1 : (mkT1 n m ((C3a p).val) ((m - 2)) (by omega) (by omega)).2.val + 3 ≤ m
              · rw [dif_pos g1]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                cupClose1
              · rw [dif_neg g1]
                by_cases g2 : (mkT1 n m ((C3a p).val) ((m - 2)) (by omega) (by omega)).1.val + 3 ≤ n
                · rw [dif_pos g2]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  cupClose1
                · rw [dif_neg g2]
                  by_cases g3 : m = 2
                  · rw [dif_pos g3]
                    by_cases g4 : n = 2
                    · rw [dif_pos g4]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      cupClose1
                    · rw [dif_neg g4]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      cupClose1
                  · rw [dif_neg g3]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    cupClose1
      · rw [dif_neg h3]
        by_cases h4 : (C3j p).val ≤ (C3a p).val + (C3c p).val + 1
        · rw [dif_pos h4]
          have hA := (C3a p).isLt
          have hB := (C3b p).isLt
          have hC := (C3c p).isLt
          have hJ := (C3j p).isLt
          have hH := C3h p
          simp only [idxL, cup3Swap_inl, swapL]
          by_cases g1 : (L3k (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g1]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            cupClose1
          · rw [dif_neg g1]
            by_cases g2 : (L3k (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3b (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
            · rw [dif_pos g2]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              cupClose1
            · rw [dif_neg g2]
              by_cases g3 : (L3k (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3b (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3c (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
              · rw [dif_pos g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
              · rw [dif_neg g3]
                by_cases g4 : (L3k (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3c (mkL n m ((C3j p).val + (C3b p).val) ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + m
                · rw [dif_pos g4]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  cupClose1
                · rw [dif_neg g4]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  cupClose1
        · rw [dif_neg h4]
          by_cases h5 : (C3j p).val = (C3a p).val + (C3c p).val + 2
          · rw [dif_pos h5]
            by_cases h6 : 1 ≤ (C3c p).val
            · rw [dif_pos h6]
              have hA := (C3a p).isLt
              have hB := (C3b p).isLt
              have hC := (C3c p).isLt
              have hJ := (C3j p).isLt
              have hH := C3h p
              simp only [idxC4, cup3Swap_C4, swapC4]
              by_cases g1 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
              · rw [dif_pos g1]
                by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g2]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  cupClose1
                · rw [dif_neg g2]
                  by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g3]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    cupClose1
                  · rw [dif_neg g3]
                    by_cases g4 : m = 2
                    · rw [dif_pos g4]
                      by_cases g5 : (C4a (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                      · rw [dif_pos g5]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        cupClose1
                      · rw [dif_neg g5]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        cupClose1
                    · rw [dif_neg g4]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      cupClose1
              · rw [dif_neg g1]
                by_cases g6 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g6]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  cupClose1
                · rw [dif_neg g6]
                  by_cases g7 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                  · rw [dif_pos g7]
                    by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g8]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      cupClose1
                    · rw [dif_neg g8]
                      by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g9]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        cupClose1
                      · rw [dif_neg g9]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        cupClose1
                  · rw [dif_neg g7]
                    by_cases g10 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                    · rw [dif_pos g10]
                      by_cases g11 : (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                      · rw [dif_pos g11]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        cupClose1
                      · rw [dif_neg g11]
                        by_cases g12 : (C4a (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                        · rw [dif_pos g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                        · rw [dif_neg g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                    · rw [dif_neg g10]
                      by_cases g13 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                      · rw [dif_pos g13]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        cupClose1
                      · rw [dif_neg g13]
                        by_cases g14 : (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                        · rw [dif_pos g14]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          cupClose1
                        · rw [dif_neg g14]
                          by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                          · rw [dif_pos g15]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            cupClose1
                          · rw [dif_neg g15]
                            by_cases g16 : m = 2
                            · rw [dif_pos g16]
                              by_cases g17 : (C4a (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val - 1) ((C3b p).val + 2) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                              · rw [dif_pos g17]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                cupClose1
                              · rw [dif_neg g17]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                cupClose1
                            · rw [dif_neg g16]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                              cupClose1
            · rw [dif_neg h6]
              by_cases h7 : 1 ≤ (C3b p).val
              · rw [dif_pos h7]
                have hA := (C3a p).isLt
                have hB := (C3b p).isLt
                have hC := (C3c p).isLt
                have hJ := (C3j p).isLt
                have hH := C3h p
                simp only [idxC3, cup3Swap_C3, swapC3]
                by_cases g1 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g1]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  cupClose1
                · rw [dif_neg g1]
                  by_cases g2 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g2]
                    by_cases g3 : 1 ≤ (C3a (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g3]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      cupClose1
                    · rw [dif_neg g3]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      cupClose1
                  · rw [dif_neg g2]
                    by_cases g4 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                    · rw [dif_pos g4]
                      by_cases g5 : 1 ≤ (C3c (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g5]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        cupClose1
                      · rw [dif_neg g5]
                        by_cases g6 : (C3b (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
                        · rw [dif_pos g6]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          cupClose1
                        · rw [dif_neg g6]
                          by_cases g7 : (C3a (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                          · rw [dif_pos g7]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            cupClose1
                          · rw [dif_neg g7]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            cupClose1
                    · rw [dif_neg g4]
                      by_cases g8 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                      · rw [dif_pos g8]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        cupClose1
                      · rw [dif_neg g8]
                        by_cases g9 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                        · rw [dif_pos g9]
                          by_cases g10 : 1 ≤ (C3c (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                          · rw [dif_pos g10]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            cupClose1
                          · rw [dif_neg g10]
                            by_cases g11 : 1 ≤ (C3b (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                            · rw [dif_pos g11]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                              cupClose1
                            · rw [dif_neg g11]
                              by_cases g12 : 1 ≤ (C3a (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                              · rw [dif_pos g12]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                                cupClose1
                              · rw [dif_neg g12]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                                cupClose1
                        · rw [dif_neg g9]
                          by_cases g13 : (C3j (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                          · rw [dif_pos g13]
                            by_cases g14 : (C3a (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C3a p).val) ((C3b p).val - 1) 0 ((C3a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                            · rw [dif_pos g14]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              cupClose1
                            · rw [dif_neg g14]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              cupClose1
                          · rw [dif_neg g13]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            cupClose1
              · rw [dif_neg h7]
                by_cases h8 : 1 ≤ (C3a p).val
                · rw [dif_pos h8]
                  have hA := (C3a p).isLt
                  have hB := (C3b p).isLt
                  have hC := (C3c p).isLt
                  have hJ := (C3j p).isLt
                  have hH := C3h p
                  simp only [idxC4, cup3Swap_C4, swapC4]
                  by_cases g1 : (C4j (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                  · rw [dif_pos g1]
                    by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g2]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      cupClose1
                    · rw [dif_neg g2]
                      by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g3]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        cupClose1
                      · rw [dif_neg g3]
                        by_cases g4 : m = 2
                        · rw [dif_pos g4]
                          by_cases g5 : (C4a (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                          · rw [dif_pos g5]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                            cupClose1
                          · rw [dif_neg g5]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                            cupClose1
                        · rw [dif_neg g4]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          cupClose1
                  · rw [dif_neg g1]
                    by_cases g6 : (C4j (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g6]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      cupClose1
                    · rw [dif_neg g6]
                      by_cases g7 : (C4j (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                      · rw [dif_pos g7]
                        by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g8]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          cupClose1
                        · rw [dif_neg g8]
                          by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                          · rw [dif_pos g9]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                            cupClose1
                          · rw [dif_neg g9]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                            cupClose1
                      · rw [dif_neg g7]
                        by_cases g10 : (C4j (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                        · rw [dif_pos g10]
                          by_cases g11 : (C4b (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                          · rw [dif_pos g11]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                            cupClose1
                          · rw [dif_neg g11]
                            by_cases g12 : (C4a (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                            · rw [dif_pos g12]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                              cupClose1
                            · rw [dif_neg g12]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                              cupClose1
                        · rw [dif_neg g10]
                          by_cases g13 : (C4j (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                          · rw [dif_pos g13]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            cupClose1
                          · rw [dif_neg g13]
                            by_cases g14 : (C4b (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                            · rw [dif_pos g14]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              cupClose1
                            · rw [dif_neg g14]
                              by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                              · rw [dif_pos g15]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                cupClose1
                              · rw [dif_neg g15]
                                by_cases g16 : m = 2
                                · rw [dif_pos g16]
                                  by_cases g17 : (C4a (mkT4 n m ((C3a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                                  · rw [dif_pos g17]
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                    cupClose1
                                  · rw [dif_neg g17]
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                    cupClose1
                                · rw [dif_neg g16]
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                  cupClose1
                · rw [dif_neg h8]
                  have hA := (C3a p).isLt
                  have hB := (C3b p).isLt
                  have hC := (C3c p).isLt
                  have hJ := (C3j p).isLt
                  have hH := C3h p
                  simp only [idxT2, cup3Swap_T2, swapT2]
                  by_cases g1 : 1 ≤ (mkT2 n m (0) (0) (by omega) (by omega)).1.val
                  · rw [dif_pos g1]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    cupClose1
                  · rw [dif_neg g1]
                    by_cases g2 : 1 ≤ (mkT2 n m (0) (0) (by omega) (by omega)).2.val
                    · rw [dif_pos g2]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      cupClose1
                    · rw [dif_neg g2]
                      by_cases g3 : m = 2
                      · rw [dif_pos g3]
                        by_cases g4 : n = 2
                        · rw [dif_pos g4]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          cupClose1
                        · rw [dif_neg g4]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          cupClose1
                      · rw [dif_neg g3]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        cupClose1
          · rw [dif_neg h5]
            by_cases h6 : (C3j p).val = (C3a p).val + (C3c p).val + 3
            · rw [dif_pos h6]
              by_cases h7 : (C3a p).val + (C3c p).val + 3 ≤ n
              · rw [dif_pos h7]
                have hA := (C3a p).isLt
                have hB := (C3b p).isLt
                have hC := (C3c p).isLt
                have hJ := (C3j p).isLt
                have hH := C3h p
                simp only [idxC4, cup3Swap_C4, swapC4]
                by_cases g1 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                · rw [dif_pos g1]
                  by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g2]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    cupClose1
                  · rw [dif_neg g2]
                    by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g3]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      cupClose1
                    · rw [dif_neg g3]
                      by_cases g4 : m = 2
                      · rw [dif_pos g4]
                        by_cases g5 : (C4a (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                        · rw [dif_pos g5]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                          cupClose1
                        · rw [dif_neg g5]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                          cupClose1
                      · rw [dif_neg g4]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        cupClose1
                · rw [dif_neg g1]
                  by_cases g6 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g6]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    cupClose1
                  · rw [dif_neg g6]
                    by_cases g7 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                    · rw [dif_pos g7]
                      by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g8]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        cupClose1
                      · rw [dif_neg g8]
                        by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g9]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          cupClose1
                        · rw [dif_neg g9]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          cupClose1
                    · rw [dif_neg g7]
                      by_cases g10 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                      · rw [dif_pos g10]
                        by_cases g11 : (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                        · rw [dif_pos g11]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          cupClose1
                        · rw [dif_neg g11]
                          by_cases g12 : (C4a (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                          · rw [dif_pos g12]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                            cupClose1
                          · rw [dif_neg g12]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                            cupClose1
                      · rw [dif_neg g10]
                        by_cases g13 : (C4j (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                        · rw [dif_pos g13]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          cupClose1
                        · rw [dif_neg g13]
                          by_cases g14 : (C4b (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                          · rw [dif_pos g14]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            cupClose1
                          · rw [dif_neg g14]
                            by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                            · rw [dif_pos g15]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                              cupClose1
                            · rw [dif_neg g15]
                              by_cases g16 : m = 2
                              · rw [dif_pos g16]
                                by_cases g17 : (C4a (mkT4 n m ((C3a p).val) ((C3b p).val) ((C3c p).val) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                                · rw [dif_pos g17]
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                  cupClose1
                                · rw [dif_neg g17]
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                  cupClose1
                              · rw [dif_neg g16]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                cupClose1
              · rw [dif_neg h7]
                have hA := (C3a p).isLt
                have hB := (C3b p).isLt
                have hC := (C3c p).isLt
                have hJ := (C3j p).isLt
                have hH := C3h p
                simp only [idxT1, cup3Swap_T1, swapT1]
                by_cases g1 : (mkT1 n m ((C3a p).val) ((C3b p).val) (by omega) (by omega)).2.val + 3 ≤ m
                · rw [dif_pos g1]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  cupClose1
                · rw [dif_neg g1]
                  by_cases g2 : (mkT1 n m ((C3a p).val) ((C3b p).val) (by omega) (by omega)).1.val + 3 ≤ n
                  · rw [dif_pos g2]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    cupClose1
                  · rw [dif_neg g2]
                    by_cases g3 : m = 2
                    · rw [dif_pos g3]
                      by_cases g4 : n = 2
                      · rw [dif_pos g4]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        cupClose1
                      · rw [dif_neg g4]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        cupClose1
                    · rw [dif_neg g3]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      cupClose1
            · rw [dif_neg h6]
              have hA := (C3a p).isLt
              have hB := (C3b p).isLt
              have hC := (C3c p).isLt
              have hJ := (C3j p).isLt
              have hH := C3h p
              simp only [idxL, cup3Swap_inl, swapL]
              by_cases g1 : (L3k (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g1]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                cupClose1
              · rw [dif_neg g1]
                by_cases g2 : (L3k (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3b (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                · rw [dif_pos g2]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  cupClose1
                · rw [dif_neg g2]
                  by_cases g3 : (L3k (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3b (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3c (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                  · rw [dif_pos g3]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    cupClose1
                  · rw [dif_neg g3]
                    by_cases g4 : (L3k (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3c (mkL n m ((C3j p).val + m - 3) ((C3a p).val) ((C3b p).val) ((C3c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + m
                    · rw [dif_pos g4]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      cupClose1
                    · rw [dif_neg g4]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      cupClose1

lemma swapC4_case (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T4Idx n m) :
    cup3Swap n m hn hm (cup3Swap n m hn hm (Sum.inr (Sum.inr (Sum.inl p)))) = Sum.inr (Sum.inr (Sum.inl p)) := by
  simp only [cup3Swap_C4]
  simp only [swapC4]
  by_cases h1 : (C4j p).val = 0
  · rw [dif_pos h1]
    by_cases h2 : 1 ≤ (C4b p).val
    · rw [dif_pos h2]
      have hA := (C4a p).isLt
      have hB := (C4b p).isLt
      have hC := (C4c p).isLt
      have hJ := (C4j p).isLt
      have hH := C4h p
      simp only [idxC3, cup3Swap_C3, swapC3]
      by_cases g1 : (C3j (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
      · rw [dif_pos g1]
        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
        cupClose1
      · rw [dif_neg g1]
        by_cases g2 : (C3j (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g2]
          by_cases g3 : 1 ≤ (C3a (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g3]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
            cupClose1
          · rw [dif_neg g3]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
            cupClose1
        · rw [dif_neg g2]
          by_cases g4 : (C3j (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
          · rw [dif_pos g4]
            by_cases g5 : 1 ≤ (C3c (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g5]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
              cupClose1
            · rw [dif_neg g5]
              by_cases g6 : (C3b (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
              · rw [dif_pos g6]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                cupClose1
              · rw [dif_neg g6]
                by_cases g7 : (C3a (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                · rw [dif_pos g7]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  cupClose1
                · rw [dif_neg g7]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  cupClose1
          · rw [dif_neg g4]
            by_cases g8 : (C3j (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
            · rw [dif_pos g8]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
              cupClose1
            · rw [dif_neg g8]
              by_cases g9 : (C3j (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
              · rw [dif_pos g9]
                by_cases g10 : 1 ≤ (C3c (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g10]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  cupClose1
                · rw [dif_neg g10]
                  by_cases g11 : 1 ≤ (C3b (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g11]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    cupClose1
                  · rw [dif_neg g11]
                    by_cases g12 : 1 ≤ (C3a (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g12]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                      cupClose1
                    · rw [dif_neg g12]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                      cupClose1
              · rw [dif_neg g9]
                by_cases g13 : (C3j (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                · rw [dif_pos g13]
                  by_cases g14 : (C3a (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val + 1) ((C4b p).val - 1) ((C4c p).val) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                  · rw [dif_pos g14]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                    cupClose1
                  · rw [dif_neg g14]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                    cupClose1
                · rw [dif_neg g13]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  cupClose1
    · rw [dif_neg h2]
      by_cases h3 : 1 ≤ (C4c p).val
      · rw [dif_pos h3]
        have hA := (C4a p).isLt
        have hB := (C4b p).isLt
        have hC := (C4c p).isLt
        have hJ := (C4j p).isLt
        have hH := C4h p
        simp only [idxC4, cup3Swap_C4, swapC4]
        by_cases g1 : (C4j (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
        · rw [dif_pos g1]
          by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g2]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            cupClose1
          · rw [dif_neg g2]
            by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g3]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              cupClose1
            · rw [dif_neg g3]
              by_cases g4 : m = 2
              · rw [dif_pos g4]
                by_cases g5 : (C4a (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                · rw [dif_pos g5]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  cupClose1
                · rw [dif_neg g5]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  cupClose1
              · rw [dif_neg g4]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                cupClose1
        · rw [dif_neg g1]
          by_cases g6 : (C4j (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g6]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
            cupClose1
          · rw [dif_neg g6]
            by_cases g7 : (C4j (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
            · rw [dif_pos g7]
              by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g8]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                cupClose1
              · rw [dif_neg g8]
                by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g9]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  cupClose1
                · rw [dif_neg g9]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  cupClose1
            · rw [dif_neg g7]
              by_cases g10 : (C4j (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
              · rw [dif_pos g10]
                by_cases g11 : (C4b (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                · rw [dif_pos g11]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                  cupClose1
                · rw [dif_neg g11]
                  by_cases g12 : (C4a (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                  · rw [dif_pos g12]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                    cupClose1
                  · rw [dif_neg g12]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                    cupClose1
              · rw [dif_neg g10]
                by_cases g13 : (C4j (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                · rw [dif_pos g13]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  cupClose1
                · rw [dif_neg g13]
                  by_cases g14 : (C4b (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                  · rw [dif_pos g14]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                    cupClose1
                  · rw [dif_neg g14]
                    by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g15]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                      cupClose1
                    · rw [dif_neg g15]
                      by_cases g16 : m = 2
                      · rw [dif_pos g16]
                        by_cases g17 : (C4a (mkT4 n m ((C4a p).val + 1) 0 ((C4c p).val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                        · rw [dif_pos g17]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                          cupClose1
                        · rw [dif_neg g17]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                          cupClose1
                      · rw [dif_neg g16]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                        cupClose1
      · rw [dif_neg h3]
        by_cases h4 : m = 2
        · rw [dif_pos h4]
          by_cases h5 : (C4a p).val + 3 = n
          · rw [dif_pos h5]
            have hA := (C4a p).isLt
            have hB := (C4b p).isLt
            have hC := (C4c p).isLt
            have hJ := (C4j p).isLt
            have hH := C4h p
            simp only [idxT1, cup3Swap_T1, swapT1]
            by_cases g1 : (mkT1 n m ((C4a p).val + 1) (0) (by omega) (by omega)).2.val + 3 ≤ m
            · rw [dif_pos g1]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              cupClose1
            · rw [dif_neg g1]
              by_cases g2 : (mkT1 n m ((C4a p).val + 1) (0) (by omega) (by omega)).1.val + 3 ≤ n
              · rw [dif_pos g2]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                cupClose1
              · rw [dif_neg g2]
                by_cases g3 : m = 2
                · rw [dif_pos g3]
                  by_cases g4 : n = 2
                  · rw [dif_pos g4]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    cupClose1
                  · rw [dif_neg g4]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    cupClose1
                · rw [dif_neg g3]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  cupClose1
          · rw [dif_neg h5]
            have hA := (C4a p).isLt
            have hB := (C4b p).isLt
            have hC := (C4c p).isLt
            have hJ := (C4j p).isLt
            have hH := C4h p
            simp only [idxC4, cup3Swap_C4, swapC4]
            by_cases g1 : (C4j (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
            · rw [dif_pos g1]
              by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g2]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                cupClose1
              · rw [dif_neg g2]
                by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g3]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  cupClose1
                · rw [dif_neg g3]
                  by_cases g4 : m = 2
                  · rw [dif_pos g4]
                    by_cases g5 : (C4a (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                    · rw [dif_pos g5]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      cupClose1
                    · rw [dif_neg g5]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      cupClose1
                  · rw [dif_neg g4]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    cupClose1
            · rw [dif_neg g1]
              by_cases g6 : (C4j (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g6]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                cupClose1
              · rw [dif_neg g6]
                by_cases g7 : (C4j (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                · rw [dif_pos g7]
                  by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g8]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    cupClose1
                  · rw [dif_neg g8]
                    by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g9]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      cupClose1
                    · rw [dif_neg g9]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      cupClose1
                · rw [dif_neg g7]
                  by_cases g10 : (C4j (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                  · rw [dif_pos g10]
                    by_cases g11 : (C4b (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                    · rw [dif_pos g11]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      cupClose1
                    · rw [dif_neg g11]
                      by_cases g12 : (C4a (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                      · rw [dif_pos g12]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                        cupClose1
                      · rw [dif_neg g12]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                        cupClose1
                  · rw [dif_neg g10]
                    by_cases g13 : (C4j (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                    · rw [dif_pos g13]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      cupClose1
                    · rw [dif_neg g13]
                      by_cases g14 : (C4b (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                      · rw [dif_pos g14]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        cupClose1
                      · rw [dif_neg g14]
                        by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g15]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                          cupClose1
                        · rw [dif_neg g15]
                          by_cases g16 : m = 2
                          · rw [dif_pos g16]
                            by_cases g17 : (C4a (mkT4 n m ((C4a p).val + 1) 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                            · rw [dif_pos g17]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                              cupClose1
                            · rw [dif_neg g17]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                              cupClose1
                          · rw [dif_neg g16]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                            cupClose1
        · rw [dif_neg h4]
          have hA := (C4a p).isLt
          have hB := (C4b p).isLt
          have hC := (C4c p).isLt
          have hJ := (C4j p).isLt
          have hH := C4h p
          simp only [idxC3, cup3Swap_C3, swapC3]
          by_cases g1 : (C3j (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g1]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            cupClose1
          · rw [dif_neg g1]
            by_cases g2 : (C3j (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g2]
              by_cases g3 : 1 ≤ (C3a (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
              · rw [dif_neg g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
            · rw [dif_neg g2]
              by_cases g4 : (C3j (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
              · rw [dif_pos g4]
                by_cases g5 : 1 ≤ (C3c (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g5]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  cupClose1
                · rw [dif_neg g5]
                  by_cases g6 : (C3b (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
                  · rw [dif_pos g6]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    cupClose1
                  · rw [dif_neg g6]
                    by_cases g7 : (C3a (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                    · rw [dif_pos g7]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      cupClose1
                    · rw [dif_neg g7]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      cupClose1
              · rw [dif_neg g4]
                by_cases g8 : (C3j (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                · rw [dif_pos g8]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  cupClose1
                · rw [dif_neg g8]
                  by_cases g9 : (C3j (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                  · rw [dif_pos g9]
                    by_cases g10 : 1 ≤ (C3c (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g10]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      cupClose1
                    · rw [dif_neg g10]
                      by_cases g11 : 1 ≤ (C3b (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g11]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        cupClose1
                      · rw [dif_neg g11]
                        by_cases g12 : 1 ≤ (C3a (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                        · rw [dif_neg g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                  · rw [dif_neg g9]
                    by_cases g13 : (C3j (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                    · rw [dif_pos g13]
                      by_cases g14 : (C3a (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val + 1) 0 0 ((C4a p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                      · rw [dif_pos g14]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        cupClose1
                      · rw [dif_neg g14]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        cupClose1
                    · rw [dif_neg g13]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      cupClose1
  · rw [dif_neg h1]
    by_cases h2 : (C4j p).val ≤ (C4b p).val
    · rw [dif_pos h2]
      have hA := (C4a p).isLt
      have hB := (C4b p).isLt
      have hC := (C4c p).isLt
      have hJ := (C4j p).isLt
      have hH := C4h p
      simp only [idxL, cup3Swap_inl, swapL]
      by_cases g1 : (L3k (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
      · rw [dif_pos g1]
        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
        cupClose1
      · rw [dif_neg g1]
        by_cases g2 : (L3k (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3b (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
        · rw [dif_pos g2]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
          cupClose1
        · rw [dif_neg g2]
          by_cases g3 : (L3k (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3b (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3c (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
          · rw [dif_pos g3]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
            cupClose1
          · rw [dif_neg g3]
            by_cases g4 : (L3k (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3c (mkL n m ((C4j p).val + (C4a p).val) ((C4a p).val) ((C4b p).val - 1) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + m
            · rw [dif_pos g4]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
              cupClose1
            · rw [dif_neg g4]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
              cupClose1
    · rw [dif_neg h2]
      by_cases h3 : (C4j p).val ≤ (C4b p).val + 1
      · rw [dif_pos h3]
        by_cases h4 : 1 ≤ (C4b p).val
        · rw [dif_pos h4]
          have hA := (C4a p).isLt
          have hB := (C4b p).isLt
          have hC := (C4c p).isLt
          have hJ := (C4j p).isLt
          have hH := C4h p
          simp only [idxC3, cup3Swap_C3, swapC3]
          by_cases g1 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g1]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            cupClose1
          · rw [dif_neg g1]
            by_cases g2 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g2]
              by_cases g3 : 1 ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
              · rw [dif_neg g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
            · rw [dif_neg g2]
              by_cases g4 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
              · rw [dif_pos g4]
                by_cases g5 : 1 ≤ (C3c (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g5]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  cupClose1
                · rw [dif_neg g5]
                  by_cases g6 : (C3b (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
                  · rw [dif_pos g6]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    cupClose1
                  · rw [dif_neg g6]
                    by_cases g7 : (C3a (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                    · rw [dif_pos g7]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      cupClose1
                    · rw [dif_neg g7]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      cupClose1
              · rw [dif_neg g4]
                by_cases g8 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                · rw [dif_pos g8]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  cupClose1
                · rw [dif_neg g8]
                  by_cases g9 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                  · rw [dif_pos g9]
                    by_cases g10 : 1 ≤ (C3c (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g10]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      cupClose1
                    · rw [dif_neg g10]
                      by_cases g11 : 1 ≤ (C3b (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g11]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        cupClose1
                      · rw [dif_neg g11]
                        by_cases g12 : 1 ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                        · rw [dif_neg g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                  · rw [dif_neg g9]
                    by_cases g13 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                    · rw [dif_pos g13]
                      by_cases g14 : (C3a (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val - 1) ((C4c p).val + 1) ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                      · rw [dif_pos g14]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        cupClose1
                      · rw [dif_neg g14]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        cupClose1
                    · rw [dif_neg g13]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      cupClose1
        · rw [dif_neg h4]
          by_cases h5 : 1 ≤ (C4a p).val
          · rw [dif_pos h5]
            have hA := (C4a p).isLt
            have hB := (C4b p).isLt
            have hC := (C4c p).isLt
            have hJ := (C4j p).isLt
            have hH := C4h p
            simp only [idxC4, cup3Swap_C4, swapC4]
            by_cases g1 : (C4j (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
            · rw [dif_pos g1]
              by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g2]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                cupClose1
              · rw [dif_neg g2]
                by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g3]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  cupClose1
                · rw [dif_neg g3]
                  by_cases g4 : m = 2
                  · rw [dif_pos g4]
                    by_cases g5 : (C4a (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                    · rw [dif_pos g5]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      cupClose1
                    · rw [dif_neg g5]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      cupClose1
                  · rw [dif_neg g4]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    cupClose1
            · rw [dif_neg g1]
              by_cases g6 : (C4j (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g6]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                cupClose1
              · rw [dif_neg g6]
                by_cases g7 : (C4j (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                · rw [dif_pos g7]
                  by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g8]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    cupClose1
                  · rw [dif_neg g8]
                    by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g9]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      cupClose1
                    · rw [dif_neg g9]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      cupClose1
                · rw [dif_neg g7]
                  by_cases g10 : (C4j (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                  · rw [dif_pos g10]
                    by_cases g11 : (C4b (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                    · rw [dif_pos g11]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      cupClose1
                    · rw [dif_neg g11]
                      by_cases g12 : (C4a (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                      · rw [dif_pos g12]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                        cupClose1
                      · rw [dif_neg g12]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                        cupClose1
                  · rw [dif_neg g10]
                    by_cases g13 : (C4j (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                    · rw [dif_pos g13]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      cupClose1
                    · rw [dif_neg g13]
                      by_cases g14 : (C4b (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                      · rw [dif_pos g14]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        cupClose1
                      · rw [dif_neg g14]
                        by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g15]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                          cupClose1
                        · rw [dif_neg g15]
                          by_cases g16 : m = 2
                          · rw [dif_pos g16]
                            by_cases g17 : (C4a (mkT4 n m ((C4a p).val - 1) 0 ((C4c p).val + 1) 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                            · rw [dif_pos g17]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                              cupClose1
                            · rw [dif_neg g17]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                              cupClose1
                          · rw [dif_neg g16]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                            cupClose1
          · rw [dif_neg h5]
            have hA := (C4a p).isLt
            have hB := (C4b p).isLt
            have hC := (C4c p).isLt
            have hJ := (C4j p).isLt
            have hH := C4h p
            simp only [idxT2, cup3Swap_T2, swapT2]
            by_cases g1 : 1 ≤ (mkT2 n m (0) ((C4c p).val + 1) (by omega) (by omega)).1.val
            · rw [dif_pos g1]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              cupClose1
            · rw [dif_neg g1]
              by_cases g2 : 1 ≤ (mkT2 n m (0) ((C4c p).val + 1) (by omega) (by omega)).2.val
              · rw [dif_pos g2]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                cupClose1
              · rw [dif_neg g2]
                by_cases g3 : m = 2
                · rw [dif_pos g3]
                  by_cases g4 : n = 2
                  · rw [dif_pos g4]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    cupClose1
                  · rw [dif_neg g4]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    cupClose1
                · rw [dif_neg g3]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  cupClose1
      · rw [dif_neg h3]
        by_cases h4 : (C4j p).val ≤ (C4b p).val + 2
        · rw [dif_pos h4]
          by_cases h5 : (C4b p).val + 3 ≤ m
          · rw [dif_pos h5]
            have hA := (C4a p).isLt
            have hB := (C4b p).isLt
            have hC := (C4c p).isLt
            have hJ := (C4j p).isLt
            have hH := C4h p
            simp only [idxC3, cup3Swap_C3, swapC3]
            by_cases g1 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g1]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              cupClose1
            · rw [dif_neg g1]
              by_cases g2 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g2]
                by_cases g3 : 1 ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g3]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  cupClose1
                · rw [dif_neg g3]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  cupClose1
              · rw [dif_neg g2]
                by_cases g4 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                · rw [dif_pos g4]
                  by_cases g5 : 1 ≤ (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g5]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    cupClose1
                  · rw [dif_neg g5]
                    by_cases g6 : (C3b (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
                    · rw [dif_pos g6]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      cupClose1
                    · rw [dif_neg g6]
                      by_cases g7 : (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                      · rw [dif_pos g7]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        cupClose1
                      · rw [dif_neg g7]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        cupClose1
                · rw [dif_neg g4]
                  by_cases g8 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                  · rw [dif_pos g8]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    cupClose1
                  · rw [dif_neg g8]
                    by_cases g9 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                    · rw [dif_pos g9]
                      by_cases g10 : 1 ≤ (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g10]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        cupClose1
                      · rw [dif_neg g10]
                        by_cases g11 : 1 ≤ (C3b (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g11]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          cupClose1
                        · rw [dif_neg g11]
                          by_cases g12 : 1 ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                          · rw [dif_pos g12]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                            cupClose1
                          · rw [dif_neg g12]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                            cupClose1
                    · rw [dif_neg g9]
                      by_cases g13 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                      · rw [dif_pos g13]
                        by_cases g14 : (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val + 1) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                        · rw [dif_pos g14]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          cupClose1
                        · rw [dif_neg g14]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          cupClose1
                      · rw [dif_neg g13]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        cupClose1
          · rw [dif_neg h5]
            by_cases h6 : (C4a p).val + (C4c p).val + 4 ≤ n
            · rw [dif_pos h6]
              have hA := (C4a p).isLt
              have hB := (C4b p).isLt
              have hC := (C4c p).isLt
              have hJ := (C4j p).isLt
              have hH := C4h p
              simp only [idxC4, cup3Swap_C4, swapC4]
              by_cases g1 : (C4j (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
              · rw [dif_pos g1]
                by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g2]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  cupClose1
                · rw [dif_neg g2]
                  by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g3]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    cupClose1
                  · rw [dif_neg g3]
                    by_cases g4 : m = 2
                    · rw [dif_pos g4]
                      by_cases g5 : (C4a (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                      · rw [dif_pos g5]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        cupClose1
                      · rw [dif_neg g5]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        cupClose1
                    · rw [dif_neg g4]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      cupClose1
              · rw [dif_neg g1]
                by_cases g6 : (C4j (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g6]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  cupClose1
                · rw [dif_neg g6]
                  by_cases g7 : (C4j (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                  · rw [dif_pos g7]
                    by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g8]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      cupClose1
                    · rw [dif_neg g8]
                      by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g9]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        cupClose1
                      · rw [dif_neg g9]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        cupClose1
                  · rw [dif_neg g7]
                    by_cases g10 : (C4j (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                    · rw [dif_pos g10]
                      by_cases g11 : (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                      · rw [dif_pos g11]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        cupClose1
                      · rw [dif_neg g11]
                        by_cases g12 : (C4a (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                        · rw [dif_pos g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                        · rw [dif_neg g12]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                          cupClose1
                    · rw [dif_neg g10]
                      by_cases g13 : (C4j (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                      · rw [dif_pos g13]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        cupClose1
                      · rw [dif_neg g13]
                        by_cases g14 : (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                        · rw [dif_pos g14]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          cupClose1
                        · rw [dif_neg g14]
                          by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                          · rw [dif_pos g15]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            cupClose1
                          · rw [dif_neg g15]
                            by_cases g16 : m = 2
                            · rw [dif_pos g16]
                              by_cases g17 : (C4a (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val + 1) (m + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                              · rw [dif_pos g17]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                cupClose1
                              · rw [dif_neg g17]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                cupClose1
                            · rw [dif_neg g16]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                              cupClose1
            · rw [dif_neg h6]
              have hA := (C4a p).isLt
              have hB := (C4b p).isLt
              have hC := (C4c p).isLt
              have hJ := (C4j p).isLt
              have hH := C4h p
              simp only [idxT1, cup3Swap_T1, swapT1]
              by_cases g1 : (mkT1 n m ((C4a p).val) ((m - 2)) (by omega) (by omega)).2.val + 3 ≤ m
              · rw [dif_pos g1]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                cupClose1
              · rw [dif_neg g1]
                by_cases g2 : (mkT1 n m ((C4a p).val) ((m - 2)) (by omega) (by omega)).1.val + 3 ≤ n
                · rw [dif_pos g2]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  cupClose1
                · rw [dif_neg g2]
                  by_cases g3 : m = 2
                  · rw [dif_pos g3]
                    by_cases g4 : n = 2
                    · rw [dif_pos g4]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      cupClose1
                    · rw [dif_neg g4]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      cupClose1
                  · rw [dif_neg g3]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    cupClose1
        · rw [dif_neg h4]
          by_cases h5 : (C4j p).val ≤ m
          · rw [dif_pos h5]
            have hA := (C4a p).isLt
            have hB := (C4b p).isLt
            have hC := (C4c p).isLt
            have hJ := (C4j p).isLt
            have hH := C4h p
            simp only [idxL, cup3Swap_inl, swapL]
            by_cases g1 : (L3k (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g1]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              cupClose1
            · rw [dif_neg g1]
              by_cases g2 : (L3k (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3b (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
              · rw [dif_pos g2]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                cupClose1
              · rw [dif_neg g2]
                by_cases g3 : (L3k (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3b (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3c (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                · rw [dif_pos g3]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  cupClose1
                · rw [dif_neg g3]
                  by_cases g4 : (L3k (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (L3a (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (L3c (mkL n m ((C4j p).val + (C4a p).val + (C4c p).val) ((C4a p).val) ((C4b p).val) ((C4c p).val) (by omega) (by omega) (by omega) (by omega) (by omega))).val + m
                  · rw [dif_pos g4]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    cupClose1
                  · rw [dif_neg g4]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    cupClose1
          · rw [dif_neg h5]
            by_cases h6 : (C4b p).val + 3 ≤ m
            · rw [dif_pos h6]
              have hA := (C4a p).isLt
              have hB := (C4b p).isLt
              have hC := (C4c p).isLt
              have hJ := (C4j p).isLt
              have hH := C4h p
              simp only [idxC3, cup3Swap_C3, swapC3]
              by_cases g1 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g1]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                cupClose1
              · rw [dif_neg g1]
                by_cases g2 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g2]
                  by_cases g3 : 1 ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g3]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    cupClose1
                  · rw [dif_neg g3]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    cupClose1
                · rw [dif_neg g2]
                  by_cases g4 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                  · rw [dif_pos g4]
                    by_cases g5 : 1 ≤ (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g5]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                      cupClose1
                    · rw [dif_neg g5]
                      by_cases g6 : (C3b (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
                      · rw [dif_pos g6]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        cupClose1
                      · rw [dif_neg g6]
                        by_cases g7 : (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                        · rw [dif_pos g7]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          cupClose1
                        · rw [dif_neg g7]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          cupClose1
                  · rw [dif_neg g4]
                    by_cases g8 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                    · rw [dif_pos g8]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      cupClose1
                    · rw [dif_neg g8]
                      by_cases g9 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                      · rw [dif_pos g9]
                        by_cases g10 : 1 ≤ (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g10]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          cupClose1
                        · rw [dif_neg g10]
                          by_cases g11 : 1 ≤ (C3b (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                          · rw [dif_pos g11]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                            cupClose1
                          · rw [dif_neg g11]
                            by_cases g12 : 1 ≤ (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                            · rw [dif_pos g12]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                              cupClose1
                            · rw [dif_neg g12]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                              cupClose1
                      · rw [dif_neg g9]
                        by_cases g13 : (C3j (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                        · rw [dif_pos g13]
                          by_cases g14 : (C3a (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) ((C4b p).val) ((C4c p).val) ((C4a p).val + (C4c p).val + 3) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                          · rw [dif_pos g14]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            cupClose1
                          · rw [dif_neg g14]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            cupClose1
                        · rw [dif_neg g13]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          cupClose1
            · rw [dif_neg h6]
              by_cases h7 : 1 ≤ (C4c p).val
              · rw [dif_pos h7]
                have hA := (C4a p).isLt
                have hB := (C4b p).isLt
                have hC := (C4c p).isLt
                have hJ := (C4j p).isLt
                have hH := C4h p
                simp only [idxC4, cup3Swap_C4, swapC4]
                by_cases g1 : (C4j (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                · rw [dif_pos g1]
                  by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g2]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    cupClose1
                  · rw [dif_neg g2]
                    by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g3]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                      cupClose1
                    · rw [dif_neg g3]
                      by_cases g4 : m = 2
                      · rw [dif_pos g4]
                        by_cases g5 : (C4a (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                        · rw [dif_pos g5]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                          cupClose1
                        · rw [dif_neg g5]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                          cupClose1
                      · rw [dif_neg g4]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        cupClose1
                · rw [dif_neg g1]
                  by_cases g6 : (C4j (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g6]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    cupClose1
                  · rw [dif_neg g6]
                    by_cases g7 : (C4j (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                    · rw [dif_pos g7]
                      by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g8]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        cupClose1
                      · rw [dif_neg g8]
                        by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g9]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          cupClose1
                        · rw [dif_neg g9]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                          cupClose1
                    · rw [dif_neg g7]
                      by_cases g10 : (C4j (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                      · rw [dif_pos g10]
                        by_cases g11 : (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                        · rw [dif_pos g11]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                          cupClose1
                        · rw [dif_neg g11]
                          by_cases g12 : (C4a (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                          · rw [dif_pos g12]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                            cupClose1
                          · rw [dif_neg g12]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                            cupClose1
                      · rw [dif_neg g10]
                        by_cases g13 : (C4j (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                        · rw [dif_pos g13]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          cupClose1
                        · rw [dif_neg g13]
                          by_cases g14 : (C4b (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                          · rw [dif_pos g14]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            cupClose1
                          · rw [dif_neg g14]
                            by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
                            · rw [dif_pos g15]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                              cupClose1
                            · rw [dif_neg g15]
                              by_cases g16 : m = 2
                              · rw [dif_pos g16]
                                by_cases g17 : (C4a (mkT4 n m ((C4a p).val) (m - 2) ((C4c p).val - 1) m (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                                · rw [dif_pos g17]
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                  cupClose1
                                · rw [dif_neg g17]
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                  cupClose1
                              · rw [dif_neg g16]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                cupClose1
              · rw [dif_neg h7]
                by_cases h8 : m = 2
                · rw [dif_pos h8]
                  by_cases h9 : (C4a p).val = 0
                  · rw [dif_pos h9]
                    have hA := (C4a p).isLt
                    have hB := (C4b p).isLt
                    have hC := (C4c p).isLt
                    have hJ := (C4j p).isLt
                    have hH := C4h p
                    simp only [idxT2, cup3Swap_T2, swapT2]
                    by_cases g1 : 1 ≤ (mkT2 n m (0) (0) (by omega) (by omega)).1.val
                    · rw [dif_pos g1]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      cupClose1
                    · rw [dif_neg g1]
                      by_cases g2 : 1 ≤ (mkT2 n m (0) (0) (by omega) (by omega)).2.val
                      · rw [dif_pos g2]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        cupClose1
                      · rw [dif_neg g2]
                        by_cases g3 : m = 2
                        · rw [dif_pos g3]
                          by_cases g4 : n = 2
                          · rw [dif_pos g4]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            cupClose1
                          · rw [dif_neg g4]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            cupClose1
                        · rw [dif_neg g3]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                          cupClose1
                  · rw [dif_neg h9]
                    have hA := (C4a p).isLt
                    have hB := (C4b p).isLt
                    have hC := (C4c p).isLt
                    have hJ := (C4j p).isLt
                    have hH := C4h p
                    simp only [idxC4, cup3Swap_C4, swapC4]
                    by_cases g1 : (C4j (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                    · rw [dif_pos g1]
                      by_cases g2 : 1 ≤ (C4b (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g2]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        cupClose1
                      · rw [dif_neg g2]
                        by_cases g3 : 1 ≤ (C4c (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g3]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                          cupClose1
                        · rw [dif_neg g3]
                          by_cases g4 : m = 2
                          · rw [dif_pos g4]
                            by_cases g5 : (C4a (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                            · rw [dif_pos g5]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                              cupClose1
                            · rw [dif_neg g5]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                              cupClose1
                          · rw [dif_neg g4]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            cupClose1
                    · rw [dif_neg g1]
                      by_cases g6 : (C4j (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g6]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        cupClose1
                      · rw [dif_neg g6]
                        by_cases g7 : (C4j (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                        · rw [dif_pos g7]
                          by_cases g8 : 1 ≤ (C4b (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                          · rw [dif_pos g8]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                            cupClose1
                          · rw [dif_neg g8]
                            by_cases g9 : 1 ≤ (C4a (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                            · rw [dif_pos g9]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                              cupClose1
                            · rw [dif_neg g9]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                              cupClose1
                        · rw [dif_neg g7]
                          by_cases g10 : (C4j (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                          · rw [dif_pos g10]
                            by_cases g11 : (C4b (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                            · rw [dif_pos g11]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                              cupClose1
                            · rw [dif_neg g11]
                              by_cases g12 : (C4a (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                              · rw [dif_pos g12]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                                cupClose1
                              · rw [dif_neg g12]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                                cupClose1
                          · rw [dif_neg g10]
                            by_cases g13 : (C4j (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                            · rw [dif_pos g13]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              cupClose1
                            · rw [dif_neg g13]
                              by_cases g14 : (C4b (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                              · rw [dif_pos g14]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                cupClose1
                              · rw [dif_neg g14]
                                by_cases g15 : 1 ≤ (C4c (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                                · rw [dif_pos g15]
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                  cupClose1
                                · rw [dif_neg g15]
                                  by_cases g16 : m = 2
                                  · rw [dif_pos g16]
                                    by_cases g17 : (C4a (mkT4 n m ((C4a p).val - 1) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                                    · rw [dif_pos g17]
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                      cupClose1
                                    · rw [dif_neg g17]
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                                      cupClose1
                                  · rw [dif_neg g16]
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                                    cupClose1
                · rw [dif_neg h8]
                  have hA := (C4a p).isLt
                  have hB := (C4b p).isLt
                  have hC := (C4c p).isLt
                  have hJ := (C4j p).isLt
                  have hH := C4h p
                  simp only [idxC3, cup3Swap_C3, swapC3]
                  by_cases g1 : (C3j (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g1]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    cupClose1
                  · rw [dif_neg g1]
                    by_cases g2 : (C3j (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g2]
                      by_cases g3 : 1 ≤ (C3a (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g3]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        cupClose1
                      · rw [dif_neg g3]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                        cupClose1
                    · rw [dif_neg g2]
                      by_cases g4 : (C3j (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                      · rw [dif_pos g4]
                        by_cases g5 : 1 ≤ (C3c (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                        · rw [dif_pos g5]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                          cupClose1
                        · rw [dif_neg g5]
                          by_cases g6 : (C3b (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
                          · rw [dif_pos g6]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            cupClose1
                          · rw [dif_neg g6]
                            by_cases g7 : (C3a (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                            · rw [dif_pos g7]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              cupClose1
                            · rw [dif_neg g7]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                              cupClose1
                      · rw [dif_neg g4]
                        by_cases g8 : (C3j (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
                        · rw [dif_pos g8]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                          cupClose1
                        · rw [dif_neg g8]
                          by_cases g9 : (C3j (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                          · rw [dif_pos g9]
                            by_cases g10 : 1 ≤ (C3c (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                            · rw [dif_pos g10]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                              cupClose1
                            · rw [dif_neg g10]
                              by_cases g11 : 1 ≤ (C3b (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                              · rw [dif_pos g11]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                                cupClose1
                              · rw [dif_neg g11]
                                by_cases g12 : 1 ≤ (C3a (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                                · rw [dif_pos g12]
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                                  cupClose1
                                · rw [dif_neg g12]
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                                  cupClose1
                          · rw [dif_neg g9]
                            by_cases g13 : (C3j (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                            · rw [dif_pos g13]
                              by_cases g14 : (C3a (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m ((C4a p).val) (m - 3) 0 ((C4a p).val + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                              · rw [dif_pos g14]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                cupClose1
                              · rw [dif_neg g14]
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                                cupClose1
                            · rw [dif_neg g13]
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                              cupClose1

lemma swapT1_case (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T1Idx n m) :
    cup3Swap n m hn hm (cup3Swap n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))) = Sum.inr (Sum.inr (Sum.inr (Sum.inl p))) := by
  simp only [cup3Swap_T1]
  simp only [swapT1]
  by_cases h1 : p.2.val + 3 ≤ m
  · rw [dif_pos h1]
    have hA := p.1.isLt
    have hB := p.2.isLt
    simp only [idxC3, cup3Swap_C3, swapC3]
    by_cases g1 : (C3j (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
    · rw [dif_pos g1]
      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
      cupClose1
    · rw [dif_neg g1]
      by_cases g2 : (C3j (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
      · rw [dif_pos g2]
        by_cases g3 : 1 ≤ (C3a (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g3]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
          cupClose1
        · rw [dif_neg g3]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
          cupClose1
      · rw [dif_neg g2]
        by_cases g4 : (C3j (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
        · rw [dif_pos g4]
          by_cases g5 : 1 ≤ (C3c (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g5]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
            cupClose1
          · rw [dif_neg g5]
            by_cases g6 : (C3b (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
            · rw [dif_pos g6]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
              cupClose1
            · rw [dif_neg g6]
              by_cases g7 : (C3a (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
              · rw [dif_pos g7]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                cupClose1
              · rw [dif_neg g7]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                cupClose1
        · rw [dif_neg g4]
          by_cases g8 : (C3j (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
          · rw [dif_pos g8]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
            cupClose1
          · rw [dif_neg g8]
            by_cases g9 : (C3j (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
            · rw [dif_pos g9]
              by_cases g10 : 1 ≤ (C3c (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g10]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                cupClose1
              · rw [dif_neg g10]
                by_cases g11 : 1 ≤ (C3b (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g11]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                  cupClose1
                · rw [dif_neg g11]
                  by_cases g12 : 1 ≤ (C3a (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g12]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                    cupClose1
                  · rw [dif_neg g12]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                    cupClose1
            · rw [dif_neg g9]
              by_cases g13 : (C3j (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
              · rw [dif_pos g13]
                by_cases g14 : (C3a (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m p.1.val p.2.val (n - 2 - p.1.val) (n + 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                · rw [dif_pos g14]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                  cupClose1
                · rw [dif_neg g14]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                  cupClose1
              · rw [dif_neg g13]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                cupClose1
  · rw [dif_neg h1]
    by_cases h2 : p.1.val + 3 ≤ n
    · rw [dif_pos h2]
      have hA := p.1.isLt
      have hB := p.2.isLt
      simp only [idxC4, cup3Swap_C4, swapC4]
      by_cases g1 : (C4j (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
      · rw [dif_pos g1]
        by_cases g2 : 1 ≤ (C4b (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g2]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
          cupClose1
        · rw [dif_neg g2]
          by_cases g3 : 1 ≤ (C4c (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g3]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
            cupClose1
          · rw [dif_neg g3]
            by_cases g4 : m = 2
            · rw [dif_pos g4]
              by_cases g5 : (C4a (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
              · rw [dif_pos g5]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                cupClose1
              · rw [dif_neg g5]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                cupClose1
            · rw [dif_neg g4]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
              cupClose1
      · rw [dif_neg g1]
        by_cases g6 : (C4j (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g6]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
          cupClose1
        · rw [dif_neg g6]
          by_cases g7 : (C4j (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
          · rw [dif_pos g7]
            by_cases g8 : 1 ≤ (C4b (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g8]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
              cupClose1
            · rw [dif_neg g8]
              by_cases g9 : 1 ≤ (C4a (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g9]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                cupClose1
              · rw [dif_neg g9]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                cupClose1
          · rw [dif_neg g7]
            by_cases g10 : (C4j (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
            · rw [dif_pos g10]
              by_cases g11 : (C4b (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
              · rw [dif_pos g11]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                cupClose1
              · rw [dif_neg g11]
                by_cases g12 : (C4a (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                · rw [dif_pos g12]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                  cupClose1
                · rw [dif_neg g12]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                  cupClose1
            · rw [dif_neg g10]
              by_cases g13 : (C4j (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
              · rw [dif_pos g13]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                cupClose1
              · rw [dif_neg g13]
                by_cases g14 : (C4b (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                · rw [dif_pos g14]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                  cupClose1
                · rw [dif_neg g14]
                  by_cases g15 : 1 ≤ (C4c (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g15]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                    cupClose1
                  · rw [dif_neg g15]
                    by_cases g16 : m = 2
                    · rw [dif_pos g16]
                      by_cases g17 : (C4a (mkT4 n m p.1.val (m - 2) (n - 3 - p.1.val) m (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                      · rw [dif_pos g17]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                        cupClose1
                      · rw [dif_neg g17]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                        cupClose1
                    · rw [dif_neg g16]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                      cupClose1
    · rw [dif_neg h2]
      by_cases h3 : m = 2
      · rw [dif_pos h3]
        by_cases h4 : n = 2
        · rw [dif_pos h4]
          have hA := p.1.isLt
          have hB := p.2.isLt
          simp only [idxT2, cup3Swap_T2, swapT2]
          by_cases g1 : 1 ≤ (mkT2 n m (0) (0) (by omega) (by omega)).1.val
          · rw [dif_pos g1]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            cupClose1
          · rw [dif_neg g1]
            by_cases g2 : 1 ≤ (mkT2 n m (0) (0) (by omega) (by omega)).2.val
            · rw [dif_pos g2]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              cupClose1
            · rw [dif_neg g2]
              by_cases g3 : m = 2
              · rw [dif_pos g3]
                by_cases g4 : n = 2
                · rw [dif_pos g4]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  cupClose1
                · rw [dif_neg g4]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  cupClose1
              · rw [dif_neg g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
        · rw [dif_neg h4]
          have hA := p.1.isLt
          have hB := p.2.isLt
          simp only [idxC4, cup3Swap_C4, swapC4]
          by_cases g1 : (C4j (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
          · rw [dif_pos g1]
            by_cases g2 : 1 ≤ (C4b (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g2]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              cupClose1
            · rw [dif_neg g2]
              by_cases g3 : 1 ≤ (C4c (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
              · rw [dif_neg g3]
                by_cases g4 : m = 2
                · rw [dif_pos g4]
                  by_cases g5 : (C4a (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                  · rw [dif_pos g5]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    cupClose1
                  · rw [dif_neg g5]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    cupClose1
                · rw [dif_neg g4]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  cupClose1
          · rw [dif_neg g1]
            by_cases g6 : (C4j (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g6]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
              cupClose1
            · rw [dif_neg g6]
              by_cases g7 : (C4j (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
              · rw [dif_pos g7]
                by_cases g8 : 1 ≤ (C4b (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g8]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  cupClose1
                · rw [dif_neg g8]
                  by_cases g9 : 1 ≤ (C4a (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g9]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    cupClose1
                  · rw [dif_neg g9]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    cupClose1
              · rw [dif_neg g7]
                by_cases g10 : (C4j (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                · rw [dif_pos g10]
                  by_cases g11 : (C4b (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                  · rw [dif_pos g11]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    cupClose1
                  · rw [dif_neg g11]
                    by_cases g12 : (C4a (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                    · rw [dif_pos g12]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                      cupClose1
                    · rw [dif_neg g12]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                      cupClose1
                · rw [dif_neg g10]
                  by_cases g13 : (C4j (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                  · rw [dif_pos g13]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    cupClose1
                  · rw [dif_neg g13]
                    by_cases g14 : (C4b (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                    · rw [dif_pos g14]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      cupClose1
                    · rw [dif_neg g14]
                      by_cases g15 : 1 ≤ (C4c (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g15]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        cupClose1
                      · rw [dif_neg g15]
                        by_cases g16 : m = 2
                        · rw [dif_pos g16]
                          by_cases g17 : (C4a (mkT4 n m (n - 3) 0 0 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                          · rw [dif_pos g17]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                            cupClose1
                          · rw [dif_neg g17]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                            cupClose1
                        · rw [dif_neg g16]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                          cupClose1
      · rw [dif_neg h3]
        have hA := p.1.isLt
        have hB := p.2.isLt
        simp only [idxC3, cup3Swap_C3, swapC3]
        by_cases g1 : (C3j (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g1]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          cupClose1
        · rw [dif_neg g1]
          by_cases g2 : (C3j (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g2]
            by_cases g3 : 1 ≤ (C3a (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g3]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              cupClose1
            · rw [dif_neg g3]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              cupClose1
          · rw [dif_neg g2]
            by_cases g4 : (C3j (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
            · rw [dif_pos g4]
              by_cases g5 : 1 ≤ (C3c (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g5]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                cupClose1
              · rw [dif_neg g5]
                by_cases g6 : (C3b (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
                · rw [dif_pos g6]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  cupClose1
                · rw [dif_neg g6]
                  by_cases g7 : (C3a (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                  · rw [dif_pos g7]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    cupClose1
                  · rw [dif_neg g7]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    cupClose1
            · rw [dif_neg g4]
              by_cases g8 : (C3j (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
              · rw [dif_pos g8]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                cupClose1
              · rw [dif_neg g8]
                by_cases g9 : (C3j (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                · rw [dif_pos g9]
                  by_cases g10 : 1 ≤ (C3c (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g10]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    cupClose1
                  · rw [dif_neg g10]
                    by_cases g11 : 1 ≤ (C3b (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g11]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      cupClose1
                    · rw [dif_neg g11]
                      by_cases g12 : 1 ≤ (C3a (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g12]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                        cupClose1
                      · rw [dif_neg g12]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                        cupClose1
                · rw [dif_neg g9]
                  by_cases g13 : (C3j (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                  · rw [dif_pos g13]
                    by_cases g14 : (C3a (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m (n - 2) (m - 3) 0 (n - 1) (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                    · rw [dif_pos g14]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      cupClose1
                    · rw [dif_neg g14]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      cupClose1
                  · rw [dif_neg g13]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    cupClose1

lemma swapT2_case (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : T2Idx n m) :
    cup3Swap n m hn hm (cup3Swap n m hn hm (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))) = Sum.inr (Sum.inr (Sum.inr (Sum.inr p))) := by
  simp only [cup3Swap_T2]
  simp only [swapT2]
  by_cases h1 : 1 ≤ p.1.val
  · rw [dif_pos h1]
    have hA := p.1.isLt
    have hB := p.2.isLt
    simp only [idxC3, cup3Swap_C3, swapC3]
    by_cases g1 : (C3j (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
    · rw [dif_pos g1]
      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
      cupClose1
    · rw [dif_neg g1]
      by_cases g2 : (C3j (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
      · rw [dif_pos g2]
        by_cases g3 : 1 ≤ (C3a (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g3]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
          cupClose1
        · rw [dif_neg g3]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
          cupClose1
      · rw [dif_neg g2]
        by_cases g4 : (C3j (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
        · rw [dif_pos g4]
          by_cases g5 : 1 ≤ (C3c (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g5]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
            cupClose1
          · rw [dif_neg g5]
            by_cases g6 : (C3b (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
            · rw [dif_pos g6]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
              cupClose1
            · rw [dif_neg g6]
              by_cases g7 : (C3a (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
              · rw [dif_pos g7]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                cupClose1
              · rw [dif_neg g7]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                cupClose1
        · rw [dif_neg g4]
          by_cases g8 : (C3j (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
          · rw [dif_pos g8]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
            cupClose1
          · rw [dif_neg g8]
            by_cases g9 : (C3j (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
            · rw [dif_pos g9]
              by_cases g10 : 1 ≤ (C3c (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g10]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                cupClose1
              · rw [dif_neg g10]
                by_cases g11 : 1 ≤ (C3b (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g11]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                  cupClose1
                · rw [dif_neg g11]
                  by_cases g12 : 1 ≤ (C3a (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g12]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                    cupClose1
                  · rw [dif_neg g12]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                    cupClose1
            · rw [dif_neg g9]
              by_cases g13 : (C3j (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
              · rw [dif_pos g13]
                by_cases g14 : (C3a (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m 0 (p.1.val - 1) p.2.val 0 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                · rw [dif_pos g14]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                  cupClose1
                · rw [dif_neg g14]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                  cupClose1
              · rw [dif_neg g13]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                cupClose1
  · rw [dif_neg h1]
    by_cases h2 : 1 ≤ p.2.val
    · rw [dif_pos h2]
      have hA := p.1.isLt
      have hB := p.2.isLt
      simp only [idxC4, cup3Swap_C4, swapC4]
      by_cases g1 : (C4j (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
      · rw [dif_pos g1]
        by_cases g2 : 1 ≤ (C4b (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g2]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
          cupClose1
        · rw [dif_neg g2]
          by_cases g3 : 1 ≤ (C4c (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g3]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
            cupClose1
          · rw [dif_neg g3]
            by_cases g4 : m = 2
            · rw [dif_pos g4]
              by_cases g5 : (C4a (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
              · rw [dif_pos g5]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                cupClose1
              · rw [dif_neg g5]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                cupClose1
            · rw [dif_neg g4]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
              cupClose1
      · rw [dif_neg g1]
        by_cases g6 : (C4j (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g6]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
          cupClose1
        · rw [dif_neg g6]
          by_cases g7 : (C4j (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
          · rw [dif_pos g7]
            by_cases g8 : 1 ≤ (C4b (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g8]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
              cupClose1
            · rw [dif_neg g8]
              by_cases g9 : 1 ≤ (C4a (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g9]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                cupClose1
              · rw [dif_neg g9]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                cupClose1
          · rw [dif_neg g7]
            by_cases g10 : (C4j (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
            · rw [dif_pos g10]
              by_cases g11 : (C4b (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
              · rw [dif_pos g11]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                cupClose1
              · rw [dif_neg g11]
                by_cases g12 : (C4a (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                · rw [dif_pos g12]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                  cupClose1
                · rw [dif_neg g12]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                  cupClose1
            · rw [dif_neg g10]
              by_cases g13 : (C4j (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
              · rw [dif_pos g13]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                cupClose1
              · rw [dif_neg g13]
                by_cases g14 : (C4b (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                · rw [dif_pos g14]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                  cupClose1
                · rw [dif_neg g14]
                  by_cases g15 : 1 ≤ (C4c (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g15]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                    cupClose1
                  · rw [dif_neg g15]
                    by_cases g16 : m = 2
                    · rw [dif_pos g16]
                      by_cases g17 : (C4a (mkT4 n m 0 0 (p.2.val - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                      · rw [dif_pos g17]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                        cupClose1
                      · rw [dif_neg g17]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                        cupClose1
                    · rw [dif_neg g16]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                      cupClose1
    · rw [dif_neg h2]
      by_cases h3 : m = 2
      · rw [dif_pos h3]
        by_cases h4 : n = 2
        · rw [dif_pos h4]
          have hA := p.1.isLt
          have hB := p.2.isLt
          simp only [idxT1, cup3Swap_T1, swapT1]
          by_cases g1 : (mkT1 n m (0) (0) (by omega) (by omega)).2.val + 3 ≤ m
          · rw [dif_pos g1]
            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
            cupClose1
          · rw [dif_neg g1]
            by_cases g2 : (mkT1 n m (0) (0) (by omega) (by omega)).1.val + 3 ≤ n
            · rw [dif_pos g2]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              cupClose1
            · rw [dif_neg g2]
              by_cases g3 : m = 2
              · rw [dif_pos g3]
                by_cases g4 : n = 2
                · rw [dif_pos g4]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  cupClose1
                · rw [dif_neg g4]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  cupClose1
              · rw [dif_neg g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
        · rw [dif_neg h4]
          have hA := p.1.isLt
          have hB := p.2.isLt
          simp only [idxC4, cup3Swap_C4, swapC4]
          by_cases g1 : (C4j (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
          · rw [dif_pos g1]
            by_cases g2 : 1 ≤ (C4b (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g2]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              cupClose1
            · rw [dif_neg g2]
              by_cases g3 : 1 ≤ (C4c (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g3]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                cupClose1
              · rw [dif_neg g3]
                by_cases g4 : m = 2
                · rw [dif_pos g4]
                  by_cases g5 : (C4a (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 = n
                  · rw [dif_pos g5]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    cupClose1
                  · rw [dif_neg g5]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    cupClose1
                · rw [dif_neg g4]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  cupClose1
          · rw [dif_neg g1]
            by_cases g6 : (C4j (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g6]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
              cupClose1
            · rw [dif_neg g6]
              by_cases g7 : (C4j (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
              · rw [dif_pos g7]
                by_cases g8 : 1 ≤ (C4b (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                · rw [dif_pos g8]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                  cupClose1
                · rw [dif_neg g8]
                  by_cases g9 : 1 ≤ (C4a (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g9]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    cupClose1
                  · rw [dif_neg g9]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    cupClose1
              · rw [dif_neg g7]
                by_cases g10 : (C4j (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C4b (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                · rw [dif_pos g10]
                  by_cases g11 : (C4b (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                  · rw [dif_pos g11]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                    cupClose1
                  · rw [dif_neg g11]
                    by_cases g12 : (C4a (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C4c (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ n
                    · rw [dif_pos g12]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                      cupClose1
                    · rw [dif_neg g12]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                      cupClose1
                · rw [dif_neg g10]
                  by_cases g13 : (C4j (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ m
                  · rw [dif_pos g13]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    cupClose1
                  · rw [dif_neg g13]
                    by_cases g14 : (C4b (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ m
                    · rw [dif_pos g14]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      cupClose1
                    · rw [dif_neg g14]
                      by_cases g15 : 1 ≤ (C4c (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g15]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                        cupClose1
                      · rw [dif_neg g15]
                        by_cases g16 : m = 2
                        · rw [dif_pos g16]
                          by_cases g17 : (C4a (mkT4 n m 0 0 0 3 (by omega) (by omega) (by omega) (by omega) (by omega))).val = 0
                          · rw [dif_pos g17]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                            cupClose1
                          · rw [dif_neg g17]
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                            try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g17
                            cupClose1
                        · rw [dif_neg g16]
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g15
                          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g16
                          cupClose1
      · rw [dif_neg h3]
        have hA := p.1.isLt
        have hB := p.2.isLt
        simp only [idxC3, cup3Swap_C3, swapC3]
        by_cases g1 : (C3j (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1 ≤ (C3a (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val
        · rw [dif_pos g1]
          try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
          cupClose1
        · rw [dif_neg g1]
          by_cases g2 : (C3j (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val
          · rw [dif_pos g2]
            by_cases g3 : 1 ≤ (C3a (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val
            · rw [dif_pos g3]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              cupClose1
            · rw [dif_neg g3]
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
              try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g3
              cupClose1
          · rw [dif_neg g2]
            by_cases g4 : (C3j (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
            · rw [dif_pos g4]
              by_cases g5 : 1 ≤ (C3c (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val
              · rw [dif_pos g5]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                cupClose1
              · rw [dif_neg g5]
                by_cases g6 : (C3b (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 4 ≤ m
                · rw [dif_pos g6]
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                  try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                  cupClose1
                · rw [dif_neg g6]
                  by_cases g7 : (C3a (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                  · rw [dif_pos g7]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    cupClose1
                  · rw [dif_neg g7]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g5
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g6
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g7
                    cupClose1
            · rw [dif_neg g4]
              by_cases g8 : (C3j (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val ≤ (C3a (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 1
              · rw [dif_pos g8]
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                cupClose1
              · rw [dif_neg g8]
                by_cases g9 : (C3j (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 2
                · rw [dif_pos g9]
                  by_cases g10 : 1 ≤ (C3c (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                  · rw [dif_pos g10]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                    cupClose1
                  · rw [dif_neg g10]
                    by_cases g11 : 1 ≤ (C3b (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                    · rw [dif_pos g11]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                      cupClose1
                    · rw [dif_neg g11]
                      by_cases g12 : 1 ≤ (C3a (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val
                      · rw [dif_pos g12]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                        cupClose1
                      · rw [dif_neg g12]
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g10
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g11
                        try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g12
                        cupClose1
                · rw [dif_neg g9]
                  by_cases g13 : (C3j (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val = (C3a (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3
                  · rw [dif_pos g13]
                    by_cases g14 : (C3a (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + (C3c (mkT3 n m 0 0 0 2 (by omega) (by omega) (by omega) (by omega) (by omega))).val + 3 ≤ n
                    · rw [dif_pos g14]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      cupClose1
                    · rw [dif_neg g14]
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                      try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g14
                      cupClose1
                  · rw [dif_neg g13]
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g1
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g2
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g4
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g8
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g9
                    try simp only [C3a_mkT3, C3b_mkT3, C3c_mkT3, C3j_mkT3, C4a_mkT4, C4b_mkT4, C4c_mkT4, C4j_mkT4, L3a_mkL, L3b_mkL, L3c_mkL, L3k_mkL, mkT1, mkT2, Fin.val_mk] at g13
                    cupClose1


/-- The pairing involution `cup3Swap` is an involution. -/
theorem cup3SwapInvol (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    Function.Involutive (Work.Pi6.SQM.cup3Swap n m hn hm) := by
  intro x
  cases x with
  | inl p => exact swapL_case n m hn hm p
  | inr y =>
    cases y with
    | inl p => exact swapC3_case n m hn hm p
    | inr y =>
      cases y with
      | inl p => exact swapC4_case n m hn hm p
      | inr y =>
        cases y with
        | inl p => exact swapT1_case n m hn hm p
        | inr p => exact swapT2_case n m hn hm p

end Work.Pi6.SQM
