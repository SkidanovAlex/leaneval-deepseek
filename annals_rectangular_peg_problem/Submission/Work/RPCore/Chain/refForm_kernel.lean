import Mathlib
import Submission.Work.RPCore.Chain.C4Defs
import Submission.Work.RPCore.Chain.rotation_orbit
import Submission.Work.RPCore.Chain.seq_const_of_step
import Submission.Work.RPCore.Chain.seq_zero_of_step
import Submission.Work.RPCore.Chain.seq_zero_of_step_right

/-!
# The kernel of the reference polar form `BvForm n N δ`

`BvForm n N δ` is the explicit polar bilinear form of the quadratic part of the reference chain
action (see `C4Defs`).  On the chain space `ChainSp n = (Fin (n+1) → ℝ²) × (Fin n → ℝ²)` with
`n = 3N - 1`, the form decomposes into three blocks (`L = [0,N-1]`, `M = [N,2N-1]`,
`R = [2N,3N-2]`):

* the "grid" term `∑_j ⟨P_j, q_{j+1} - q_j⟩ + ⟨P'_j, q_{j+1} - q_j⟩`, which couples the first
  coordinate of `q` with the first coordinate of `P` along the chain and the *second* coordinate
  of `q` only with the second coordinate of `P`;
* a `(1/cos δ - 1)` term on the middle block, coupling `q¹_j` and `P¹_j`;
* a `tan δ` term on the middle block, coupling `q¹_j` with `q'¹_j` and `P¹_j` with `P'¹_j`.

Reading the test vectors `δ_qᵏ = (Pi.single k (1,0), 0)`, `(Pi.single k (0,1), 0)`,
`(0, Pi.single k (1,0))`, `(0, Pi.single k (0,1))` through the form (lemmas below) produces four
families of scalar equations which are solved here: the second coordinate of `q` is constant, the
second coordinate of `P` vanishes, the first coordinates of `q` and `P` vanish on the two outer
blocks, and on the middle block the pair `(q¹_k, P¹_{k-1})` rotates by `δ` at each step.  The
rotation being by `δ` per step over `N` steps and `sin (N δ) ≠ 0` forces the whole kernel to be
the diagonal line `ℝ ∙ diagVec n`.
-/

namespace Work.RPCore.Chain

open scoped BigOperators

noncomputable section

/-! ## Evaluating the form on the coordinate test vectors -/

lemma single_fst {n : ℕ} (k : Fin n) (v : ℝ×ℝ) (j : Fin n) :
    ((Pi.single k v : Fin n → ℝ×ℝ) j).1 = if j = k then v.1 else 0 := by
  rw [Pi.single_apply]; split <;> simp

lemma single_snd {n : ℕ} (k : Fin n) (v : ℝ×ℝ) (j : Fin n) :
    ((Pi.single k v : Fin n → ℝ×ℝ) j).2 = if j = k then v.2 else 0 := by
  rw [Pi.single_apply]; split <;> simp

lemma sum_succ_indicator {n : ℕ} (k : Fin (n+1)) (f : Fin n → ℝ) :
    (∑ j : Fin n, (if j.succ = k then f j else 0)) = if h : k = 0 then 0 else f (k.pred h) := by
  by_cases h : k = 0
  · subst h
    rw [dite_eq_left rfl]
    exact Finset.sum_eq_zero (fun j _ => by rw [ite_eq_right (Fin.succ_ne_zero j)])
  · rw [dite_eq_right h]
    have key : ∀ j : Fin n, (if j.succ = k then f j else 0) = (if j = k.pred h then f j else 0) := by
      intro j
      by_cases hjk : j = k.pred h
      · rw [ite_eq_left (by rw [hjk, Fin.succ_pred k h]), ite_eq_left hjk]
      · rw [ite_eq_right (fun hc => hjk (Fin.succ_injective n (by rw [hc, Fin.succ_pred k h]))),
          ite_eq_right hjk]
    rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_ite_eq']; simp

lemma sum_castSucc_indicator {n : ℕ} (k : Fin (n+1)) (f : Fin n → ℝ) :
    (∑ j : Fin n, (if j.castSucc = k then f j else 0))
      = if h : (k:ℕ) < n then f ⟨(k:ℕ), h⟩ else 0 := by
  by_cases h : (k:ℕ) < n
  · rw [dite_eq_left h]
    have key : ∀ j : Fin n, (if j.castSucc = k then f j else 0) = (if j = ⟨(k:ℕ), h⟩ then f j else 0) := by
      intro j
      by_cases hj : j = ⟨(k:ℕ), h⟩
      · rw [ite_eq_left, ite_eq_left hj]; apply Fin.ext; rw [hj]; simp
      · rw [ite_eq_right, ite_eq_right hj]; intro hc
        exact hj (Fin.ext (by simpa using congrArg Fin.val hc))
    rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_ite_eq']; simp
  · rw [dite_eq_right h]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [ite_eq_right]; intro hc
    have hv : (j.castSucc : ℕ) = (k:ℕ) := congrArg Fin.val hc
    simp at hv; omega

lemma ite_mid_combine {n N : ℕ} (k : Fin (n+1)) (j : Fin n) (t : ℝ) :
    (if midBlock N (j:ℕ) then (if j.castSucc = k then t else 0) else 0)
      = (if j.castSucc = k then (if midBlock N (j:ℕ) then t else 0) else 0) := by
  by_cases hm : midBlock N (j:ℕ) <;> by_cases hc : j.castSucc = k <;> simp [hm, hc]

lemma ite_mid_combine_eq {n N : ℕ} (k : Fin n) (j : Fin n) (t : ℝ) :
    (if midBlock N (j:ℕ) then (if j = k then t else 0) else 0)
      = (if j = k then (if midBlock N (j:ℕ) then t else 0) else 0) := by
  by_cases hm : midBlock N (j:ℕ) <;> by_cases hc : j = k <;> simp [hm, hc]

/-- Value of the form on the test vector `(Pi.single k (1,0), 0)` (`k : Fin (n+1)`). -/
lemma BvForm_deltaQ1 {n N : ℕ} (δ : ℝ) (z : ChainSp n) (k : Fin (n+1)) :
    BvForm n N δ z (Pi.single k ((1:ℝ),0), (0 : Fin n → ℝ×ℝ))
      = (if h : k = 0 then 0 else (z.2 (k.pred h)).1)
        - (if h : (k:ℕ) < n then (z.2 ⟨(k:ℕ), h⟩).1 else 0)
        - (1/Real.cos δ - 1) * (if h : (k:ℕ) < n then (if midBlock N (k:ℕ) then (z.2 ⟨(k:ℕ), h⟩).1 else 0) else 0)
        + Real.tan δ * (if h : (k:ℕ) < n then (if midBlock N (k:ℕ) then (z.1 k).1 else 0) else 0) := by
  simp only [BvForm, single_fst, single_snd, Pi.zero_apply, Prod.fst_zero, Prod.snd_zero,
    sub_zero, add_zero, zero_add, ite_self, ite_mul, mul_ite, mul_one, one_mul, zero_mul, mul_zero]
  have h1 : (∑ x : Fin n, (z.2 x).1 * ((if x.succ = k then (1:ℝ) else 0) - (if x.castSucc = k then 1 else 0)))
      = (if h : k = 0 then 0 else (z.2 (k.pred h)).1) - (if h : (k:ℕ) < n then (z.2 ⟨(k:ℕ), h⟩).1 else 0) := by
    rw [Finset.sum_congr rfl (fun x _ => by rw [mul_sub]), Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_congr rfl (fun x _ => by rw [mul_ite, mul_one, mul_zero])]
      rw [sum_succ_indicator]
    · rw [Finset.sum_congr rfl (fun x _ => by rw [mul_ite, mul_one, mul_zero])]
      rw [sum_castSucc_indicator]
  have h2 : (∑ x : Fin n, if midBlock N (x:ℕ) then (if x.castSucc = k then (z.2 x).1 else 0) else 0)
      = (if h : (k:ℕ) < n then (if midBlock N (k:ℕ) then (z.2 ⟨(k:ℕ), h⟩).1 else 0) else 0) := by
    rw [Finset.sum_congr rfl (fun x _ => ite_mid_combine k x ((z.2 x).1)), sum_castSucc_indicator]
  have h3 : (∑ x : Fin n, if midBlock N (x:ℕ) then (if x.castSucc = k then (z.1 x.castSucc).1 else 0) else 0)
      = (if h : (k:ℕ) < n then (if midBlock N (k:ℕ) then (z.1 k).1 else 0) else 0) := by
    rw [Finset.sum_congr rfl (fun x _ => ite_mid_combine k x ((z.1 x.castSucc).1))]
    have hA : (∑ x : Fin n, if x.castSucc = k then (if midBlock N (x:ℕ) then (z.1 x.castSucc).1 else 0) else 0)
        = (∑ x : Fin n, if x.castSucc = k then (if midBlock N (x:ℕ) then (z.1 k).1 else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hc : x.castSucc = k
      · rw [ite_eq_left hc, ite_eq_left hc, hc]
      · rw [ite_eq_right hc, ite_eq_right hc]
    rw [hA, sum_castSucc_indicator]
  rw [h1, h2, h3]

/-- Value of the form on the test vector `(Pi.single k (0,1), 0)` (`k : Fin (n+1)`). -/
lemma BvForm_deltaQ2 {n N : ℕ} (δ : ℝ) (z : ChainSp n) (k : Fin (n+1)) :
    BvForm n N δ z (Pi.single k ((0:ℝ),1), (0 : Fin n → ℝ×ℝ))
      = (if h : k = 0 then 0 else (z.2 (k.pred h)).2)
        - (if h : (k:ℕ) < n then (z.2 ⟨(k:ℕ), h⟩).2 else 0) := by
  simp only [BvForm, single_fst, single_snd, Pi.zero_apply, Prod.fst_zero, Prod.snd_zero,
    sub_zero, add_zero, zero_add, ite_self, ite_mul, mul_ite, mul_one, one_mul, zero_mul, mul_zero]
  have hT : (∑ x : Fin n, (z.2 x).2 * ((if x.succ = k then (1:ℝ) else 0) - (if x.castSucc = k then 1 else 0)))
      = (if h : k = 0 then 0 else (z.2 (k.pred h)).2) - (if h : (k:ℕ) < n then (z.2 ⟨(k:ℕ), h⟩).2 else 0) := by
    rw [Finset.sum_congr rfl (fun x _ => by rw [mul_sub]), Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_congr rfl (fun x _ => by rw [mul_ite, mul_one, mul_zero])]
      rw [sum_succ_indicator]
    · rw [Finset.sum_congr rfl (fun x _ => by rw [mul_ite, mul_one, mul_zero])]
      rw [sum_castSucc_indicator]
  rw [hT]; simp

/-- Value of the form on the test vector `(0, Pi.single k (1,0))` (`k : Fin n`). -/
lemma BvForm_deltaP1 {n N : ℕ} (δ : ℝ) (z : ChainSp n) (k : Fin n) :
    BvForm n N δ z ((0 : Fin (n+1) → ℝ×ℝ), Pi.single k ((1:ℝ),0))
      = ((z.1 k.succ).1 - (z.1 k.castSucc).1)
        - (1/Real.cos δ - 1) * (if midBlock N (k:ℕ) then (z.1 k.castSucc).1 else 0)
        + Real.tan δ * (if midBlock N (k:ℕ) then (z.2 k).1 else 0) := by
  simp only [BvForm, single_fst, single_snd, Pi.zero_apply, Prod.fst_zero, Prod.snd_zero,
    sub_zero, add_zero, zero_add, ite_self, ite_mul, mul_ite, mul_one, one_mul, zero_mul, mul_zero]
  have hT : (∑ x : Fin n, (if x = k then ((z.1 x.succ).1 - (z.1 x.castSucc).1) else 0))
      = (z.1 k.succ).1 - (z.1 k.castSucc).1 := by
    rw [Finset.sum_ite_eq']; simp
  have hM : (∑ x : Fin n, if midBlock N (x:ℕ) then (if x = k then (z.1 x.castSucc).1 else 0) else 0)
      = (if midBlock N (k:ℕ) then (z.1 k.castSucc).1 else 0) := by
    rw [Finset.sum_congr rfl (fun x _ => ite_mid_combine_eq k x ((z.1 x.castSucc).1)),
      Finset.sum_ite_eq']; simp
  have hM2 : (∑ x : Fin n, if midBlock N (x:ℕ) then (if x = k then (z.2 x).1 else 0) else 0)
      = (if midBlock N (k:ℕ) then (z.2 k).1 else 0) := by
    rw [Finset.sum_congr rfl (fun x _ => ite_mid_combine_eq k x ((z.2 x).1)),
      Finset.sum_ite_eq']; simp
  rw [hT, hM, hM2]
  by_cases hm : midBlock N (k:ℕ) <;> simp [hm]

/-- Value of the form on the test vector `(0, Pi.single k (0,1))` (`k : Fin n`). -/
lemma BvForm_deltaP2 {n N : ℕ} (δ : ℝ) (z : ChainSp n) (k : Fin n) :
    BvForm n N δ z ((0 : Fin (n+1) → ℝ×ℝ), Pi.single k ((0:ℝ),1))
      = (z.1 k.succ).2 - (z.1 k.castSucc).2 := by
  simp only [BvForm, single_fst, single_snd, Pi.zero_apply, Prod.fst_zero, Prod.snd_zero]
  simp only [sub_self, mul_zero, add_zero, zero_add, ite_self, ite_mul, mul_ite, mul_one,
    one_mul, zero_mul]
  rw [Finset.sum_ite_eq']; simp

/-! ## ℕ-indexed coordinate sequences -/

/-- First coordinate of the position `q_m`, totalised by `0` outside `[0,n]`. -/
def sq1 {n : ℕ} (z : ChainSp n) (m : ℕ) : ℝ := if h : m < n + 1 then (z.1 ⟨m, h⟩).1 else 0
/-- Second coordinate of the position `q_m`, totalised by `0` outside `[0,n]`. -/
def sq2 {n : ℕ} (z : ChainSp n) (m : ℕ) : ℝ := if h : m < n + 1 then (z.1 ⟨m, h⟩).2 else 0
/-- First coordinate of the momentum `P_m`, totalised by `0` outside `[0,n)`. -/
def sp1 {n : ℕ} (z : ChainSp n) (m : ℕ) : ℝ := if h : m < n then (z.2 ⟨m, h⟩).1 else 0
/-- Second coordinate of the momentum `P_m`, totalised by `0` outside `[0,n)`. -/
def sp2 {n : ℕ} (z : ChainSp n) (m : ℕ) : ℝ := if h : m < n then (z.2 ⟨m, h⟩).2 else 0

lemma sq1_of_le {n : ℕ} {z : ChainSp n} {m : ℕ} (h : m ≤ n) :
    sq1 z m = (z.1 ⟨m, Nat.lt_succ_of_le h⟩).1 := dite_eq_left (Nat.lt_succ_of_le h)
lemma sq2_of_le {n : ℕ} {z : ChainSp n} {m : ℕ} (h : m ≤ n) :
    sq2 z m = (z.1 ⟨m, Nat.lt_succ_of_le h⟩).2 := dite_eq_left (Nat.lt_succ_of_le h)
lemma sp1_of_lt {n : ℕ} {z : ChainSp n} {m : ℕ} (h : m < n) :
    sp1 z m = (z.2 ⟨m, h⟩).1 := dite_eq_left h
lemma sp2_of_lt {n : ℕ} {z : ChainSp n} {m : ℕ} (h : m < n) :
    sp2 z m = (z.2 ⟨m, h⟩).2 := dite_eq_left h

lemma sq1_mk {n : ℕ} (z : ChainSp n) {m : ℕ} (h : m < n + 1) : (z.1 ⟨m, h⟩).1 = sq1 z m := by
  rw [sq1_of_le (show m ≤ n by omega)]
lemma sq2_mk {n : ℕ} (z : ChainSp n) {m : ℕ} (h : m < n + 1) : (z.1 ⟨m, h⟩).2 = sq2 z m := by
  rw [sq2_of_le (show m ≤ n by omega)]
lemma sp1_mk {n : ℕ} (z : ChainSp n) {m : ℕ} (h : m < n) : (z.2 ⟨m, h⟩).1 = sp1 z m := by
  rw [sp1_of_lt h]
lemma sp2_mk {n : ℕ} (z : ChainSp n) {m : ℕ} (h : m < n) : (z.2 ⟨m, h⟩).2 = sp2 z m := by
  rw [sp2_of_lt h]
lemma sq1_fin {n : ℕ} (z : ChainSp n) (k : Fin (n + 1)) : (z.1 k).1 = sq1 z (k:ℕ) := by
  rw [sq1_of_le (show (k:ℕ) ≤ n by have := k.isLt; omega)]
lemma sq2_fin {n : ℕ} (z : ChainSp n) (k : Fin (n + 1)) : (z.1 k).2 = sq2 z (k:ℕ) := by
  rw [sq2_of_le (show (k:ℕ) ≤ n by have := k.isLt; omega)]
lemma sp1_fin {n : ℕ} (z : ChainSp n) (k : Fin n) : (z.2 k).1 = sp1 z (k:ℕ) := by
  rw [sp1_of_lt k.isLt]
lemma sp2_fin {n : ℕ} (z : ChainSp n) (k : Fin n) : (z.2 k).2 = sp2 z (k:ℕ) := by
  rw [sp2_of_lt k.isLt]
lemma sp1_pred {n : ℕ} (z : ChainSp n) (k : Fin (n + 1)) (hk : k ≠ 0) :
    (z.2 (k.pred hk)).1 = sp1 z ((k:ℕ) - 1) := by
  have hk1 : 1 ≤ (k:ℕ) := Nat.one_le_iff_ne_zero.mpr (fun hc => hk (Fin.ext (by rw [hc]; rfl)))
  have hlt : (k:ℕ) - 1 < n := by have := k.isLt; omega
  rw [sp1_of_lt hlt]; congr 1
lemma sp2_pred {n : ℕ} (z : ChainSp n) (k : Fin (n + 1)) (hk : k ≠ 0) :
    (z.2 (k.pred hk)).2 = sp2 z ((k:ℕ) - 1) := by
  have hk1 : 1 ≤ (k:ℕ) := Nat.one_le_iff_ne_zero.mpr (fun hc => hk (Fin.ext (by rw [hc]; rfl)))
  have hlt : (k:ℕ) - 1 < n := by have := k.isLt; omega
  rw [sp2_of_lt hlt]; congr 1

lemma if_pred_sp1 {n : ℕ} (z : ChainSp n) (k : Fin (n + 1)) :
    (if h : k = 0 then (0:ℝ) else (z.2 (k.pred h)).1) =
      (if h : (k:ℕ) = 0 then (0:ℝ) else sp1 z ((k:ℕ) - 1)) := by
  by_cases hk : k = 0
  · have hk' : (k:ℕ) = 0 := by rw [hk]; rfl
    rw [dite_eq_left hk, dite_eq_left hk']
  · have hk' : (k:ℕ) ≠ 0 := fun hc => hk (Fin.ext (by rw [hc]; rfl))
    rw [dite_eq_right hk, dite_eq_right hk', sp1_pred z k hk]
lemma if_pred_sp2 {n : ℕ} (z : ChainSp n) (k : Fin (n + 1)) :
    (if h : k = 0 then (0:ℝ) else (z.2 (k.pred h)).2) =
      (if h : (k:ℕ) = 0 then (0:ℝ) else sp2 z ((k:ℕ) - 1)) := by
  by_cases hk : k = 0
  · have hk' : (k:ℕ) = 0 := by rw [hk]; rfl
    rw [dite_eq_left hk, dite_eq_left hk']
  · have hk' : (k:ℕ) ≠ 0 := fun hc => hk (Fin.ext (by rw [hc]; rfl))
    rw [dite_eq_right hk, dite_eq_right hk', sp2_pred z k hk]
lemma if_lt_sp1 {n : ℕ} (z : ChainSp n) (k : Fin (n + 1)) :
    (if h : (k:ℕ) < n then (z.2 ⟨(k:ℕ), h⟩).1 else (0:ℝ)) =
      (if h : (k:ℕ) < n then sp1 z (k:ℕ) else (0:ℝ)) := by
  by_cases h : (k:ℕ) < n
  · rw [dite_eq_left h, dite_eq_left h, sp1_mk z h]
  · rw [dite_eq_right h, dite_eq_right h]
lemma if_lt_sp2 {n : ℕ} (z : ChainSp n) (k : Fin (n + 1)) :
    (if h : (k:ℕ) < n then (z.2 ⟨(k:ℕ), h⟩).2 else (0:ℝ)) =
      (if h : (k:ℕ) < n then sp2 z (k:ℕ) else (0:ℝ)) := by
  by_cases h : (k:ℕ) < n
  · rw [dite_eq_left h, dite_eq_left h, sp2_mk z h]
  · rw [dite_eq_right h, dite_eq_right h]
lemma if_lt_mid_sp1 {n N : ℕ} (z : ChainSp n) (k : Fin (n + 1)) :
    (if h : (k:ℕ) < n then (if midBlock N (k:ℕ) then (z.2 ⟨(k:ℕ), h⟩).1 else (0:ℝ)) else (0:ℝ)) =
      (if h : (k:ℕ) < n then (if midBlock N (k:ℕ) then sp1 z (k:ℕ) else (0:ℝ)) else (0:ℝ)) := by
  by_cases h : (k:ℕ) < n
  · rw [dite_eq_left h, dite_eq_left h, sp1_mk z h]
  · rw [dite_eq_right h, dite_eq_right h]
lemma if_lt_mid_sq1 {n N : ℕ} (z : ChainSp n) (k : Fin (n + 1)) :
    (if h : (k:ℕ) < n then (if midBlock N (k:ℕ) then (z.1 k).1 else (0:ℝ)) else (0:ℝ)) =
      (if h : (k:ℕ) < n then (if midBlock N (k:ℕ) then sq1 z (k:ℕ) else (0:ℝ)) else (0:ℝ)) := by
  by_cases h : (k:ℕ) < n
  · rw [dite_eq_left h, dite_eq_left h, sq1_fin z k]
  · rw [dite_eq_right h, dite_eq_right h]

/-- `sp1 z m = (1/cos δ) * sp1 z m - (1/cos δ - 1) * sp1 z m`-style rearrangement used below. -/
private lemma alg1 (a x : ℝ) : (a - 1) * x = a * x - x := by ring
private lemma alg2 (a x : ℝ) : x + (a - 1) * x = a * x := by ring

theorem refForm_kernel (n N : ℕ) (hN : 1 ≤ N) (hn : n = 3 * N - 1) (δ : ℝ)
    (hcos : Real.cos δ ≠ 0) (hsin : Real.sin ((N : ℝ) * δ) ≠ 0)
    (z : Work.RPCore.Chain.ChainSp n)
    (hz : ∀ z' : Work.RPCore.Chain.ChainSp n, Work.RPCore.Chain.BvForm n N δ z z' = 0) :
    ∃ c : ℝ, z = c • Work.RPCore.Chain.diagVec n := by
  have hNn : N < n := by omega
  -- ## the four families of scalar equations, read off from `hz`
  have hAgen : ∀ k : Fin (n+1),
      (if h : (k:ℕ) = 0 then (0:ℝ) else sp1 z ((k:ℕ) - 1))
        - (if h : (k:ℕ) < n then sp1 z (k:ℕ) else 0)
        - (1/Real.cos δ - 1) * (if h : (k:ℕ) < n then (if midBlock N (k:ℕ) then sp1 z (k:ℕ) else 0) else 0)
        + Real.tan δ * (if h : (k:ℕ) < n then (if midBlock N (k:ℕ) then sq1 z (k:ℕ) else 0) else 0)
      = 0 := by
    intro k
    have h := hz (Pi.single k ((1:ℝ),0), (0 : Fin n → ℝ×ℝ))
    rw [BvForm_deltaQ1] at h
    rwa [if_pred_sp1 z k, if_lt_sp1 z k, if_lt_mid_sp1 z k, if_lt_mid_sq1 z k] at h
  have hCgen : ∀ k : Fin (n+1),
      (if h : (k:ℕ) = 0 then (0:ℝ) else sp2 z ((k:ℕ) - 1))
        - (if h : (k:ℕ) < n then sp2 z (k:ℕ) else 0) = 0 := by
    intro k
    have h := hz (Pi.single k ((0:ℝ),1), (0 : Fin n → ℝ×ℝ))
    rw [BvForm_deltaQ2] at h
    rwa [if_pred_sp2 z k, if_lt_sp2 z k] at h
  have hBgen : ∀ k : Fin n,
      (sq1 z ((k:ℕ)+1) - sq1 z (k:ℕ))
        - (1/Real.cos δ - 1) * (if midBlock N (k:ℕ) then sq1 z (k:ℕ) else 0)
        + Real.tan δ * (if midBlock N (k:ℕ) then sp1 z (k:ℕ) else 0) = 0 := by
    intro k
    have h := hz ((0 : Fin (n+1) → ℝ×ℝ), Pi.single k ((1:ℝ),0))
    rw [BvForm_deltaP1] at h
    rw [sq1_fin z k.succ, sq1_fin z k.castSucc, sp1_fin z k] at h
    simp only [Fin.val_succ, Fin.val_castSucc] at h
    exact h
  have hDgen : ∀ k : Fin n, sq2 z ((k:ℕ)+1) = sq2 z (k:ℕ) := by
    intro k
    have h := hz ((0 : Fin (n+1) → ℝ×ℝ), Pi.single k ((0:ℝ),1))
    rw [BvForm_deltaP2] at h
    rw [sq2_fin z k.succ, sq2_fin z k.castSucc] at h
    simp only [Fin.val_succ, Fin.val_castSucc] at h
    linarith
  -- ## ℕ-indexed forms
  have hA : ∀ m, m ≤ n →
      (if h : m = 0 then (0:ℝ) else sp1 z (m - 1))
        - (if h : m < n then sp1 z m else 0)
        - (1/Real.cos δ - 1) * (if h : m < n then (if midBlock N m then sp1 z m else 0) else 0)
        + Real.tan δ * (if h : m < n then (if midBlock N m then sq1 z m else 0) else 0)
      = 0 := fun m hm => hAgen ⟨m, Nat.lt_succ_of_le hm⟩
  have hC : ∀ m, m ≤ n →
      (if h : m = 0 then (0:ℝ) else sp2 z (m - 1))
        - (if h : m < n then sp2 z m else 0) = 0 :=
    fun m hm => hCgen ⟨m, Nat.lt_succ_of_le hm⟩
  have hB : ∀ m, m < n →
      (sq1 z (m+1) - sq1 z m)
        - (1/Real.cos δ - 1) * (if midBlock N m then sq1 z m else 0)
        + Real.tan δ * (if midBlock N m then sp1 z m else 0) = 0 := fun m hm => hBgen ⟨m, hm⟩
  have hD : ∀ m, m < n → sq2 z (m+1) = sq2 z m := fun m hm => hDgen ⟨m, hm⟩
  -- ## the individual pieces
  have hC0 : sp2 z 0 = 0 := by
    have h := hC 0 (by omega)
    rw [dite_eq_left rfl, dite_eq_left (show (0:ℕ) < n by omega)] at h
    linarith
  have hCstep : ∀ m, 0 < m → m < n → sp2 z (m-1) = sp2 z m := by
    intro m h1 h2
    have h := hC m (by omega)
    rw [dite_eq_right (show ¬ (m = 0) by omega), dite_eq_left h2] at h
    linarith
  have hClast : sp2 z (n-1) = 0 := by
    have h := hC n le_rfl
    rw [dite_eq_right (show ¬ (n = 0) by omega),
      dite_eq_right (show ¬ (n < n) by omega)] at h
    linarith
  have hA0 : sp1 z 0 = 0 := by
    have h := hA 0 (by omega)
    have hmid0 : ¬ midBlock N 0 := by unfold midBlock; omega
    rw [dite_eq_left rfl, dite_eq_left (show (0:ℕ) < n by omega),
      dite_eq_left (show (0:ℕ) < n by omega), dite_eq_left (show (0:ℕ) < n by omega),
      ite_eq_right hmid0, ite_eq_right hmid0] at h
    simp only [mul_zero, sub_zero, add_zero, zero_sub] at h
    linarith
  have hAstep : ∀ m, 0 < m → m < n → ¬ midBlock N m → sp1 z (m-1) = sp1 z m := by
    intro m h1 h2 hmid
    have h := hA m (by omega)
    simp only [dite_eq_right (show ¬ (m = 0) by omega), dite_eq_left h2,
      ite_eq_right hmid, mul_zero, sub_zero, add_zero] at h
    linarith
  have hUmid : ∀ m, N ≤ m → m ≤ 2*N-1 →
      sp1 z m = Real.sin δ * sq1 z m + Real.cos δ * sp1 z (m-1) := by
    intro m h1 h2
    have hmn : m < n := by omega
    have hmid : midBlock N m := by unfold midBlock; omega
    have heq : sp1 z (m-1) = (1/Real.cos δ) * sp1 z m - Real.tan δ * sq1 z m := by
      have h := hA m (by omega)
      simp only [dite_eq_right (show ¬ (m = 0) by omega), dite_eq_left hmn,
        ite_eq_left hmid] at h
      rw [alg1 (1/Real.cos δ) (sp1 z m)] at h
      linarith
    have h2' : Real.cos δ * sp1 z (m-1) = sp1 z m - Real.sin δ * sq1 z m := by
      rw [heq, Real.tan_eq_sin_div_cos]
      field_simp
    linarith
  have hAlast : sp1 z (n-1) = 0 := by
    have h := hA n le_rfl
    rw [dite_eq_right (show ¬ (n = 0) by omega),
      dite_eq_right (show ¬ (n < n) by omega),
      dite_eq_right (show ¬ (n < n) by omega),
      dite_eq_right (show ¬ (n < n) by omega)] at h
    simp only [mul_zero, sub_zero, add_zero, zero_sub] at h
    linarith
  have hBstep : ∀ m, m < n → ¬ midBlock N m → sq1 z (m+1) = sq1 z m := by
    intro m hmn hmid
    have h := hB m hmn
    simp only [ite_eq_right hmid, mul_zero, add_zero, sub_zero] at h
    linarith
  have hBmid : ∀ m, N ≤ m → m ≤ 2*N-1 →
      sq1 z (m+1) = (1/Real.cos δ) * sq1 z m - Real.tan δ * sp1 z m := by
    intro m h1 h2
    have hmn : m < n := by omega
    have hmid : midBlock N m := by unfold midBlock; omega
    have h := hB m hmn
    simp only [ite_eq_left hmid] at h
    rw [alg1 (1/Real.cos δ) (sq1 z m)] at h
    linarith
  have hArot : ∀ m, N ≤ m → m ≤ 2*N-1 →
      sq1 z (m+1) = Real.cos δ * sq1 z m - Real.sin δ * sp1 z (m-1) := by
    intro m h1 h2
    have hb := hBmid m h1 h2
    have ha := hUmid m h1 h2
    rw [hb, ha, Real.tan_eq_sin_div_cos]
    field_simp
    linear_combination (-(sq1 z m)) * (Real.sin_sq_add_cos_sq δ)
  -- ## global facts
  have hbconst : ∀ m, m ≤ n → sq2 z m = sq2 z 0 :=
    fun m hm => seq_const_of_step (sq2 z) 0 (fun m _ hm => hD m hm) m (Nat.zero_le m) hm
  have hvzero : ∀ m, m < n → sp2 z m = 0 :=
    seq_zero_of_step (sp2 z) hC0 fun m => hCstep m
  have huleft : ∀ m, m < N → sp1 z m = 0 :=
    seq_zero_of_step (sp1 z) hA0 fun m h1 h2 =>
      hAstep m h1 (by omega) (by unfold midBlock; omega)
  have huright : ∀ m, 2*N-1 ≤ m → m < n → sp1 z m = 0 :=
    seq_zero_of_step_right (sp1 z) (2*N-1) (by omega)
      (fun m h1 h2 => hAstep m (by omega) h2 (by unfold midBlock; omega)) hAlast
  have haleft : ∀ m, m ≤ N → sq1 z m = sq1 z 0 :=
    fun m hm => seq_const_of_step (n := N) (sq1 z) 0
      (fun m _ hmN => hBstep m (by omega) (by unfold midBlock; omega)) m (Nat.zero_le m) hm
  have haright : ∀ m, 2*N ≤ m → m ≤ n → sq1 z m = sq1 z (2*N) :=
    seq_const_of_step (n := n) (sq1 z) (2*N)
      (fun m h1 hm => hBstep m hm (by unfold midBlock; omega))
  -- ## the middle block rotates by `δ`, `N` times
  have hrot := rotation_orbit N δ (sq1 z N) (sq1 z) (sp1 z)
    (fun k h1 h2 => ⟨hArot k h1 h2, hUmid k h1 h2⟩) rfl (huleft (N-1) (by omega))
  have hα0 : sq1 z N = 0 := by
    have hkey := hrot.2 N le_rfl
    rw [show N + N - 1 = 2*N-1 by omega] at hkey
    rw [huright (2*N-1) le_rfl (by omega)] at hkey
    rcases mul_eq_zero.mp hkey.symm with h | h
    · exact h
    · exact absurd h hsin
  have hsq1zero : ∀ m, m ≤ n → sq1 z m = 0 := by
    intro m hm
    rcases lt_or_ge N m with h | h
    · rcases lt_or_ge (2*N) m with h2 | h2
      · rw [haright m (by omega) hm, show 2*N = N + N by omega, hrot.1 N le_rfl, hα0]
        ring
      · rw [← show N + (m - N) = m by omega, hrot.1 (m - N) (by omega), hα0]
        ring
    · rw [haleft m h, ← haleft N le_rfl, hα0]
  have hsp1zero : ∀ m, m < n → sp1 z m = 0 := by
    intro m hm
    rcases lt_or_ge N m with h | h
    · rcases lt_or_ge (2*N-1) m with h2 | h2
      · exact huright m (by omega) hm
      · rw [← show N + (m - N + 1) - 1 = m by omega,
          hrot.2 (m - N + 1) (by omega), hα0]
        ring
    · rcases lt_or_eq_of_le h with hmN | hmN
      · exact huleft m hmN
      · rw [hmN, ← show N + 1 - 1 = N by omega, hrot.2 1 (by omega), hα0]
        ring
  -- ## conclusion
  refine ⟨sq2 z 0, ?_⟩
  have hz1 : z.1 = fun i => ((0:ℝ), sq2 z 0) := by
    funext i
    exact Prod.ext (by rw [sq1_fin z i]; exact hsq1zero (i:ℕ) (by have := i.isLt; omega))
      (by rw [sq2_fin z i]; exact hbconst (i:ℕ) (by have := i.isLt; omega))
  have hz2 : z.2 = fun _ => (0:ℝ×ℝ) := by
    funext j
    exact Prod.ext (by rw [sp1_fin z j]; exact hsp1zero (j:ℕ) j.isLt)
      (by rw [sp2_fin z j]; exact hvzero (j:ℕ) j.isLt)
  apply Prod.ext
  · rw [hz1]; funext i; simp [diagVec]
  · rw [hz2]; funext j; simp [diagVec]

end

end Work.RPCore.Chain
