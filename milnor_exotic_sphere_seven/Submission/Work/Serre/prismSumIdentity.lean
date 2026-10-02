import Mathlib
import Submission.Work.Serre.simpHomChain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 2000000

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial

namespace Work.Serre

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}

/-- The index type of the terms of the prism identity: the pairs `(k,f)` of the sum `∂T`, the
pairs `(x,y)` of the sum `T∂`, and the two "boundary" terms. -/
abbrev PIdx (m : ℕ) : Type := (Fin (m+2) × Fin (m+3)) ⊕ (Fin (m+2) × Fin (m+1)) ⊕ Unit ⊕ Unit

/-- The value of a term of the prism identity. -/
def pval (H : SimpHom X A N) {m : ℕ} (s : SSetSimplex X (m+1)) :
    PIdx m → (SSetSimplex X (m+1) →₀ ℤ) := fun z =>
  match z with
  | Sum.inl (k, f) =>
      ((-1:ℤ)^((k:ℕ)+1+(f:ℕ))) • Finsupp.single ((singX X).δ f (hSimplex H (m+1) k s)) (1:ℤ)
  | Sum.inr (Sum.inl (x, y)) =>
      ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (hSimplex H m y ((singX X).δ x s)) (1:ℤ)
  | Sum.inr (Sum.inr (Sum.inl _)) => - Finsupp.single s (1:ℤ)
  | Sum.inr (Sum.inr (Sum.inr _)) => Finsupp.single (gSimplex H (m+1) s) (1:ℤ)

/-- The sign reversing involution pairing the terms of the prism identity. -/
def pinv {m : ℕ} : PIdx m → PIdx m := fun z =>
  match z with
  | Sum.inl (k, f) =>
      if hfk : (f:ℕ) < (k:ℕ) then
        Sum.inr (Sum.inl (⟨(f:ℕ), by have hf := f.isLt; have hk := k.isLt; omega⟩,
          ⟨(k:ℕ)-1, by have hk := k.isLt; omega⟩))
      else if hfe : (f:ℕ) = (k:ℕ) then
        (if hk0 : (k:ℕ) = 0 then Sum.inr (Sum.inr (Sum.inr ()))
          else Sum.inl (⟨(k:ℕ)-1, by have hk := k.isLt; omega⟩, f))
      else if hfe1 : (f:ℕ) = (k:ℕ)+1 then
        (if hkm : (k:ℕ) = m+1 then Sum.inr (Sum.inr (Sum.inl ()))
          else Sum.inl (⟨(k:ℕ)+1, by have hk := k.isLt; omega⟩, f))
      else Sum.inr (Sum.inl (⟨(f:ℕ)-1, by have hf := f.isLt; omega⟩,
        ⟨(k:ℕ), by have hk := k.isLt; omega⟩))
  | Sum.inr (Sum.inl (x, y)) =>
      if hxy : (x:ℕ) ≤ (y:ℕ) then
        Sum.inl (⟨(y:ℕ)+1, by have hy := y.isLt; omega⟩, ⟨(x:ℕ), by have hx := x.isLt; omega⟩)
      else Sum.inl (⟨(y:ℕ), by have hy := y.isLt; omega⟩,
        ⟨(x:ℕ)+1, by have hx := x.isLt; omega⟩)
  | Sum.inr (Sum.inr (Sum.inl _)) => Sum.inl (Fin.last (m+1), Fin.last (m+2))
  | Sum.inr (Sum.inr (Sum.inr _)) => Sum.inl (0, 0)

theorem pval_ne_zero (H : SimpHom X A N) {m : ℕ} (s : SSetSimplex X (m+1)) (z : PIdx m) :
    pval H s z ≠ 0 := by
  match z with
  | Sum.inl (k, f) =>
      intro h
      have h1 := congrArg (fun (w : SSetSimplex X (m+1) →₀ ℤ) =>
        w ((singX X).δ f (hSimplex H (m+1) k s))) h
      simp only [pval, Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.zero_apply,
        smul_eq_mul, mul_one] at h1
      exact pow_ne_zero _ (by norm_num : (-1:ℤ) ≠ 0) h1
  | Sum.inr (Sum.inl (x, y)) =>
      intro h
      have h1 := congrArg (fun (w : SSetSimplex X (m+1) →₀ ℤ) =>
        w (hSimplex H m y ((singX X).δ x s))) h
      simp only [pval, Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.zero_apply,
        smul_eq_mul, mul_one] at h1
      exact pow_ne_zero _ (by norm_num : (-1:ℤ) ≠ 0) h1
  | Sum.inr (Sum.inr (Sum.inl u)) =>
      intro h
      have h1 := congrArg (fun (w : SSetSimplex X (m+1) →₀ ℤ) => w s) h
      simp only [pval, Finsupp.neg_apply, Finsupp.single_eq_same, Finsupp.zero_apply] at h1
      exact one_ne_zero (neg_eq_zero.mp h1)
  | Sum.inr (Sum.inr (Sum.inr u)) =>
      intro h
      have h1 := congrArg (fun (w : SSetSimplex X (m+1) →₀ ℤ) => w (gSimplex H (m+1) s)) h
      simp only [pval, Finsupp.single_eq_same, Finsupp.zero_apply] at h1
      exact one_ne_zero h1

theorem pinv_pinv {m : ℕ} (z : PIdx m) : pinv (pinv z) = z := by
  match z with
  | Sum.inl (k, f) =>
      simp only [pinv]
      split_ifs
      all_goals (try (simp only [pinv]))
      all_goals (try split_ifs)
      all_goals (first
        | rfl
        | (simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero,
            Fin.val_last, and_true, true_and]
           omega)
        | (exfalso; omega))
  | Sum.inr (Sum.inl (x, y)) =>
      simp only [pinv]
      split_ifs
      all_goals (try (simp only [pinv]))
      all_goals (try split_ifs)
      all_goals (first
        | rfl
        | (simp only [Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero,
            Fin.val_last, and_true, true_and]
           omega)
        | (exfalso; omega))
  | Sum.inr (Sum.inr (Sum.inl u)) =>
      cases u
      simp only [pinv, Fin.val_last]
      split_ifs <;> (first | rfl | (exfalso; omega))
  | Sum.inr (Sum.inr (Sum.inr u)) =>
      cases u
      simp only [pinv, Fin.val_zero]
      split_ifs <;> (first | rfl | (exfalso; omega))

theorem pval_pinv (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N) (s : SSetSimplex X (m+1))
    (z : PIdx m) : pval H s (pinv z) = - pval H s z := by
  match z with
  | Sum.inl (k, f) =>
      simp only [pinv]
      by_cases h1 : (f:ℕ) < (k:ℕ)
      · rw [dif_pos h1]
        simp only [pval]
        rw [δ_hSimplex_lt H hm s f k h1, ← neg_smul]
        congr 1
        rw [show (↑k + 1 + ↑f : ℕ) = (↑f + (↑k - 1 + 1)) + 1 by omega, pow_succ]
        ring
      · rw [dif_neg h1]
        by_cases h2 : (f:ℕ) = (k:ℕ)
        · rw [dif_pos h2]
          by_cases h3 : (k:ℕ) = 0
          · rw [dif_pos h3]
            simp only [pval]
            rw [show (↑k + 1 + ↑f : ℕ) = 1 by omega, pow_one]
            rw [show (f : Fin (m+3)) = 0 from Fin.ext (by simp only [Fin.val_zero]; omega),
              show (k : Fin (m+2)) = 0 from Fin.ext (by simp only [Fin.val_zero]; omega),
              δ_hSimplex_zero H (m+1) hm s]
            rw [neg_one_smul, neg_neg]
          · rw [dif_neg h3]
            simp only [pval]
            have hfac : (singX X).δ f
                  (hSimplex H (m+1) (⟨(k:ℕ)-1, by have hk := k.isLt; omega⟩ : Fin (m+2)) s)
                = (singX X).δ f (hSimplex H (m+1) k s) := by
              let j : Fin (m+1) := ⟨(k:ℕ)-1, by have hk := k.isLt; omega⟩
              have hjv : (j:ℕ) = (k:ℕ)-1 := rfl
              have hjc : j.castSucc
                  = (⟨(k:ℕ)-1, by have hk := k.isLt; omega⟩ : Fin (m+2)) := rfl
              rw [← hjc]
              rw [show f = j.castSucc.succ from
                Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
              rw [show k = j.succ from Fin.ext (by simp only [Fin.val_succ]; omega)]
              exact δ_hSimplex_diag H hm s j
            rw [hfac, ← neg_smul]
            congr 1
            rw [show (↑k + 1 + ↑f : ℕ) = (↑k - 1 + 1 + ↑f) + 1 by omega, pow_succ]
            ring
        · rw [dif_neg h2]
          by_cases h4 : (f:ℕ) = (k:ℕ)+1
          · rw [dif_pos h4]
            by_cases h5 : (k:ℕ) = m+1
            · rw [dif_pos h5]
              simp only [pval]
              rw [show (↑k + 1 + ↑f : ℕ) = 2 * (m + 2) by omega]
              rw [pow_mul, show ((-1:ℤ)^2) = 1 by norm_num, one_pow, one_smul]
              rw [show (f : Fin (m+3)) = Fin.last (m+2) from
                  Fin.ext (by simp only [Fin.val_last]; omega),
                show (k : Fin (m+2)) = Fin.last (m+1) from
                  Fin.ext (by simp only [Fin.val_last]; omega),
                δ_hSimplex_last H (m+1) hm s]
            · rw [dif_neg h5]
              simp only [pval]
              have hfac : (singX X).δ f
                    (hSimplex H (m+1) (⟨(k:ℕ)+1, by have hk := k.isLt; omega⟩ : Fin (m+2)) s)
                  = (singX X).δ f (hSimplex H (m+1) k s) := by
                let j : Fin (m+1) := ⟨(k:ℕ), by have hk := k.isLt; omega⟩
                have hjv : (j:ℕ) = (k:ℕ) := rfl
                have hjs : j.succ
                    = (⟨(k:ℕ)+1, by have hk := k.isLt; omega⟩ : Fin (m+2)) := rfl
                rw [← hjs]
                rw [show f = j.castSucc.succ from
                  Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
                rw [show k = j.castSucc from Fin.ext (by simp only [Fin.val_castSucc]; omega)]
                exact (δ_hSimplex_diag H hm s j).symm
              rw [hfac, ← neg_smul]
              congr 1
              rw [show (↑k + 1 + 1 + ↑f : ℕ) = (↑k + 1 + ↑f) + 1 by omega, pow_succ]
              ring
          · rw [dif_neg h4]
            simp only [pval]
            rw [δ_hSimplex_gt H hm s f k (by omega), ← neg_smul]
            congr 1
            rw [show (↑k + 1 + ↑f : ℕ) = (↑f - 1 + (↑k + 1)) + 1 by omega, pow_succ]
            ring
  | Sum.inr (Sum.inl (x, y)) =>
      simp only [pinv]
      by_cases h1 : (x:ℕ) ≤ (y:ℕ)
      · rw [dif_pos h1]
        simp only [pval]
        rw [δ_hSimplex_lt H hm s (⟨(x:ℕ), by have hx := x.isLt; omega⟩ : Fin (m+3))
          (⟨(y:ℕ)+1, by have hy := y.isLt; omega⟩ : Fin (m+2))
          (by simp only [Fin.val_mk]; omega), ← neg_smul]
        congr 1
        rw [show (↑y + 1 + 1 + ↑x : ℕ) = (↑x + (↑y + 1)) + 1 by omega, pow_succ]
        ring
      · rw [dif_neg h1]
        simp only [pval]
        rw [δ_hSimplex_gt H hm s (⟨(x:ℕ)+1, by have hx := x.isLt; omega⟩ : Fin (m+3))
          (⟨(y:ℕ), by have hy := y.isLt; omega⟩ : Fin (m+2))
          (by simp only [Fin.val_mk]; omega), ← neg_smul]
        congr 1
        rw [show (↑y + 1 + (↑x + 1) : ℕ) = (↑x + (↑y + 1)) + 1 by omega, pow_succ]
        ring
  | Sum.inr (Sum.inr (Sum.inl u)) =>
      cases u
      simp only [pinv, pval]
      rw [show (↑(Fin.last (m+1)) + 1 + ↑(Fin.last (m+2)) : ℕ) = 2 * (m + 2) by
        simp only [Fin.val_last]; omega]
      rw [pow_mul, show ((-1:ℤ)^2) = 1 by norm_num, one_pow, one_smul]
      simp only [δ_hSimplex_last H (m+1) hm s, neg_neg]
  | Sum.inr (Sum.inr (Sum.inr u)) =>
      cases u
      simp only [pinv, pval]
      rw [δ_hSimplex_zero H (m+1) hm s]
      norm_num

theorem pinv_ne_self (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N) (s : SSetSimplex X (m+1))
    (z : PIdx m) : pinv z ≠ z := by
  intro h
  have hpinv : pval H s (pinv z) = pval H s z := by rw [h]
  rw [pval_pinv H hm s z] at hpinv
  have h1 : pval H s z + pval H s z = 0 := neg_eq_iff_add_eq_zero.mp hpinv
  have h2 : (2:ℤ) • pval H s z = 0 := by rw [two_smul ℤ (pval H s z)]; exact h1
  exact pval_ne_zero H s z ((smul_eq_zero.mp h2).resolve_left (by norm_num))

theorem prismSumIdentity (H : SimpHom X A N) (m : ℕ) (hm : m + 1 ≤ N)
    (s : SSetSimplex X (m + 1)) :
    (∑ x : Fin (m + 2), ∑ y : Fin (m + 3),
        ((-1 : ℤ) ^ ((x : ℕ) + 1 + (y : ℕ))) •
          Finsupp.single ((singX X).δ y (hSimplex H (m + 1) x s)) (1 : ℤ))
      + (∑ x : Fin (m + 2), ∑ y : Fin (m + 1),
          ((-1 : ℤ) ^ ((x : ℕ) + ((y : ℕ) + 1))) •
            Finsupp.single (hSimplex H m y ((singX X).δ x s)) (1 : ℤ))
      = Finsupp.single s (1 : ℤ) - Finsupp.single (gSimplex H (m + 1) s) (1 : ℤ) := by
  have hsum : ∑ z : PIdx m, pval H s z = 0 := by
    have h := Finset.sum_ninvolution (s := (Finset.univ : Finset (PIdx m))) (f := pval H s)
      (pinv (m := m))
      (fun a => by rw [pval_pinv H hm s a]; abel) (fun a _ => pinv_ne_self H hm s a)
      (fun a => Finset.mem_univ (pinv a)) (fun a => pinv_pinv a)
    simpa using h
  have hsplit : ∑ z : PIdx m, pval H s z
      = (∑ x : Fin (m + 2), ∑ y : Fin (m + 3),
            ((-1 : ℤ) ^ ((x : ℕ) + 1 + (y : ℕ))) •
              Finsupp.single ((singX X).δ y (hSimplex H (m + 1) x s)) (1 : ℤ))
        + ((∑ x : Fin (m + 2), ∑ y : Fin (m + 1),
              ((-1 : ℤ) ^ ((x : ℕ) + ((y : ℕ) + 1))) •
                Finsupp.single (hSimplex H m y ((singX X).δ x s)) (1 : ℤ))
          + (- Finsupp.single s (1 : ℤ) + Finsupp.single (gSimplex H (m + 1) s) (1 : ℤ))) := by
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, pval, Finset.univ_unique,
      Finset.sum_singleton]
  rw [hsplit] at hsum
  have hsum' : ((∑ x : Fin (m + 2), ∑ y : Fin (m + 3),
            ((-1 : ℤ) ^ ((x : ℕ) + 1 + (y : ℕ))) •
              Finsupp.single ((singX X).δ y (hSimplex H (m + 1) x s)) (1 : ℤ))
        + (∑ x : Fin (m + 2), ∑ y : Fin (m + 1),
              ((-1 : ℤ) ^ ((x : ℕ) + ((y : ℕ) + 1))) •
                Finsupp.single (hSimplex H m y ((singX X).δ x s)) (1 : ℤ)))
        + (- Finsupp.single s (1 : ℤ) + Finsupp.single (gSimplex H (m + 1) s) (1 : ℤ)) = 0 := by
    rw [← hsum]; abel
  have h2 := add_eq_zero_iff_eq_neg.mp hsum'
  rw [neg_add_rev, neg_neg] at h2
  rw [sub_eq_add_neg]
  exact h2.trans (add_comm _ _)

end

end Work.Serre
