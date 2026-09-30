import Mathlib
import Submission.Work.SSSR.Serre.simpHomChain
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Serre
variable {R : Type} [CommRing R] [Nontrivial R]

set_option maxHeartbeats 2000000

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial
namespace Work.SSSR.Serre

noncomputable section

variable {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}

/-- The index type of the terms of the prism identity: the pairs `(k,f)` of the sum `∂T`, the
pairs `(x,y)` of the sum `T∂`, and the two "boundary" terms. -/
abbrev PIdx (m : ℕ) : Type := (Fin (m+2) × Fin (m+3)) ⊕ (Fin (m+2) × Fin (m+1)) ⊕ Unit ⊕ Unit

/-- The value of a term of the prism identity. -/
def pval (R : Type) [CommRing R] [Nontrivial R] (H : SimpHom X A N) {m : ℕ} (s : SSetSimplex X (m+1)) :
    PIdx m → (SSetSimplex X (m+1) →₀ R) := fun z =>
  match z with
  | Sum.inl (k, f) =>
      ((-1:ℤ)^((k:ℕ)+1+(f:ℕ))) • Finsupp.single ((singX X).δ f (hSimplex H (m+1) k s)) (1 : R)
  | Sum.inr (Sum.inl (x, y)) =>
      ((-1:ℤ)^((x:ℕ)+((y:ℕ)+1))) • Finsupp.single (hSimplex H m y ((singX X).δ x s)) (1 : R)
  | Sum.inr (Sum.inr (Sum.inl _)) => - Finsupp.single s (1 : R)
  | Sum.inr (Sum.inr (Sum.inr _)) => Finsupp.single (gSimplex H (m+1) s) (1 : R)

/-- The sign reversing involution pairing the terms of the prism identity. -/
def pinv (R : Type) [CommRing R] [Nontrivial R] {m : ℕ} : PIdx m → PIdx m := fun z =>
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

theorem pval_ne_zero (R : Type) [CommRing R] [Nontrivial R] (H : SimpHom X A N) {m : ℕ} (s : SSetSimplex X (m+1)) (z : PIdx m) :
    pval R H s z ≠ 0 := by
  match z with
  | Sum.inl (k, f) =>
      intro h
      have h1 := congrArg (fun (w : SSetSimplex X (m+1) →₀ R) =>
        w ((singX X).δ f (hSimplex H (m+1) k s))) h
      simp only [pval, Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.zero_apply,
        zsmul_eq_mul, smul_eq_mul, mul_one] at h1
      have hne : ((-1:R)^((k:ℕ)+1+(f:ℕ))) ≠ 0 := by
        rcases Nat.even_or_odd ((k:ℕ)+1+(f:ℕ)) with hh | hh
        · rw [hh.neg_one_pow]; exact one_ne_zero
        · rw [hh.neg_one_pow]; exact neg_ne_zero.mpr one_ne_zero
      exact hne (by simpa [Int.cast_pow] using h1)
  | Sum.inr (Sum.inl (x, y)) =>
      intro h
      have h1 := congrArg (fun (w : SSetSimplex X (m+1) →₀ R) =>
        w (hSimplex H m y ((singX X).δ x s))) h
      simp only [pval, Finsupp.smul_apply, Finsupp.single_eq_same, Finsupp.zero_apply,
        zsmul_eq_mul, smul_eq_mul, mul_one] at h1
      have hne : ((-1:R)^((x:ℕ)+((y:ℕ)+1))) ≠ 0 := by
        rcases Nat.even_or_odd ((x:ℕ)+((y:ℕ)+1)) with hh | hh
        · rw [hh.neg_one_pow]; exact one_ne_zero
        · rw [hh.neg_one_pow]; exact neg_ne_zero.mpr one_ne_zero
      exact hne (by simpa [Int.cast_pow] using h1)
  | Sum.inr (Sum.inr (Sum.inl u)) =>
      intro h
      have h1 := congrArg (fun (w : SSetSimplex X (m+1) →₀ R) => w s) h
      simp only [pval, Finsupp.neg_apply, Finsupp.single_eq_same, Finsupp.zero_apply] at h1
      exact one_ne_zero (neg_eq_zero.mp h1)
  | Sum.inr (Sum.inr (Sum.inr u)) =>
      intro h
      have h1 := congrArg (fun (w : SSetSimplex X (m+1) →₀ R) => w (gSimplex H (m+1) s)) h
      simp only [pval, Finsupp.single_eq_same, Finsupp.zero_apply] at h1
      exact one_ne_zero h1

theorem pinv_pinv (R : Type) [CommRing R] [Nontrivial R] {m : ℕ} (z : PIdx m) : pinv R (pinv R z) = z := by
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

theorem pval_pinv (R : Type) [CommRing R] [Nontrivial R] (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N) (s : SSetSimplex X (m+1))
    (z : PIdx m) : pval R H s (pinv R z) = - pval R H s z := by
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

theorem pinv_ne_self (R : Type) [CommRing R] [Nontrivial R] (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N) (s : SSetSimplex X (m+1))
    (z : PIdx m) : pinv R z ≠ z := by
  match z with
  | Sum.inl (k, f) =>
      simp only [pinv]
      split_ifs
      all_goals
        (rintro h
         first
         | exact Sum.inr_ne_inl h
         | (simp only [Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff] at h
            omega))
  | Sum.inr (Sum.inl (x, y)) =>
      simp only [pinv]
      split_ifs
      all_goals
        (rintro h
         first
         | exact Sum.inl_ne_inr h
         | (simp only [Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff] at h
            omega))
  | Sum.inr (Sum.inr (Sum.inl u)) =>
      cases u
      simp only [pinv]
      rintro h
      exact Sum.inl_ne_inr h
  | Sum.inr (Sum.inr (Sum.inr u)) =>
      cases u
      simp only [pinv]
      rintro h
      exact Sum.inl_ne_inr h

theorem prismSumIdentity (H : SimpHom X A N) (m : ℕ) (hm : m + 1 ≤ N)
    (s : SSetSimplex X (m + 1)) :
    (∑ x : Fin (m + 2), ∑ y : Fin (m + 3),
        ((-1 : ℤ) ^ ((x : ℕ) + 1 + (y : ℕ))) •
          Finsupp.single ((singX X).δ y (hSimplex H (m + 1) x s)) (1 : R))
      + (∑ x : Fin (m + 2), ∑ y : Fin (m + 1),
          ((-1 : ℤ) ^ ((x : ℕ) + ((y : ℕ) + 1))) •
            Finsupp.single (hSimplex H m y ((singX X).δ x s)) (1 : R))
      = Finsupp.single s (1 : R) - Finsupp.single (gSimplex H (m + 1) s) (1 : R) := by
  have hsum : ∑ z : PIdx m, pval R H s z = 0 := by
    have h := Finset.sum_ninvolution (s := (Finset.univ : Finset (PIdx m))) (f := pval R H s)
      (pinv R (m := m))
      (fun a => by rw [pval_pinv R H hm s a]; abel) (fun a _ => pinv_ne_self R H hm s a)
      (fun a => Finset.mem_univ (pinv R a)) (fun a => pinv_pinv R a)
    simpa using h
  have hsplit : ∑ z : PIdx m, pval R H s z
      = (∑ x : Fin (m + 2), ∑ y : Fin (m + 3),
            ((-1 : ℤ) ^ ((x : ℕ) + 1 + (y : ℕ))) •
              Finsupp.single ((singX X).δ y (hSimplex H (m + 1) x s)) (1 : R))
        + ((∑ x : Fin (m + 2), ∑ y : Fin (m + 1),
              ((-1 : ℤ) ^ ((x : ℕ) + ((y : ℕ) + 1))) •
                Finsupp.single (hSimplex H m y ((singX X).δ x s)) (1 : R))
          + (- Finsupp.single s (1 : R) + Finsupp.single (gSimplex H (m + 1) s) (1 : R))) := by
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, pval, Finset.univ_unique,
      Finset.sum_singleton]
  rw [hsplit] at hsum
  have hsum' : ((∑ x : Fin (m + 2), ∑ y : Fin (m + 3),
            ((-1 : ℤ) ^ ((x : ℕ) + 1 + (y : ℕ))) •
              Finsupp.single ((singX X).δ y (hSimplex H (m + 1) x s)) (1 : R))
        + (∑ x : Fin (m + 2), ∑ y : Fin (m + 1),
              ((-1 : ℤ) ^ ((x : ℕ) + ((y : ℕ) + 1))) •
                Finsupp.single (hSimplex H m y ((singX X).δ x s)) (1 : R)))
        + (- Finsupp.single s (1 : R) + Finsupp.single (gSimplex H (m + 1) s) (1 : R)) = 0 := by
    rw [← hsum]; abel
  have h2 := add_eq_zero_iff_eq_neg.mp hsum'
  rw [neg_add_rev, neg_neg] at h2
  rw [sub_eq_add_neg]
  exact h2.trans (add_comm _ _)

end

end Work.SSSR.Serre
