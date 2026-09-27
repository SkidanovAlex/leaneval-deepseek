import Mathlib
import Submission.Work.KT.EG.kappa_linearise_defs
import Submission.Work.KT.EG.kappa_linearise_b
import Submission.Work.KT.Fund.kappa_homotopic

/-!
# `Work.KT.EG.kappa_linearise_c` — the companion matrix and its reduction

The column operations `A ↦ A * R` and the row operations `L * (A * R) = B` of Hatcher's
linearisation, together with the identification of the bottom-right block with `q(z)`.
-/

namespace Work.KT.EG

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X]

/-! ## 1. The coefficient matrix -/

@[simp] lemma coeffMatBig_inl {m : ℕ} (N : ℕ)
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) (a : Fin N × Fin m) (z : BIdx N m) :
    coeffMatBig X N q (Sum.inl a) z = 0 := rfl

@[simp] lemma coeffMatBig_inr_inl {m : ℕ} (N : ℕ)
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) (r : Fin m) (j : Fin N) (s : Fin m) :
    coeffMatBig X N q (Sum.inr r) (Sum.inl (j, s)) = (q r s).coeff (N - j.val) := rfl

@[simp] lemma coeffMatBig_inr_inr {m : ℕ} (N : ℕ)
    (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) (r s : Fin m) :
    coeffMatBig X N q (Sum.inr r) (Sum.inr s) = (q r s).coeff 0 := rfl

lemma coeffC_inl {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (a : Fin N × Fin m) (z : BIdx N m) : coeffC X N q (Sum.inl a) z = 0 := by
  show (coeffMatBig X N q (Sum.inl a) z).comp (ContinuousMap.fst : C(X × Sph ℂ, X)) = 0
  rw [coeffMatBig_inl]
  ext p
  rfl

lemma coeffC_inr_inl {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (r : Fin m) (j : Fin N) (s : Fin m) :
    coeffC X N q (Sum.inr r) (Sum.inl (j, s))
      = ((q r s).coeff (N - j.val)).comp (ContinuousMap.fst : C(X × Sph ℂ, X)) := by
  show (coeffMatBig X N q (Sum.inr r) (Sum.inl (j, s))).comp _ = _
  rw [coeffMatBig_inr_inl]

lemma coeffC_inr_inr {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (r s : Fin m) :
    coeffC X N q (Sum.inr r) (Sum.inr s)
      = ((q r s).coeff 0).comp (ContinuousMap.fst : C(X × Sph ℂ, X)) := by
  show (coeffMatBig X N q (Sum.inr r) (Sum.inr s)).comp _ = _
  rw [coeffMatBig_inr_inr]

lemma crMat_inl (m : ℕ) (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (a : Fin N × Fin m) (y : BIdx N m) :
    CRmat X N q (Sum.inl a) y = 0 := by
  have hdef : CRmat X N q = coeffC X N q * Rmat X N := rfl
  rw [hdef, Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun z _ => ?_)
  rw [coeffC_inl X N q, zero_mul]

/-! ## 2. `A * R` as a block matrix -/

lemma idMat_eq_fromBlocks (X : Type) [TopologicalSpace X] (N m : ℕ) :
    idMat C(X × Sph ℂ, ℂ) N m
      = (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ))
          0 0 0 : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) := by
  funext i j
  rcases i with a | r <;> rcases j with b | s
  · rw [Matrix.fromBlocks_apply₁₁, Matrix.one_apply, idMat_apply_eq, BIdx.st_inl, if_pos a.1.2]
    by_cases h : a = b
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (fun hh => h (Sum.inl.inj hh).symm), if_neg h]
  · rw [Matrix.fromBlocks_apply₁₂, idMat_apply_eq, BIdx.st_inl, if_pos a.1.2,
      if_neg (by simp)]
    simp
  · rw [Matrix.fromBlocks_apply₂₁, idMat_apply_eq, BIdx.st_inr, if_neg (by omega)]
    simp
  · rw [Matrix.fromBlocks_apply₂₂, idMat_apply_eq, BIdx.st_inr, if_neg (by omega)]
    simp

lemma crMat_eq_fromBlocks (m : ℕ) (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    CRmat X N q
      = (Matrix.fromBlocks 0 0 (RowM X N q) (Qm X N q) :
          Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) := by
  funext i j
  rcases i with a | r <;> rcases j with b | s
  · rw [Matrix.fromBlocks_apply₁₁, crMat_inl X m N q]
    simp
  · rw [Matrix.fromBlocks_apply₁₂, crMat_inl X m N q]
    simp
  · rfl
  · rfl

theorem Amat_mul_Rmat (m : ℕ) (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Amat X N q * Rmat X N
      = (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ)) 0
          (RowM X N q) (Qm X N q) : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) := by
  have hA : Amat X N q
      = idMat C(X × Sph ℂ, ℂ) N m - zc X • shC X N m + coeffC X N q := rfl
  rw [hA, add_mul, idMat_sub_zc_shC_mul_Rmat]
  change idMat C(X × Sph ℂ, ℂ) N m + CRmat X N q
    = (Matrix.fromBlocks 1 0 (RowM X N q) (Qm X N q) :
        Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))
  rw [crMat_eq_fromBlocks X m N q, idMat_eq_fromBlocks X N m, Matrix.fromBlocks_add]
  simp only [add_zero, zero_add]

/-! ## 3. The bottom-right block is `q(z)` -/

lemma shC_pow_inl_inr_one {m : ℕ} (N : ℕ) (k : ℕ) (j : Fin N) (s : Fin m)
    (hj : j.val + k = N) : ((shC X N m) ^ k) (Sum.inl (j, s)) (Sum.inr s) = 1 := by
  rw [shC_pow_apply, BIdx.st_inl, if_pos (by omega : j.val + k ≤ N)]
  rw [show k = N - j.val from by omega]
  rw [BIdx.nx_iterate_inr_eval (by omega : j.val < N) s, if_pos rfl]

lemma shC_pow_inl_inr_zero {m : ℕ} (N : ℕ) (k : ℕ) (j : Fin N) (t s : Fin m)
    (h : j.val + k ≠ N ∨ t ≠ s) : ((shC X N m) ^ k) (Sum.inl (j, t)) (Sum.inr s) = 0 := by
  rw [shC_pow_apply, BIdx.st_inl]
  by_cases hjk : j.val + k ≤ N
  · rw [if_pos hjk]
    by_cases hlt : j.val + k < N
    · rw [BIdx.nx_iterate_inl_eval (i := j) k hlt t, if_neg (by simp)]
    · have heq : j.val + k = N := by omega
      rcases h with hne | hts
      · exact absurd heq hne
      · rw [show k = N - j.val from by omega,
          BIdx.nx_iterate_inr_eval (by omega : j.val < N) t]
        exact if_neg (fun hh => hts (Sum.inr.inj hh.symm))
  · rw [if_neg hjk]

lemma shC_pow_inr_inr_zero {m : ℕ} (N : ℕ) (k : ℕ) (t s : Fin m) (hk : k ≠ 0) :
    ((shC X N m) ^ k) (Sum.inr t) (Sum.inr s) = 0 := by
  rw [shC_pow_apply, BIdx.st_inr, if_neg (by omega : ¬ (N + k ≤ N))]

theorem coeffC_mul_shC_pow_inr (m : ℕ) (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (k : ℕ) (hk : k ≤ N) (r s : Fin m) :
    (coeffC X N q * (shC X N m) ^ k) (Sum.inr r) (Sum.inr s)
      = pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X)) ((q r s).coeff k) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [pow_zero, Matrix.mul_one, coeffC_inr_inr X N q, Work.KT.Fund.pullAlg_apply']
  · rw [Matrix.mul_apply, Fintype.sum_sum_type]
    have h2 : (∑ t : Fin m, coeffC X N q (Sum.inr r) (Sum.inr t)
        * ((shC X N m) ^ k) (Sum.inr t) (Sum.inr s)) = 0 := by
      refine Finset.sum_eq_zero (fun t _ => ?_)
      rw [shC_pow_inr_inr_zero X N k t s (by omega), mul_zero]
    rw [h2, add_zero]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ j : Fin N,
        (∑ t : Fin m, coeffC X N q (Sum.inr r) (Sum.inl (j, t))
          * ((shC X N m) ^ k) (Sum.inl (j, t)) (Sum.inr s))
          = if j.val + k = N then
              pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X)) ((q r s).coeff (N - j.val))
            else 0 := by
      intro j
      by_cases hj : j.val + k = N
      · have hval : ∀ t : Fin m, coeffC X N q (Sum.inr r) (Sum.inl (j, t))
            * ((shC X N m) ^ k) (Sum.inl (j, t)) (Sum.inr s)
            = if t = s then
                pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X)) ((q r s).coeff (N - j.val))
              else 0 := by
          intro t
          by_cases ht : t = s
          · rw [if_pos ht, ht, shC_pow_inl_inr_one X N k j s hj, mul_one, coeffC_inr_inl X N q,
              Work.KT.Fund.pullAlg_apply']
          · rw [shC_pow_inl_inr_zero X N k j t s (Or.inr ht), mul_zero, if_neg ht]
        rw [Finset.sum_congr rfl (fun t _ => hval t), Finset.sum_ite_eq']
        rw [if_pos (Finset.mem_univ s), if_pos hj]
      · rw [if_neg hj]
        refine Finset.sum_eq_zero (fun t _ => ?_)
        rw [shC_pow_inl_inr_zero X N k j t s (Or.inl hj), mul_zero]
    rw [Finset.sum_congr rfl (fun j _ => hinner j)]
    have hj : (N - k) < N := by omega
    rw [Finset.sum_eq_single (⟨N - k, hj⟩ : Fin N)]
    · have hidx : N - (⟨N - k, hj⟩ : Fin N).val = k := by simp only [Fin.val_mk]; omega
      rw [if_pos (by simp only [Fin.val_mk]; omega), hidx]
    · intro j _ hjne
      exact if_neg (fun hh => hjne (Fin.ext (by simp only [Fin.val_mk]; omega)))
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem

theorem Qm_eq (m : ℕ) (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (hN : ∀ i j, (q i j).natDegree ≤ N) :
    Qm X N q = q.map (polyMapA X) := by
  funext r s
  have hCR : CRmat X N q
      = ∑ k ∈ Finset.range (N + 1), (zc X) ^ k • (coeffC X N q * (shC X N m) ^ k) := by
    have hdef : CRmat X N q = coeffC X N q * Rmat X N := rfl
    rw [hdef, show Rmat X N = ∑ k ∈ Finset.range (N + 1), (zc X) ^ k • (shC X N m) ^ k from rfl]
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact Matrix.mul_smul (coeffC X N q) (zc X ^ k) ((shC X N m) ^ k)
  rw [show Qm X N q r s = CRmat X N q (Sum.inr r) (Sum.inr s) from rfl, hCR, Matrix.sum_apply]
  have hterm : ∀ k ∈ Finset.range (N + 1),
      ((zc X) ^ k • (coeffC X N q * (shC X N m) ^ k)) (Sum.inr r) (Sum.inr s)
        = pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X)) ((q r s).coeff k) * (zc X) ^ k := by
    intro k hk
    rw [show ((zc X) ^ k • (coeffC X N q * (shC X N m) ^ k)) (Sum.inr r) (Sum.inr s)
        = (zc X) ^ k * ((coeffC X N q * (shC X N m) ^ k) (Sum.inr r) (Sum.inr s)) from rfl]
    rw [coeffC_mul_shC_pow_inr X m N q k (by have := Finset.mem_range.mp hk; omega) r s]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hpoly := poly_eval_sum (polyMapA X)
    ((pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom)
    (zc X) (fun a => polyMapA_C X a) (polyMapA_X X) (q r s) N (hN r s)
  rw [show q.map (polyMapA X) r s = polyMapA X (q r s) from rfl, hpoly]
  exact Finset.sum_congr rfl (fun k _ => rfl)

theorem Lmat_mul_Amat_Rmat (m : ℕ) (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (hN : ∀ i j, (q i j).natDegree ≤ N) :
    Lmat X N q * (Amat X N q * Rmat X N) = Bmat X N q := by
  rw [Amat_mul_Rmat X m N q, Qm_eq X m N q hN]
  have hL : Lmat X N q
      = (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ)) 0
          (-(RowM X N q)) (1 : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) :
          Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) := rfl
  rw [hL, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.neg_mul, neg_add_cancel, neg_zero]

end

end Work.KT.EG
