import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.aDiag_conj_uij

namespace Work.EKLComp

open Work.EKLContract

/-! ## Elementary matrix-vector identities for diagonal `×` transvection matrices -/

/-- `(diagonal D) *ᵥ v = D ⊙ v`. -/
private lemma mulVec_diagonal (D v : Fin 3 → ℝ) :
    Matrix.mulVec (Matrix.diagonal D) v = fun c => D c * v c := by
  funext c
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  -- `∑ x, (if c = x then D c else 0) * v x = D c * v c`
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- `(single i j s) *ᵥ v` adds `s * v j` to the `i`-th coordinate. -/
private lemma mulVec_single (i j : Fin 3) (s : ℝ) (v : Fin 3 → ℝ) :
    Matrix.mulVec (Matrix.single i j s) v = fun c => if c = i then s * v j else 0 := by
  funext c
  by_cases hc : c = i
  · subst hc
    simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, true_and, if_true]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg hc]
    simp only [Matrix.mulVec, dotProduct, Matrix.single_apply]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (fun h => hc h.1.symm), zero_mul]

/-- `(diagonal D * (1 + single i j s)) *ᵥ v` scales `v + s v_j e_i` by `D`. -/
private lemma mulVec_diag_single (D : Fin 3 → ℝ) (i j : Fin 3) (s : ℝ) (v : Fin 3 → ℝ) :
    Matrix.mulVec (Matrix.diagonal D * (1 + Matrix.single i j s)) v
      = fun c => D c * (v c + if c = i then s * v j else 0) := by
  have hN : Matrix.mulVec (1 + Matrix.single i j s) v
      = v + (fun c => if c = i then s * v j else 0) := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, mulVec_single]
  rw [← Matrix.mulVec_mulVec, hN, mulVec_diagonal]
  funext c
  simp

/-- For `α = aDiag t` with `t i = 2R`, `t k = -R` (`k ≠ i`) and `u = uij hij s` with
`s = -v i / v j`, the vector `α u v` has its `i`-th coordinate equal to `0` and its other
coordinates equal to `e^{-R} v c`.  Choosing `R` large makes all coordinates `≤ η`. -/
theorem Endgame_diag_short {i j : Fin 3} (hij : i ≠ j) (v : Fin 3 → ℝ) (hv : v j ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ (t : Fin 3 → ℝ) (s : ℝ), ∀ c : Fin 3,
      |Matrix.mulVec (Work.EKLContract.toMat
        (Work.EKLContract.aDiag t * Work.EKLContract.uij hij s)) v c| ≤ η := by
  set K : ℝ := (∑ c : Fin 3, |v c|) + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  set R : ℝ := Real.log (K / η) with hR
  have hexp : Real.exp (-R) = η / K := by
    rw [hR, Real.exp_neg, Real.exp_log (div_pos hKpos hη), inv_div]
  have hbound : ∀ c : Fin 3, Real.exp (-R) * |v c| ≤ η := by
    intro c
    rw [hexp]
    have hvc : |v c| ≤ K := by
      rw [hK]
      have h1 : |v c| ≤ ∑ d : Fin 3, |v d| :=
        Finset.single_le_sum (fun d _ => abs_nonneg (v d)) (Finset.mem_univ c)
      linarith
    calc η / K * |v c| ≤ η / K * K := by
          apply mul_le_mul_of_nonneg_left hvc
          positivity
      _ = η := by rw [div_mul_cancel₀ _ (ne_of_gt hKpos)]
  set t : Fin 3 → ℝ := fun k => if k = i then 2 * R else -R with ht
  set s : ℝ := - v i / v j with hs
  refine ⟨t, s, ?_⟩
  intro c
  have hsumt : (∑ k : Fin 3, t k) = 0 := by
    rw [ht, Fin.sum_univ_three]
    fin_cases i <;> simp <;> ring
  have hDoff : ∀ c : Fin 3, c ≠ i →
      Real.exp (t c - (∑ k : Fin 3, t k) / 3) = Real.exp (-R) := by
    intro c hc
    have htc : t c = -R := by rw [ht]; simp [hc]
    rw [hsumt, zero_div, sub_zero, htc]
  have hM : toMat (aDiag t * uij hij s)
      = Matrix.diagonal (fun k => Real.exp (t k - (∑ l : Fin 3, t l) / 3))
          * (1 + Matrix.single i j s) := by
    simp only [toMat_mul, toMat_aDiag, Work.EKLContract.Lemmas.toMat_uij]
  have hval : Matrix.mulVec
        (Matrix.diagonal (fun k => Real.exp (t k - (∑ l : Fin 3, t l) / 3))
          * (1 + Matrix.single i j s)) v
      = fun c => Real.exp (t c - (∑ k : Fin 3, t k) / 3)
          * (v c + if c = i then s * v j else 0) :=
    mulVec_diag_single _ i j s v
  have hvalc : Matrix.mulVec (toMat (aDiag t * uij hij s)) v c
      = Real.exp (t c - (∑ k : Fin 3, t k) / 3)
          * (v c + if c = i then s * v j else 0) := by
    rw [hM, congrFun hval c]
  rw [hvalc]
  by_cases hc : c = i
  · rw [hc, if_pos rfl]
    have hs0 : s * v j = - v i := by rw [hs]; exact div_mul_cancel₀ (- v i) hv
    have hz : v i + - v i = 0 := by ring
    rw [hs0, hz, mul_zero, abs_zero]
    exact hη.le
  · rw [if_neg hc, add_zero, hDoff c hc, abs_mul, abs_of_pos (Real.exp_pos (-R))]
    exact hbound c

end Work.EKLComp
