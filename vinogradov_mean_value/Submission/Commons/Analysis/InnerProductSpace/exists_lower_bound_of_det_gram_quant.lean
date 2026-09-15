import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Submission.Commons.Analysis.InnerProductSpace.exists_lower_bound_of_det_gram

namespace Commons.Analysis.InnerProductSpace

open Matrix

/-- Determinant bound with one distinguished column.  If every entry of column `i` of `M` is
bounded by `X ≥ 0` and every other entry by `Y ≥ 0`, then
`|det M| ≤ l! * X * Y ^ (l - 1)`. -/
lemma abs_det_le_of_col_bound {l : ℕ} (M : Matrix (Fin l) (Fin l) ℝ) (i : Fin l) {X Y : ℝ}
    (hX : 0 ≤ X)
    (hcol : ∀ a, |M a i| ≤ X) (hother : ∀ a b, b ≠ i → |M a b| ≤ Y) :
    |M.det| ≤ (l.factorial : ℝ) * X * Y ^ (l - 1) := by
  rw [Matrix.det_apply']
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ σ : Equiv.Perm (Fin l),
      |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ r, M (σ r) r| ≤ X * Y ^ (l - 1) := by
    intro σ
    rw [abs_mul]
    have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
    rw [hsign, one_mul]
    rw [Finset.abs_prod]
    rw [← Finset.mul_prod_erase (Finset.univ) (fun r => |M (σ r) r|) (Finset.mem_univ i)]
    apply mul_le_mul (hcol (σ i)) _ (Finset.prod_nonneg (fun r _ => abs_nonneg _)) hX
    calc ∏ r ∈ Finset.univ.erase i, |M (σ r) r| ≤ ∏ _r ∈ Finset.univ.erase i, Y := by
          apply Finset.prod_le_prod
          · intro r _; exact abs_nonneg _
          · intro r hr; exact hother (σ r) r (Finset.mem_erase.mp hr).1
      _ = Y ^ (Finset.univ.erase i).card := Finset.prod_const Y
      _ = Y ^ (l - 1) := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  calc ∑ σ : Equiv.Perm (Fin l), |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ r, M (σ r) r|
        ≤ ∑ _σ : Equiv.Perm (Fin l), X * Y ^ (l - 1) := Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (Fintype.card (Equiv.Perm (Fin l))) * (X * Y ^ (l - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (l.factorial : ℝ) * X * Y ^ (l - 1) := by
          rw [Fintype.card_perm, Fintype.card_fin]; ring

theorem exists_lower_bound_of_det_gram_quant {l : ℕ} (hl : 1 ≤ l)
    (s : Fin l → EuclideanSpace ℝ (Fin l)) {c A : ℝ} (hc : 0 < c) (hA : 1 ≤ A)
    (hsi : ∀ i, ‖s i‖ ≤ A) (h : c ≤ (Matrix.gram ℝ s).det) :
    ∀ w : Fin l → ℝ,
      c * ‖w‖ ≤ ((l : ℝ) * ((l - 1).factorial : ℝ) * A ^ (2 * l - 1))
        * ‖∑ i : Fin l, w i • s i‖ := by
  intro w
  set G : Matrix (Fin l) (Fin l) ℝ := Matrix.gram ℝ s with hG
  set u : EuclideanSpace ℝ (Fin l) := ∑ i, w i • s i with hu
  set v : Fin l → ℝ := fun j => inner ℝ (s j) u with hv
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hA0 : 0 ≤ A := le_of_lt hApos
  have hdet_pos : 0 < G.det := by
    rw [hG]; exact lt_of_lt_of_le hc h
  have hdet_ge : c ≤ G.det := by rw [hG]; exact h
  -- The Gram matrix times `w` computes the inner products with `u`.
  have hmulVec : G *ᵥ w = v := by
    funext j
    simp only [Matrix.mulVec, dotProduct, hv, hu, hG, Matrix.gram_apply]
    rw [inner_sum Finset.univ (fun i => w i • s i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_right]; ring
  -- Cramer's rule: `cramer G v = G.det • w`.
  have hcramer : G.cramer v = G.det • w := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hmulVec]
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hfac : (l.factorial : ℝ) = (l : ℝ) * ((l - 1).factorial : ℝ) := by
    have h : l - 1 + 1 = l := by omega
    conv_lhs => rw [← h]
    rw [Nat.factorial_succ, Nat.cast_mul, h]
  -- per-coordinate bound
  have hcoord : ∀ i : Fin l,
      |w i| ≤ (l.factorial : ℝ) * A ^ (2 * l - 1) * ‖u‖ / c := by
    intro i
    have hcol : ∀ a, |(G.updateCol i v) a i| ≤ A * ‖u‖ := by
      intro a
      rw [Matrix.updateCol_self, hv]
      exact (abs_real_inner_le_norm (s a) u).trans
        (mul_le_mul_of_nonneg_right (hsi a) (norm_nonneg u))
    have hother : ∀ a b, b ≠ i → |(G.updateCol i v) a b| ≤ A ^ 2 := by
      intro a b hb
      rw [Matrix.updateCol_ne hb, hG, Matrix.gram_apply]
      calc |inner ℝ (s a) (s b)| ≤ ‖s a‖ * ‖s b‖ := abs_real_inner_le_norm _ _
        _ ≤ A * A := mul_le_mul (hsi a) (hsi b) (norm_nonneg _) hA0
        _ = A ^ 2 := by ring
    have hpow : (A * ‖u‖) * (A ^ 2) ^ (l - 1) = A ^ (2 * l - 1) * ‖u‖ := by
      rw [← pow_mul]
      have hexp : 1 + 2 * (l - 1) = 2 * l - 1 := by omega
      rw [← hexp, pow_add, pow_one]
      ring
    have hdet_bound : |(G.updateCol i v).det| ≤ (l.factorial : ℝ) * A ^ (2 * l - 1) * ‖u‖ := by
      have h1 := abs_det_le_of_col_bound (G.updateCol i v) i (X := A * ‖u‖) (Y := A ^ 2)
        (mul_nonneg hA0 (norm_nonneg u)) hcol hother
      calc |(G.updateCol i v).det| ≤ (l.factorial : ℝ) * (A * ‖u‖) * (A ^ 2) ^ (l - 1) := h1
        _ = (l.factorial : ℝ) * ((A * ‖u‖) * (A ^ 2) ^ (l - 1)) := by ring
        _ = (l.factorial : ℝ) * (A ^ (2 * l - 1) * ‖u‖) := by rw [hpow]
        _ = (l.factorial : ℝ) * A ^ (2 * l - 1) * ‖u‖ := by ring
    have hwi_eq : G.det * w i = (G.updateCol i v).det := by
      have := congrFun hcramer i
      rw [Matrix.cramer_apply] at this
      rw [Pi.smul_apply, smul_eq_mul] at this
      exact this.symm
    have hd : |(G.updateCol i v).det| = G.det * |w i| := by
      rw [← hwi_eq, abs_mul, abs_of_pos hdet_pos]
    rw [hd] at hdet_bound
    have h2 : |w i| ≤ (l.factorial : ℝ) * A ^ (2 * l - 1) * ‖u‖ / G.det := by
      rw [le_div_iff₀ hdet_pos]
      rw [mul_comm]
      exact hdet_bound
    refine h2.trans (div_le_div_of_nonneg_left ?_ hc hdet_ge)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hA0 _)) (norm_nonneg u)
  have hK_nonneg : 0 ≤ (l.factorial : ℝ) * A ^ (2 * l - 1) * ‖u‖ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hA0 _)) (norm_nonneg u)
  have hw_bound : ‖w‖ ≤ (l.factorial : ℝ) * A ^ (2 * l - 1) * ‖u‖ / c := by
    refine (pi_norm_le_iff_of_nonneg (div_nonneg hK_nonneg hc.le)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact hcoord i
  calc c * ‖w‖ ≤ c * ((l.factorial : ℝ) * A ^ (2 * l - 1) * ‖u‖ / c) :=
        mul_le_mul_of_nonneg_left hw_bound hc.le
    _ = (l.factorial : ℝ) * A ^ (2 * l - 1) * ‖u‖ := by field_simp
    _ = ((l : ℝ) * ((l - 1).factorial : ℝ) * A ^ (2 * l - 1)) * ‖u‖ := by
          rw [hfac]

end Commons.Analysis.InnerProductSpace