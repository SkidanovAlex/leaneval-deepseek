import Mathlib
import Submission.Commons.Analysis.MomentCurve.transversality_det
import Submission.Commons.Analysis.InnerProductSpace.gram_det_shear_orthogonal
import Submission.Commons.LinearAlgebra.Matrix.det_le_prod_diag_of_posSemidef

open scoped BigOperators

/-!
# Lower bound for the Gram determinant of the torsion projection

Guo–Li–Yung–Zorin-Kranich, *A short proof of ℓ² decoupling for the moment curve*,
arXiv:1912.09798.  The `l` derivative vectors `γ^{(1)}(ξ₂), …, γ^{(l)}(ξ₂)` of the moment
curve, projected onto the orthogonal complement of `span{γ^{(1)}(ξ₁), …, γ^{(k-l)}(ξ₁)}`,
are linearly independent with a Gram determinant bounded below uniformly in
`ξ₁, ξ₂ ∈ [0,1]` with `|ξ₁ - ξ₂| ≥ 1/4`.

The proof combines the transversality determinant lower bound (`transversality_det`) with the
Schur-complement identity `det (gram (Sum.elim b a)) = det (gram b) * det (gram (proj a))`
(`gram_det_shear_orthogonal_of_span`).
-/

namespace Commons.Analysis.MomentCurve

/-- The falling factorial of `n` is bounded by `n!`. -/
private lemma descFactorial_le_factorial (n m : ℕ) : n.descFactorial m ≤ n.factorial := by
  by_cases h : m ≤ n
  · rw [Nat.descFactorial_eq_div h]
    exact Nat.div_le_self _ _
  · rw [not_le] at h
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
    exact Nat.zero_le _

/-- Every coordinate of `gam k θ a` is bounded by `k!` when `|θ| ≤ 1`. -/
private lemma gam_coord_abs_le (k : ℕ) {θ : ℝ} (hθ : |θ| ≤ 1) (a : ℕ) (j : Fin k) :
    |gam k θ a j| ≤ (k.factorial : ℝ) := by
  rw [gam_apply, abs_mul]
  have hj : j.val + 1 ≤ k := by have := j.isLt; omega
  have h1 : (((j.val + 1).descFactorial a : ℕ) : ℝ) ≤ (k.factorial : ℝ) := by
    have h2 := descFactorial_le_factorial (j.val + 1) a
    have h3 : (j.val + 1).factorial ≤ k.factorial := Nat.factorial_le hj
    exact_mod_cast le_trans h2 h3
  have h4 : |θ ^ (j.val + 1 - a)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg θ) hθ
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  calc (((j.val + 1).descFactorial a : ℕ) : ℝ) * |θ ^ (j.val + 1 - a)|
      ≤ (k.factorial : ℝ) * 1 := mul_le_mul h1 h4 (abs_nonneg _) (Nat.cast_nonneg _)
    _ = (k.factorial : ℝ) := by ring

/-- Squared euclidean norm bound for `gam k θ a`. -/
private lemma norm_sq_gam_le (k : ℕ) {θ : ℝ} (hθ : |θ| ≤ 1) (a : ℕ) :
    ‖(WithLp.equiv 2 (Fin k → ℝ)).symm (gam k θ a)‖ ^ 2
      ≤ (k : ℝ) * (k.factorial : ℝ) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc ∑ j : Fin k, ‖((WithLp.equiv 2 (Fin k → ℝ)).symm (gam k θ a)) j‖ ^ 2
      = ∑ j : Fin k, ‖gam k θ a j‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show ((WithLp.equiv 2 (Fin k → ℝ)).symm (gam k θ a)) j = gam k θ a j from rfl]
    _ ≤ ∑ _j : Fin k, (k.factorial : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (gam_coord_abs_le k hθ a j) 2
    _ = (k : ℝ) * (k.factorial : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

/-- The determinant of the Gram matrix of a family `v : Fin k → EuclideanSpace ℝ (Fin k)`
is the square of the determinant of the matrix of its coordinates. -/
private lemma det_gram_fin_eq_det_sq (k : ℕ) (v : Fin k → EuclideanSpace ℝ (Fin k)) :
    (Matrix.gram ℝ v).det =
      (Matrix.of (fun (i j : Fin k) => (v j : Fin k → ℝ) i)).det ^ 2 := by
  have h := Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin k) ℝ) v
  simp only at h
  have hm : (Matrix.of (fun (i : Fin k) (j : Fin k) =>
        (EuclideanSpace.basisFun (Fin k) ℝ).repr (v j) i))
      = Matrix.of (fun (i j : Fin k) => (v j : Fin k → ℝ) i) := by
    ext i j
    simp only [Matrix.of_apply]
    rw [EuclideanSpace.basisFun_repr]
  rw [h, hm, Matrix.det_mul]
  have hc : Matrix.conjTranspose (Matrix.of (fun (i j : Fin k) => (v j : Fin k → ℝ) i))
      = Matrix.transpose (Matrix.of (fun (i j : Fin k) => (v j : Fin k → ℝ) i)) := by
    ext i j; simp [Matrix.conjTranspose_apply]
  rw [hc, Matrix.det_transpose, sq]

/-- Splitting `Fin k` into the two blocks `Fin (k-l)` and `Fin l`. -/
noncomputable def sumEquivFin (k l : ℕ) (hlk : l ≤ k) : Fin (k - l) ⊕ Fin l ≃ Fin k where
  toFun x := match x with
    | Sum.inl i => ⟨i.val, by omega⟩
    | Sum.inr j => ⟨k - l + j.val, by omega⟩
  invFun n := if h : n.val < k - l then Sum.inl ⟨n.val, h⟩
    else Sum.inr ⟨n.val - (k - l), by have := n.isLt; omega⟩
  left_inv := by
    rintro (i | j)
    · dsimp only
      rw [dif_pos i.isLt]
    · dsimp only
      rw [dif_neg (show ¬ k - l + j.val < k - l by omega)]
      exact congrArg Sum.inr (Fin.ext (by simp))
  right_inv := by
    intro n
    dsimp only
    by_cases h : n.val < k - l
    · rw [dif_pos h]
    · rw [dif_neg h]
      exact Fin.ext (by simp; omega)

@[simp] lemma sumEquivFin_inl (k l : ℕ) (hlk : l ≤ k) (i : Fin (k - l)) :
    sumEquivFin k l hlk (Sum.inl i) = ⟨i.val, by omega⟩ := rfl

@[simp] lemma sumEquivFin_inr (k l : ℕ) (hlk : l ≤ k) (j : Fin l) :
    sumEquivFin k l hlk (Sum.inr j) = ⟨k - l + j.val, by omega⟩ := rfl

@[simp] lemma sumEquivFin_symm_apply (k l : ℕ) (hlk : l ≤ k) (n : Fin k) :
    (sumEquivFin k l hlk).symm n
      = if h : n.val < k - l then Sum.inl ⟨n.val, h⟩
        else Sum.inr ⟨n.val - (k - l), by have := n.isLt; omega⟩ := rfl

/-- The Gram determinant of the block family
`(γ^{(1)}(ξ₁), …, γ^{(k-l)}(ξ₁), γ^{(1)}(ξ₂), …, γ^{(l)}(ξ₂))`
equals the square of `det (Mmat k (k-l) ξ₁ ξ₂)`. -/
private lemma det_gram_elim_eq (k l : ℕ) (hlk : l ≤ k) (ξ₁ ξ₂ : ℝ) :
    (Matrix.gram ℝ (Sum.elim
        (fun i : Fin (k - l) => (WithLp.equiv 2 (Fin k → ℝ)).symm (gam k ξ₁ (i.val + 1)))
        (fun j : Fin l => (WithLp.equiv 2 (Fin k → ℝ)).symm (gam k ξ₂ (j.val + 1))))).det
      = (Mmat k (k - l) ξ₁ ξ₂).det ^ 2 := by
  let b : Fin (k - l) → EuclideanSpace ℝ (Fin k) :=
    fun i => (WithLp.equiv 2 (Fin k → ℝ)).symm (gam k ξ₁ (i.val + 1))
  let a : Fin l → EuclideanSpace ℝ (Fin k) :=
    fun j => (WithLp.equiv 2 (Fin k → ℝ)).symm (gam k ξ₂ (j.val + 1))
  let e := sumEquivFin k l hlk
  let V : Fin k → EuclideanSpace ℝ (Fin k) := fun n => Sum.elim b a (e.symm n)
  have hfam : (fun i : Fin (k - l) => (WithLp.equiv 2 (Fin k → ℝ)).symm (gam k ξ₁ (i.val + 1))) = b := rfl
  have hfam' : (fun j : Fin l => (WithLp.equiv 2 (Fin k → ℝ)).symm (gam k ξ₂ (j.val + 1))) = a := rfl
  rw [hfam, hfam']
  have hgram : Matrix.gram ℝ (Sum.elim b a) = (Matrix.gram ℝ V).submatrix e e := by
    ext x x'
    simp only [Matrix.gram_apply, Matrix.submatrix_apply, V, Equiv.symm_apply_apply]
  have hcoord : (Matrix.of (fun (i j : Fin k) => (V j : Fin k → ℝ) i))
      = Mmat k (k - l) ξ₁ ξ₂ := by
    ext i n
    simp only [Matrix.of_apply, Mmat, Matrix.of_apply]
    dsimp only [V, e]
    rw [sumEquivFin_symm_apply]
    by_cases h : n.val < k - l
    · rw [dif_pos h, if_pos h]
      rfl
    · rw [dif_neg h, if_neg h]
      rfl
  rw [hgram, Matrix.det_submatrix_equiv_self, det_gram_fin_eq_det_sq k V, hcoord]

/-- Lower bound for `|det (Mmat k l' ξ₁ ξ₂)|` under separation. -/
private lemma mmat_det_lower (k l' : ℕ) (hlk : l' ≤ k) :
    ∃ B : ℝ, 0 < B ∧ ∀ ξ₁ ξ₂ : ℝ, 0 ≤ ξ₁ → ξ₁ ≤ 1 → 0 ≤ ξ₂ → ξ₂ ≤ 1 →
      (1 / 4 : ℝ) ≤ |ξ₁ - ξ₂| → B ≤ |(Mmat k l' ξ₁ ξ₂).det| := by
  rcases Nat.eq_zero_or_pos l' with h0 | hpos
  · subst h0
    refine ⟨1, one_pos, ?_⟩
    intro ξ₁ ξ₂ _ _ _ _ _
    have hB : Mmat k 0 ξ₁ ξ₂ = Bmat k ξ₂ := by
      ext j i
      simp only [Mmat, Bmat, Matrix.of_apply]
      rw [if_neg (Nat.not_lt_zero _), Nat.sub_zero]
    rw [hB, det_Bmat, abs_of_nonneg (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _)]
    exact Finset.one_le_prod fun i _ => by
      have := Nat.factorial_pos (i.val + 1)
      exact_mod_cast this
  · obtain ⟨c, hcpos, hc⟩ := transversality_det k l' hpos hlk
    refine ⟨c * (1 / 4 : ℝ) ^ (l' * (k - l')), mul_pos hcpos (pow_pos (by norm_num) _), ?_⟩
    intro ξ₁ ξ₂ h1 h2 h3 h4 hsep
    have hmat : (Matrix.of (fun (j i : Fin k) =>
          if i.val < l' then ((j.val + 1).descFactorial (i.val + 1) : ℝ)
              * ξ₁ ^ (j.val + 1 - (i.val + 1))
            else ((j.val + 1).descFactorial (i.val - l' + 1) : ℝ)
              * ξ₂ ^ (j.val + 1 - (i.val - l' + 1))))
        = Mmat k l' ξ₁ ξ₂ := by
      ext j i
      simp only [Matrix.of_apply, Mmat, Matrix.of_apply, gam_apply]
    have h := hc ξ₁ ξ₂ h1 h2 h3 h4
    rw [hmat] at h
    have hpow : (1 / 4 : ℝ) ^ (l' * (k - l')) ≤ |ξ₁ - ξ₂| ^ (l' * (k - l')) :=
      pow_le_pow_left₀ (by norm_num) hsep _
    calc c * (1 / 4 : ℝ) ^ (l' * (k - l'))
        ≤ c * |ξ₁ - ξ₂| ^ (l' * (k - l')) :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt hcpos)
      _ ≤ |(Mmat k l' ξ₁ ξ₂).det| := h

theorem projected_torsion_det_orthogonal (k l : ℕ) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ₁ ξ₂ : ℝ, 0 ≤ ξ₁ → ξ₁ ≤ 1 → 0 ≤ ξ₂ → ξ₂ ≤ 1 →
      (1 / 4 : ℝ) ≤ |ξ₁ - ξ₂| →
      c ≤ (Matrix.gram ℝ (fun j : Fin l =>
            (Submodule.span ℝ (Set.range (fun i : Fin (k - l) =>
              (WithLp.equiv 2 (Fin k → ℝ)).symm (Commons.Analysis.MomentCurve.gam k ξ₁ (i.val + 1)))))ᗮ.starProjection
              ((WithLp.equiv 2 (Fin k → ℝ)).symm (Commons.Analysis.MomentCurve.gam k ξ₂ (j.val + 1))))).det := by
  obtain ⟨B, hBpos, hBlow⟩ := mmat_det_lower k (k - l) (by omega)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hMpos : 0 < ((k : ℝ) * (k.factorial : ℝ) ^ 2) ^ (k - l) :=
    pow_pos (mul_pos (by linarith) (pow_pos (Nat.cast_pos.mpr (Nat.factorial_pos k)) 2)) _
  refine ⟨B ^ 2 / ((k : ℝ) * (k.factorial : ℝ) ^ 2) ^ (k - l),
    div_pos (pow_pos hBpos 2) hMpos, ?_⟩
  intro ξ₁ ξ₂ hξ₁0 hξ₁1 hξ₂0 hξ₂1 hsep
  have hξ₁abs : |ξ₁| ≤ 1 := by rw [abs_of_nonneg hξ₁0]; exact hξ₁1
  let b : Fin (k - l) → EuclideanSpace ℝ (Fin k) :=
    fun i => (WithLp.equiv 2 (Fin k → ℝ)).symm (gam k ξ₁ (i.val + 1))
  let a : Fin l → EuclideanSpace ℝ (Fin k) :=
    fun j => (WithLp.equiv 2 (Fin k → ℝ)).symm (gam k ξ₂ (j.val + 1))
  let w : Fin l → EuclideanSpace ℝ (Fin k) :=
    fun j => (Submodule.span ℝ (Set.range b))ᗮ.starProjection (a j)
  change B ^ 2 / ((k : ℝ) * (k.factorial : ℝ) ^ 2) ^ (k - l) ≤ (Matrix.gram ℝ w).det
  have hnum : B ^ 2 ≤ (Matrix.gram ℝ (Sum.elim b a)).det := by
    have h := hBlow ξ₁ ξ₂ hξ₁0 hξ₁1 hξ₂0 hξ₂1 hsep
    have h2 : B ^ 2 ≤ |(Mmat k (k - l) ξ₁ ξ₂).det| ^ 2 := by
      nlinarith [h, hBpos, abs_nonneg ((Mmat k (k - l) ξ₁ ξ₂).det)]
    rw [sq_abs] at h2
    simpa only [← det_gram_elim_eq k l hlk ξ₁ ξ₂] using h2
  have hden : (Matrix.gram ℝ b).det ≤ ((k : ℝ) * (k.factorial : ℝ) ^ 2) ^ (k - l) := by
    have h1 := Commons.LinearAlgebra.Matrix.det_le_prod_diag_of_posSemidef
      (Matrix.gram ℝ b) (Matrix.posSemidef_gram ℝ b)
    calc (Matrix.gram ℝ b).det ≤ ∏ i : Fin (k - l), (Matrix.gram ℝ b) i i := h1
      _ ≤ ∏ _i : Fin (k - l), ((k : ℝ) * (k.factorial : ℝ) ^ 2) := by
          refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
          · rw [Matrix.gram_apply, real_inner_self_eq_norm_sq]; positivity
          · rw [Matrix.gram_apply, real_inner_self_eq_norm_sq]
            exact norm_sq_gam_le k hξ₁abs (i.val + 1)
      _ = ((k : ℝ) * (k.factorial : ℝ) ^ 2) ^ (k - l) := by
          rw [Finset.prod_const, Finset.card_fin]
  have hshear : (Matrix.gram ℝ (Sum.elim b a)).det
      = (Matrix.gram ℝ b).det * (Matrix.gram ℝ w).det := by
    refine Commons.Analysis.InnerProductSpace.gram_det_shear_orthogonal_of_span b a w ?_ ?_
    · intro j
      show a j - w j ∈ Submodule.span ℝ (Set.range b)
      simp only [w]
      rw [Submodule.starProjection_orthogonal_val]
      rw [sub_sub_cancel]
      exact Submodule.starProjection_apply_mem _ _
    · intro j
      exact Submodule.starProjection_apply_mem _ _
  have hb_nonneg : 0 ≤ (Matrix.gram ℝ b).det := (Matrix.posSemidef_gram ℝ b).det_nonneg
  have hb_pos : 0 < (Matrix.gram ℝ b).det := by
    rcases lt_or_eq_of_le hb_nonneg with h | h
    · exact h
    · exfalso
      have hzero : (Matrix.gram ℝ (Sum.elim b a)).det = 0 := by
        rw [hshear, ← h, zero_mul]
      nlinarith [hnum, hBpos]
  have hmain : (Matrix.gram ℝ b).det * (B ^ 2 / ((k : ℝ) * (k.factorial : ℝ) ^ 2) ^ (k - l))
      ≤ (Matrix.gram ℝ b).det * (Matrix.gram ℝ w).det := by
    calc (Matrix.gram ℝ b).det * (B ^ 2 / ((k : ℝ) * (k.factorial : ℝ) ^ 2) ^ (k - l))
        = B ^ 2 / ((k : ℝ) * (k.factorial : ℝ) ^ 2) ^ (k - l) * (Matrix.gram ℝ b).det := by ring
      _ ≤ B ^ 2 / ((k : ℝ) * (k.factorial : ℝ) ^ 2) ^ (k - l)
            * ((k : ℝ) * (k.factorial : ℝ) ^ 2) ^ (k - l) :=
          mul_le_mul_of_nonneg_left hden (le_of_lt (div_pos (pow_pos hBpos 2) hMpos))
      _ = B ^ 2 := by rw [div_mul_cancel₀]; exact ne_of_gt hMpos
      _ ≤ (Matrix.gram ℝ (Sum.elim b a)).det := hnum
      _ = (Matrix.gram ℝ b).det * (Matrix.gram ℝ w).det := hshear
  exact le_of_mul_le_mul_left hmain hb_pos

end Commons.Analysis.MomentCurve
