/-
  WilE9G / Lagrange — **`lagJacTrue_det`**.

  `lagJacTrue` is the honest Jacobian of the Lagrange system of the construction (its `(L,yt)`
  block is the derivative `∂_{l'} (μ₀(∂_{l₀}Φ + Φ c_{l₀}) - ∑_a μ_a ∂_{l₀}h_a)`), while `lagJac`
  carries the *same* system with the `(L,yt)` block transposed (it is the "convention" matrix whose
  determinant is used elsewhere).  The theorem says the two determinants agree at a Lagrange point.

  The proof proceeds in the abstract block model `cM` of `LagBlocks.lean`:

  * `cM A W g mu mu0` is `[[A, -W, g], [Wᵀ, 0, 0], [0, 2μ, 2μ₀]]` (`L,h,N` rows against `yt,μ,μ₀`
    columns), and `lagJac`/`lagJacTrue` are `cM` for `A = lagA1`/`lagA2` (with `lagA2 = lagA1ᵀ`);
  * if `μ₀ ≠ 0`, the determinant-preserving column operation
    `col_{μ₀} ← col_{μ₀} + ∑_a (μ_a/μ₀) col_{μ_a}` (the Lagrange equations `LagEq` and the
    normalisation `LagNorm` make the new column `2/μ₀ · e_N`) turns `cM` into the block matrix
    `cM0 A W = [[A,-W],[Wᵀ,0]]` bordered by `2/μ₀`, whose determinant is `det (cM0 A W) * (2/μ₀)`;
  * `det (cM0 A W) = det (cM0 Aᵀ W)` because `cM0 A W = fromBlocks A (-W) Wᵀ 0` is the transpose
    of `cM0` with `Aᵀ` (`det_fromBlocks_transpose_left`);
  * if `μ₀ = 0` then `LagNorm` gives a non-trivial multiplier and `LagEq` makes the `h`-rows
    linearly dependent, so both determinants vanish (`cM_det_eq_zero_of_dep_rows`).
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.Stratum
import Submission.Work.WilE9G.Lagrange.LagBlocks
import Submission.Work.WilE3.API.eaD_commute
import Submission.Work.WilE9G.Lagrange.det_fromBlocks_transpose_left
import Submission.Work.WilE9G.Lagrange.lagJac_eq_cM
import Submission.Work.WilE9G.Lagrange.lagJacTrue_eq_cM
import Submission.Work.WilE9G.Lagrange.lagA2_eq_transpose
import Submission.Work.WilE9G.Lagrange.cM_det_eq_zero_of_dep_rows

set_option linter.deprecated false
set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Lagrange
open Matrix
open WilkiesDesign WilkiesDesign.E Work.WilE9G

variable {r j : ℕ}

/-! ## The determinant-preserving column operation -/

/-- The coefficient function of the column operation `col_{μ₀} ← col_{μ₀} + ∑_a (μ_a/μ₀) col_{μ_a}`
of the abstract block model: the coefficient of `col_{μ₀}` itself is `1`, so the determinant is
unchanged. -/
def cCoef (mu : Fin j → ℝ) (mu0 : ℝ) : ((Fin r ⊕ Fin j) ⊕ Fin 1) → ℝ :=
  fun x => Sum.elim (Sum.elim (fun _ : Fin r => 0) (fun b : Fin j => mu b / mu0))
    (fun _ : Fin 1 => 1) x

@[simp] theorem cCoef_inl_inl (mu : Fin j → ℝ) (mu0 : ℝ) (i : Fin r) :
    cCoef (r := r) mu mu0 (Sum.inl (Sum.inl i)) = 0 := rfl

@[simp] theorem cCoef_inl_inr (mu : Fin j → ℝ) (mu0 : ℝ) (b : Fin j) :
    cCoef (r := r) mu mu0 (Sum.inl (Sum.inr b) : (Fin r ⊕ Fin j) ⊕ Fin 1) = mu b / mu0 := rfl

@[simp] theorem cCoef_inr (mu : Fin j → ℝ) (mu0 : ℝ) (u : Fin 1) :
    cCoef (r := r) mu mu0 (Sum.inr u : (Fin r ⊕ Fin j) ⊕ Fin 1) = 1 := rfl

/-- The reduced block matrix of the abstract model: the `μ₀`-column is supported on the
normalisation row. -/
def cMr (A : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin j) ℝ) (mu : Fin j → ℝ)
    (mu0 : ℝ) : Matrix ((Fin r ⊕ Fin j) ⊕ Fin 1) ((Fin r ⊕ Fin j) ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks (cM0 A W) 0
    (Matrix.of fun (_ : Fin 1) y => Sum.elim (fun _ => 0) (fun b => 2 * mu b) y)
    (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => 2 / mu0)

/-- The new `μ₀`-column produced by the operations of `cCoef`: it vanishes on the `L`- and
`h`-rows and equals `2/μ₀` on the normalisation row.  This is where `LagEq` and `LagNorm` are
used. -/
theorem cCoef_column (A : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ)
    (mu : Fin j → ℝ) {mu0 : ℝ} (hmu0 : mu0 ≠ 0)
    (hcon : ∀ l : Fin r, mu0 * g l = ∑ a, mu a * W l a)
    (hnorm : (∑ a, mu a ^ 2) + mu0 ^ 2 = 1) :
    ∀ x : (Fin r ⊕ Fin j) ⊕ Fin 1,
      (∑ y, cCoef mu mu0 y • cM A W g mu mu0 x y) = (if x = Sum.inr 0 then 2 / mu0 else 0) := by
  intro x
  rcases x with (⟨i|b⟩|u)
  · rw [if_neg (by simp : ¬ (Sum.inl (Sum.inl i) = (Sum.inr 0 : (Fin r ⊕ Fin j) ⊕ Fin 1)))]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [cCoef_inl_inl, cCoef_inl_inr, cCoef_inr, smul_eq_mul,
      cM_apply_inl_inl_inl_inr, cM_apply_inl_inl_inr, Fin.sum_univ_one, mul_neg]
    have hb : (∑ a₂ : Fin j, mu a₂ / mu0 * W i a₂) = g i := by
      have h1 : (∑ a₂ : Fin j, mu a₂ / mu0 * W i a₂) = mu0⁻¹ * (∑ a₂, mu a₂ * W i a₂) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b _ => by ring)
      rw [h1, ← hcon i]
      field_simp
    rw [show (∑ a₁ : Fin r, 0 * cM A W g mu mu0 (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl a₁)))
          = 0 from Finset.sum_eq_zero (fun a₁ _ => by ring), zero_add,
      Finset.sum_neg_distrib, hb]
    ring
  · rw [if_neg (by simp : ¬ (Sum.inl (Sum.inr b) = (Sum.inr 0 : (Fin r ⊕ Fin j) ⊕ Fin 1)))]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [cCoef_inl_inl, cCoef_inl_inr, cCoef_inr, smul_eq_mul,
      cM_apply_inl_inr_inl_inr, cM_apply_inl_inr_inr, Fin.sum_univ_one, mul_zero]
    simp
  · rw [Fin.eq_zero u, if_pos rfl]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [cCoef_inl_inl, cCoef_inl_inr, cCoef_inr, smul_eq_mul,
      cM_apply_inr_inl_inr, cM_apply_inr_inr, Fin.sum_univ_one, one_mul]
    have hN : (∑ a₂ : Fin j, mu a₂ / mu0 * (2 * mu a₂)) = (2 / mu0) * (∑ a₂, mu a₂ ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [show (∑ a₁ : Fin r, 0 * cM A W g mu mu0 (Sum.inr 0) (Sum.inl (Sum.inl a₁)))
          = 0 from Finset.sum_eq_zero (fun a₁ _ => by ring), zero_add, hN]
    have hfac : (2 / mu0) * (∑ a₂ : Fin j, mu a₂ ^ 2) + 2 * mu0
        = (2 / mu0) * ((∑ a₂ : Fin j, mu a₂ ^ 2) + mu0 ^ 2) := by
      field_simp
    rw [hfac, hnorm]
    ring

/-- The `μ₀ ≠ 0` reduction: the determinant of `cM` is that of the bordered core block `cM0`. -/
theorem cM_det_eq_mu0_ne_zero (A : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin j) ℝ)
    (g : Fin r → ℝ) (mu : Fin j → ℝ) {mu0 : ℝ} (hmu0 : mu0 ≠ 0)
    (hcon : ∀ l : Fin r, mu0 * g l = ∑ a, mu a * W l a)
    (hnorm : (∑ a, mu a ^ 2) + mu0 ^ 2 = 1) :
    (cM A W g mu mu0).det = (cM0 A W).det * (2 / mu0) := by
  have hsum := cCoef_column A W g mu hmu0 hcon hnorm
  have hunit : (cM A W g mu mu0).updateCol (Sum.inr 0)
      (fun k => ∑ y, cCoef mu mu0 y • cM A W g mu mu0 k y) = cMr A W mu mu0 := by
    rw [show (fun k => ∑ y, cCoef mu mu0 y • cM A W g mu mu0 k y)
          = (fun k => if k = Sum.inr 0 then 2 / mu0 else 0) from funext hsum]
    ext x y
    rcases y with (⟨k|b⟩|v)
    · rw [Matrix.updateCol_ne
        (by simp : (Sum.inl (Sum.inl k) : (Fin r ⊕ Fin j) ⊕ Fin 1) ≠ Sum.inr 0)]
      rcases x with (⟨i|a⟩|u) <;> simp [cM, cMr, cM0]
    · rw [Matrix.updateCol_ne
        (by simp : (Sum.inl (Sum.inr b) : (Fin r ⊕ Fin j) ⊕ Fin 1) ≠ Sum.inr 0)]
      rcases x with (⟨i|a⟩|u) <;> simp [cM, cMr, cM0]
    · rw [Fin.eq_zero v, Matrix.updateCol_self]
      rcases x with (⟨i|a⟩|u)
      · simp [cM, cMr, cM0]
      · simp [cM, cMr, cM0]
      · rw [Fin.eq_zero u]; simp [cM, cMr, cM0]
  have hdet : (cMr A W mu mu0).det = (cM0 A W).det * (2 / mu0) := by
    rw [cMr, Matrix.det_fromBlocks_zero₁₂]
    congr 1
    rw [Matrix.det_fin_one]
    rfl
  calc (cM A W g mu mu0).det
      = ((cM A W g mu mu0).updateCol (Sum.inr 0)
          (fun k => ∑ y, cCoef mu mu0 y • cM A W g mu mu0 k y)).det := by
          rw [Matrix.det_updateCol_sum]
          simp [cCoef]
      _ = (cMr A W mu mu0).det := by rw [hunit]
      _ = (cM0 A W).det * (2 / mu0) := hdet

/-- The core block is transpose-invariant in its top-left block. -/
theorem cM0_det_eq (A : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin j) ℝ) :
    (cM0 A W).det = (cM0 Aᵀ W).det := by
  have h := det_fromBlocks_transpose_left A (-W)
  simpa only [cM0, neg_neg, transpose_neg, neg_inj] using h

/-! ## The theorem -/

theorem lagJacTrue_det {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (hEq : Work.WilE9G.LagEq S Phi c z mu mu0) (hNorm : Work.WilE9G.LagNorm mu mu0) :
    (Work.WilE9G.Lagrange.lagJacTrue S Phi c z mu mu0).det
      = (Work.WilE9G.lagJac S Phi c z mu mu0).det := by
  have hcon : ∀ l : Fin (1 + m), mu0 * lagG S Phi c z l = ∑ a : Fin S.j, mu a * lagW S z l a :=
    fun l => by simp only [lagG, lagW, Matrix.of_apply] at *; exact hEq l
  have hnorm : (∑ a : Fin S.j, mu a ^ 2) + mu0 ^ 2 = 1 := hNorm
  rw [lagJac_eq_cM S Phi c z mu mu0, lagJacTrue_eq_cM S Phi c z mu mu0,
    lagA2_eq_transpose S Phi c z mu mu0, Matrix.det_submatrix_equiv_self,
    Matrix.det_submatrix_equiv_self]
  rcases eq_or_ne mu0 0 with h0 | h0
  · subst mu0
    have hdep : ∀ l : Fin (1 + m), ∑ a : Fin S.j, mu a * lagW S z l a = 0 := by
      intro l
      have hl := hcon l
      rw [zero_mul] at hl
      exact hl.symm
    have hne : ∃ a : Fin S.j, mu a ≠ 0 := by
      by_contra h
      push_neg at h
      have hzero : (∑ a : Fin S.j, mu a ^ 2) = 0 :=
        Finset.sum_eq_zero (fun a _ => by rw [h a]; ring)
      rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hnorm
      norm_num at hnorm
    obtain ⟨hdet, hdet'⟩ :=
      cM_det_eq_zero_of_dep_rows (lagA1 S Phi c z mu 0) (lagW S z) (lagG S Phi c z) mu hdep hne
    rw [hdet, hdet']
  · rw [cM_det_eq_mu0_ne_zero (lagA1 S Phi c z mu mu0)ᵀ (lagW S z) (lagG S Phi c z) mu h0 hcon
        hnorm,
      cM_det_eq_mu0_ne_zero (lagA1 S Phi c z mu mu0) (lagW S z) (lagG S Phi c z) mu h0 hcon
        hnorm]
    exact congrArg (· * (2 / mu0))
      (cM0_det_eq (lagA1 S Phi c z mu mu0) (lagW S z)).symm

end Work.WilE9G.Lagrange
