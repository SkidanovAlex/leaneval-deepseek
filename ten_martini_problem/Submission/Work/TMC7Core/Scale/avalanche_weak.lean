import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Avalanche.rift
import Submission.Work.Avalanche.svd
import Submission.Work.TMC7Core.Avalanche.avalanche_principle
import Submission.Work.TMC7Core.Scale.RiftDefs
import Submission.Work.TMC7Core.Avalanche.svd_ge_one

/-!
# The weak avalanche estimate for chains of `SL₂(ℂ)` matrices

`Work.TMC7Core.Scale.avalanche_weak`: for a sequence `A : ℕ → SL₂(ℂ)` with `‖A j‖_F ≥ μ ≥ 10⁶`
and pair defects `log ‖A (j+1)‖ + log ‖A j‖ - log ‖A (j+1) A j‖ ≤ (log μ)/2`, the defect of the
full product `P_m = matProd A m` differs from the sum of the pair defects by at most
`1000 m/√μ`.

The proof follows the structure of the Goldstein–Schlag / Bourgain–Jitomirskaya avalanche
principle:

* `rift W Y = ‖WY‖_F/(‖W‖_F ‖Y‖_F)` is the fraction of the product of the Frobenius norms
  surviving in the product;
* `rift_prod_le` (the analytic core): for `det = 1` matrices `W, X, M` of Frobenius norm `≥ μ`
  with `rift X M` not too small, replacing `X` by `X * M` changes `rift W ·` by at most
  `500 μ^{-3/2}`.  This is proved by writing the three matrices in singular-value form, which
  reduces the claim to the explicit diagonal-times-unitary algebra of `u_bounds` + `core_ineq`;
* telescoping (`assembly`) turns the target into `Σ_k (log rift (A k) (P k) - log rift (A k) (A (k-1)))`,
  and an induction gives the per-term bound `500/√μ`.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

namespace Work.TMC7Core.Scale

/-! ## 1. The diagonal matrix `Dg s = diag (s, s⁻¹)` -/

abbrev Dg (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((s : ℝ) : ℂ), ((s⁻¹ : ℝ) : ℂ)]

@[simp] theorem Dg_zero_zero (s : ℝ) : Dg s 0 0 = ((s : ℝ) : ℂ) := by
  simp [Dg, Matrix.diagonal_apply_eq, Matrix.cons_val_zero]

@[simp] theorem Dg_one_one (s : ℝ) : Dg s 1 1 = ((s⁻¹ : ℝ) : ℂ) := by
  simp [Dg, Matrix.diagonal_apply_eq, Matrix.cons_val_one]

@[simp] theorem Dg_zero_one (s : ℝ) : Dg s 0 1 = 0 := by
  show Matrix.diagonal ![((s : ℝ) : ℂ), ((s⁻¹ : ℝ) : ℂ)] 0 1 = 0
  rw [Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1)]

@[simp] theorem Dg_one_zero (s : ℝ) : Dg s 1 0 = 0 := by
  show Matrix.diagonal ![((s : ℝ) : ℂ), ((s⁻¹ : ℝ) : ℂ)] 1 0 = 0
  rw [Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]

/-- `‖((s : ℝ) : ℂ)‖ ^ 2 = s ^ 2`. -/
@[simp] theorem norm_ofReal_sq (s : ℝ) : ‖((s : ℝ) : ℂ)‖ ^ 2 = s ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  ring

/-! ## 2. Row and column norms of a unitary matrix -/

theorem row_norm_sq_eq_one (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T * Tᴴ = 1) (i : Fin 2) :
    ‖T i 0‖ ^ 2 + ‖T i 1‖ ^ 2 = 1 := by
  have h := Work.TMC7Core.Avalanche.re_mul_conjTranspose_diag T i
  rw [hT, Fin.sum_univ_two] at h
  simpa only [Matrix.one_apply_eq, Complex.one_re] using h.symm

theorem col_norm_sq_eq_one (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : Tᴴ * T = 1) (j : Fin 2) :
    ‖T 0 j‖ ^ 2 + ‖T 1 j‖ ^ 2 = 1 := by
  have h := Work.TMC7Core.Avalanche.re_mul_conjTranspose_diag Tᴴ j
  rw [Matrix.conjTranspose_conjTranspose, hT, Fin.sum_univ_two] at h
  simp only [Matrix.one_apply_eq, Complex.one_re, Matrix.conjTranspose_apply, norm_star,
    Fin.isValue] at h
  linarith [h]

/-! ## 3. Frobenius norms of the explicit products -/

theorem frob_Dg_sq (s : ℝ) : frob (Dg s) ^ 2 = FOf s := by
  show frob (Matrix.diagonal ![((s : ℝ) : ℂ), ((s⁻¹ : ℝ) : ℂ)]) ^ 2 = FOf s
  rw [Work.TMC7Core.Avalanche.frob_diagonal_sq' s s⁻¹, FOf, inv_pow]

theorem frob_Dg_mul_sq (s : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℂ) :
    frob (Dg s * Z) ^ 2
      = s ^ 2 * (‖Z 0 0‖ ^ 2 + ‖Z 0 1‖ ^ 2)
        + (s ^ 2)⁻¹ * (‖Z 1 0‖ ^ 2 + ‖Z 1 1‖ ^ 2) := by
  rw [frob_sq]
  simp only [Dg, Matrix.diagonal_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.sum_univ_two, norm_mul, norm_ofReal_sq, inv_pow, mul_pow, Fin.isValue]
  ring

theorem frob_Dg_mul_sq' (s : ℝ) (Z : Matrix (Fin 2) (Fin 2) ℂ) :
    frob (Dg s * Z) ^ 2
      = s ^ 2 * (‖Z 0 0‖ ^ 2 + ‖Z 0 1‖ ^ 2)
        + (s ^ 2)⁻¹ * (frob Z ^ 2 - (‖Z 0 0‖ ^ 2 + ‖Z 0 1‖ ^ 2)) := by
  rw [frob_Dg_mul_sq s Z, frob_sq Z]
  ring

theorem row_norm_Dg_sq (b : ℝ) (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T * Tᴴ = 1) :
    ‖(T * Dg b) 0 0‖ ^ 2 + ‖(T * Dg b) 0 1‖ ^ 2 = pOf b (‖T 0 0‖ ^ 2) := by
  have hrow := row_norm_sq_eq_one T hT 0
  have h00 : ‖(T * Dg b) 0 0‖ ^ 2 = b ^ 2 * ‖T 0 0‖ ^ 2 := by
    simp only [Dg, Matrix.mul_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
      norm_mul, mul_pow, norm_ofReal_sq, Fin.isValue]
    ring
  have h01 : ‖(T * Dg b) 0 1‖ ^ 2 = (b ^ 2)⁻¹ * ‖T 0 1‖ ^ 2 := by
    simp only [Dg, Matrix.mul_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
      norm_mul, mul_pow, norm_ofReal_sq, inv_pow, Fin.isValue]
    ring
  have h1 : ‖T 0 1‖ ^ 2 = 1 - ‖T 0 0‖ ^ 2 := by linarith [hrow]
  rw [h00, h01, h1, pOf]

theorem row_norm_Dg_mul_Dg_sq (b c : ℝ) (T R : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖(T * Dg b * R * Dg c) 0 0‖ ^ 2 + ‖(T * Dg b * R * Dg c) 0 1‖ ^ 2
      = c ^ 2 * ‖((b : ℝ) : ℂ) * T 0 0 * R 0 0 + (((b⁻¹ : ℝ)) : ℂ) * T 0 1 * R 1 0‖ ^ 2
        + (c ^ 2)⁻¹ * ‖((b : ℝ) : ℂ) * T 0 0 * R 0 1 + (((b⁻¹ : ℝ)) : ℂ) * T 0 1 * R 1 1‖ ^ 2 := by
  have h00 : (T * Dg b * R * Dg c) 0 0
      = (((b : ℝ) : ℂ) * T 0 0 * R 0 0 + (((b⁻¹ : ℝ)) : ℂ) * T 0 1 * R 1 0)
        * ((c : ℝ) : ℂ) := by
    simp only [Dg, Dg_zero_zero, Dg_one_one, Dg_zero_one, Dg_one_zero, Matrix.mul_diagonal,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Fin.isValue]
    ring
  have h01 : (T * Dg b * R * Dg c) 0 1
      = (((b : ℝ) : ℂ) * T 0 0 * R 0 1 + (((b⁻¹ : ℝ)) : ℂ) * T 0 1 * R 1 1)
        * ((c⁻¹ : ℝ) : ℂ) := by
    simp only [Dg, Dg_zero_zero, Dg_one_one, Dg_zero_one, Dg_one_zero, Matrix.mul_diagonal,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Fin.isValue]
    ring
  rw [h00, h01]
  simp only [norm_mul, mul_pow, norm_ofReal_sq, inv_pow]
  ring

theorem frob_Dg_mul_Dg_sq (b c : ℝ) (R : Matrix (Fin 2) (Fin 2) ℂ) (hR : Rᴴ * R = 1)
    (hR' : R * Rᴴ = 1) :
    frob (Dg b * R * Dg c) ^ 2 = FZ b c (‖R 0 0‖ ^ 2) := by
  obtain ⟨e11, e01, e10⟩ := Work.TMC7Core.Avalanche.unitary_entries R hR hR'
  have h00 : ‖(R * Dg c) 0 0‖ ^ 2 = c ^ 2 * ‖R 0 0‖ ^ 2 := by
    simp only [Dg, Matrix.mul_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
      norm_mul, mul_pow, norm_ofReal_sq, Fin.isValue]
    ring
  have h01 : ‖(R * Dg c) 0 1‖ ^ 2 = (c ^ 2)⁻¹ * ‖R 0 1‖ ^ 2 := by
    simp only [Dg, Matrix.mul_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
      norm_mul, mul_pow, norm_ofReal_sq, inv_pow, Fin.isValue]
    ring
  have h10 : ‖(R * Dg c) 1 0‖ ^ 2 = c ^ 2 * ‖R 1 0‖ ^ 2 := by
    simp only [Dg, Matrix.mul_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
      norm_mul, mul_pow, norm_ofReal_sq, Fin.isValue]
    ring
  have h11 : ‖(R * Dg c) 1 1‖ ^ 2 = (c ^ 2)⁻¹ * ‖R 1 1‖ ^ 2 := by
    simp only [Dg, Matrix.mul_diagonal, Matrix.cons_val_zero, Matrix.cons_val_one,
      norm_mul, mul_pow, norm_ofReal_sq, inv_pow, Fin.isValue]
    ring
  rw [show Dg b * R * Dg c = Dg b * (R * Dg c) from by rw [mul_assoc],
    frob_Dg_mul_sq b (R * Dg c), h00, h01, h10, h11, e11, e01, e10, FZ]
  ring

end Work.TMC7Core.Scale

namespace Work.TMC7Core.Scale

theorem cstar_re (z : ℂ) : (star z).re = z.re := rfl

theorem cstar_im (z : ℂ) : (star z).im = -z.im := rfl

theorem norm_sq_add (A B : ℂ) : ‖A + B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + 2 * (A * star B).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, cstar_re, cstar_im]
  ring

theorem abs_two_re_mul_conj_le (A B : ℂ) : |2 * (A * star B).re| ≤ 2 * ‖A‖ * ‖B‖ := by
  have h := Complex.abs_re_le_norm (A * star B)
  rw [norm_mul, norm_star] at h
  have h2 : |2 * (A * star B).re| = 2 * |(A * star B).re| := by
    rw [abs_mul, abs_two]
  rw [h2]
  linarith

theorem sqrt_prod4 {x y z w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    Real.sqrt (x * y * z * w) = Real.sqrt x * Real.sqrt y * Real.sqrt z * Real.sqrt w := by
  rw [show x * y * z * w = (x * y) * (z * w) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_mul hx, Real.sqrt_mul hz]
  ring

theorem u_bounds (t0 t1 r00 r01 r10 r11 : ℂ) (b q α : ℝ) (hb : 0 < b)
    (hq : ‖t0‖ ^ 2 = q) (ht : ‖t0‖ ^ 2 + ‖t1‖ ^ 2 = 1)
    (hα : ‖r00‖ ^ 2 = α) (hr0 : ‖r00‖ ^ 2 + ‖r01‖ ^ 2 = 1)
    (hr1 : ‖r10‖ ^ 2 + ‖r00‖ ^ 2 = 1) (hr2 : ‖r11‖ ^ 2 = ‖r00‖ ^ 2) :
    |‖((b : ℝ) : ℂ) * t0 * r00 + (((b⁻¹ : ℝ)) : ℂ) * t1 * r10‖ ^ 2
        - (b ^ 2 * q * α + (b ^ 2)⁻¹ * (1 - q) * (1 - α))|
      ≤ 2 * Real.sqrt (q * α * (1 - q) * (1 - α))
    ∧ |‖((b:ℝ):ℂ) * t0 * r01 + (((b⁻¹:ℝ)):ℂ) * t1 * r11‖ ^ 2
        - (b ^ 2 * q * (1 - α) + (b ^ 2)⁻¹ * (1 - q) * α)|
      ≤ 2 * Real.sqrt (q * (1 - α) * (1 - q) * α) := by
  have ht1 : ‖t1‖ ^ 2 = 1 - q := by linarith
  have hr01 : ‖r01‖ ^ 2 = 1 - α := by linarith
  have hr10 : ‖r10‖ ^ 2 = 1 - α := by linarith
  have hq0 : 0 ≤ q := by rw [← hq]; positivity
  have hα0 : 0 ≤ α := by rw [← hα]; positivity
  have h1q : 0 ≤ 1 - q := by rw [← ht1]; positivity
  have h1α : 0 ≤ 1 - α := by rw [← hr10]; positivity
  have hbne : b ≠ 0 := ne_of_gt hb
  have key : ∀ A B : ℂ, |‖A + B‖ ^ 2 - (‖A‖ ^ 2 + ‖B‖ ^ 2)| ≤ 2 * ‖A‖ * ‖B‖ := by
    intro A B
    have h := abs_two_re_mul_conj_le A B
    have heq : ‖A + B‖ ^ 2 - (‖A‖ ^ 2 + ‖B‖ ^ 2) = 2 * (A * star B).re := by
      rw [norm_sq_add]; ring
    rw [heq]
    exact h
  constructor
  · have hsq0 : ‖t0‖ = Real.sqrt q := by rw [← hq, Real.sqrt_sq (norm_nonneg t0)]
    have hsqr : ‖r00‖ = Real.sqrt α := by rw [← hα, Real.sqrt_sq (norm_nonneg r00)]
    have hsq1 : ‖t1‖ = Real.sqrt (1 - q) := by rw [← ht1, Real.sqrt_sq (norm_nonneg t1)]
    have hsqr1 : ‖r10‖ = Real.sqrt (1 - α) := by rw [← hr10, Real.sqrt_sq (norm_nonneg r10)]
    have hAn : ‖((b : ℝ) : ℂ) * t0 * r00‖ = b * Real.sqrt q * Real.sqrt α := by
      rw [norm_mul, norm_mul, Work.TMC7Core.Avalanche.norm_ofReal, hsq0, hsqr, abs_of_pos hb]
    have hBn : ‖(((b⁻¹ : ℝ)) : ℂ) * t1 * r10‖
        = b⁻¹ * Real.sqrt (1 - q) * Real.sqrt (1 - α) := by
      rw [norm_mul, norm_mul, Work.TMC7Core.Avalanche.norm_ofReal, hsq1, hsqr1,
        abs_of_pos (inv_pos.mpr hb)]
    have hA2 : ‖((b : ℝ) : ℂ) * t0 * r00‖ ^ 2 = b ^ 2 * q * α := by
      rw [hAn, mul_pow, mul_pow, Real.sq_sqrt hq0, Real.sq_sqrt hα0]
    have hB2 : ‖(((b⁻¹ : ℝ)) : ℂ) * t1 * r10‖ ^ 2 = (b ^ 2)⁻¹ * (1 - q) * (1 - α) := by
      rw [hBn, mul_pow, mul_pow, Real.sq_sqrt h1q, Real.sq_sqrt h1α, inv_pow]
    have hprod : 2 * ‖((b : ℝ) : ℂ) * t0 * r00‖ * ‖(((b⁻¹ : ℝ)) : ℂ) * t1 * r10‖
        = 2 * Real.sqrt (q * α * (1 - q) * (1 - α)) := by
      rw [hAn, hBn, sqrt_prod4 hq0 hα0 h1q h1α]
      field_simp <;> ring
    have h1 := key (((b : ℝ) : ℂ) * t0 * r00) ((((b⁻¹ : ℝ)) : ℂ) * t1 * r10)
    rw [hA2, hB2, hprod] at h1
    exact h1
  · have hsq0 : ‖t0‖ = Real.sqrt q := by rw [← hq, Real.sqrt_sq (norm_nonneg t0)]
    have hsq1 : ‖t1‖ = Real.sqrt (1 - q) := by rw [← ht1, Real.sqrt_sq (norm_nonneg t1)]
    have hsqr01 : ‖r01‖ = Real.sqrt (1 - α) := by rw [← hr01, Real.sqrt_sq (norm_nonneg r01)]
    have hsqr11 : ‖r11‖ = Real.sqrt α := by
      rw [← show ‖r11‖ ^ 2 = α from by rw [hr2, hα], Real.sqrt_sq (norm_nonneg r11)]
    have hAn : ‖((b : ℝ) : ℂ) * t0 * r01‖ = b * Real.sqrt q * Real.sqrt (1 - α) := by
      rw [norm_mul, norm_mul, Work.TMC7Core.Avalanche.norm_ofReal, hsq0, hsqr01, abs_of_pos hb]
    have hBn : ‖(((b⁻¹ : ℝ)) : ℂ) * t1 * r11‖ = b⁻¹ * Real.sqrt (1 - q) * Real.sqrt α := by
      rw [norm_mul, norm_mul, Work.TMC7Core.Avalanche.norm_ofReal, hsq1, hsqr11,
        abs_of_pos (inv_pos.mpr hb)]
    have hA2 : ‖((b : ℝ) : ℂ) * t0 * r01‖ ^ 2 = b ^ 2 * q * (1 - α) := by
      rw [hAn, mul_pow, mul_pow, Real.sq_sqrt hq0, Real.sq_sqrt h1α]
    have hB2 : ‖(((b⁻¹ : ℝ)) : ℂ) * t1 * r11‖ ^ 2 = (b ^ 2)⁻¹ * (1 - q) * α := by
      rw [hBn, mul_pow, mul_pow, Real.sq_sqrt h1q, Real.sq_sqrt hα0, inv_pow]
    have hprod : 2 * ‖((b : ℝ) : ℂ) * t0 * r01‖ * ‖(((b⁻¹ : ℝ)) : ℂ) * t1 * r11‖
        = 2 * Real.sqrt (q * (1 - α) * (1 - q) * α) := by
      rw [hAn, hBn, sqrt_prod4 hq0 h1α h1q hα0]
      field_simp <;> ring
    have h1 := key (((b : ℝ) : ℂ) * t0 * r01) ((((b⁻¹ : ℝ)) : ℂ) * t1 * r11)
    rw [hA2, hB2, hprod] at h1
    exact h1

theorem Phi_eq (a p F : ℝ) (hF : F ≠ 0) (ha : 0 < a) :
    Phi a p F = p / F * ((a ^ 4 - 1) / (a ^ 4 + 1)) + 1 / (a ^ 4 + 1) := by
  unfold Phi
  have ha2 : a ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have ha4 : a ^ 4 + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem Phi_sub_eq (a p1 F1 p2 F2 : ℝ) (h1 : F1 ≠ 0) (h2 : F2 ≠ 0) (ha : 0 < a) :
    Phi a p1 F1 - Phi a p2 F2 = (a ^ 4 - 1) / (a ^ 4 + 1) * (p1 / F1 - p2 / F2) := by
  rw [Phi_eq a p1 F1 h1 ha, Phi_eq a p2 F2 h2 ha]
  ring

theorem Phi_sub_le (a p1 F1 p2 F2 : ℝ) (h1 : 0 < F1) (h2 : 0 < F2) (ha : 1 ≤ a) :
    |Phi a p1 F1 - Phi a p2 F2| ≤ |p1 / F1 - p2 / F2| := by
  rw [Phi_sub_eq a p1 F1 p2 F2 (ne_of_gt h1) (ne_of_gt h2) (by linarith), abs_mul]
  have ha4 : (1:ℝ) ≤ a ^ 4 := by
    have h2 : (1:ℝ) ≤ a ^ 2 := by nlinarith [sq_nonneg (a - 1)]
    nlinarith [sq_nonneg (a ^ 2 - 1), h2]
  have hle : |(a ^ 4 - 1) / (a ^ 4 + 1)| ≤ 1 := by
    have hpos : (0:ℝ) < a ^ 4 + 1 := by positivity
    rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_of_nonneg (by linarith : (0:ℝ) ≤ a ^ 4 - 1)]
    linarith
  calc |(a ^ 4 - 1) / (a ^ 4 + 1)| * |p1 / F1 - p2 / F2| ≤ 1 * |p1 / F1 - p2 / F2| :=
        mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ = |p1 / F1 - p2 / F2| := one_mul _

end Work.TMC7Core.Scale

namespace Work.TMC7Core.Scale

theorem mu_sqrt_le (μ : ℝ) (hμ : 16 ≤ μ) : μ * Real.sqrt μ ≤ μ ^ 3 / 16 := by
  have hμpos : 0 < μ := by linarith
  have step1 : 16 * Real.sqrt μ ≤ μ ^ 2 := by
    have hsq : (16 * Real.sqrt μ)^2 ≤ (μ ^ 2)^2 := by
      rw [mul_pow, Real.sq_sqrt hμpos.le]
      have h2 : (256:ℝ) ≤ μ ^ 2 := by nlinarith [hμ, sq_nonneg (μ - 16)]
      have h3 : (256:ℝ) ≤ μ ^ 3 := by
        have hm := mul_le_mul_of_nonneg_left h2 hμpos.le
        nlinarith [hm]
      have hm := mul_le_mul_of_nonneg_left h3 hμpos.le
      nlinarith [hm]
    calc 16 * Real.sqrt μ = Real.sqrt ((16 * Real.sqrt μ)^2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((μ ^ 2)^2) := Real.sqrt_le_sqrt hsq
      _ = μ ^ 2 := Real.sqrt_sq (by positivity)
  have h2 : μ * (16 * Real.sqrt μ) ≤ μ * μ ^ 2 := mul_le_mul_of_nonneg_left step1 hμpos.le
  have h3 : 16 * (μ * Real.sqrt μ) ≤ μ ^ 3 := by nlinarith [h2]
  linarith [h3]

theorem sq_lower (b μ : ℝ) (hμ : 16 ≤ μ) (hb : μ / Real.sqrt 2 ≤ b) : μ ^ 2 / 2 ≤ b ^ 2 := by
  have hμpos : 0 < μ := by linarith
  have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ μ / Real.sqrt 2) hb 2
  rwa [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h

theorem fourth_lower (b μ : ℝ) (hμ : 16 ≤ μ) (hb : μ / Real.sqrt 2 ≤ b) : μ ^ 4 / 4 ≤ b ^ 4 := by
  have h := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ μ^2/2) (sq_lower b μ hμ hb)
  calc μ^4/4 = (μ^2/2)*(μ^2/2) := by ring
    _ ≤ b^2 * b^2 := h
    _ = b^4 := by ring

theorem b2m_pos (μ : ℝ) (hμ : 16 ≤ μ) : 0 < μ ^ 2 / 2 := by positivity

theorem b2_alpha_lower (b μ α : ℝ) (hμ : 16 ≤ μ) (hb : μ / Real.sqrt 2 ≤ b)
    (hα : 1 / (4 * μ) ≤ α) : μ * Real.sqrt μ / 4 ≤ b ^ 2 * Real.sqrt α := by
  have hμpos : 0 < μ := by linarith
  have hαpos : 0 < α := by
    have h : 0 < 1/(4*μ) := by positivity
    linarith
  have hsα : 1 / (2 * Real.sqrt μ) ≤ Real.sqrt α := by
    have h1 : (1/(2*Real.sqrt μ)) = Real.sqrt (1/(4*μ)) := by
      rw [show (1:ℝ)/(4*μ) = (1/(2*Real.sqrt μ))^2 by
        rw [div_pow, mul_pow, Real.sq_sqrt hμpos.le]; ring]
      exact (Real.sqrt_sq (by positivity)).symm
    rw [h1]
    exact Real.sqrt_le_sqrt hα
  have h := mul_le_mul (sq_lower b μ hμ hb) hsα (by positivity) (by positivity)
  have h3 : (μ ^ 2 / 2) * (1 / (2 * Real.sqrt μ)) = μ * Real.sqrt μ / 4 := by
    field_simp
    nlinarith [Real.sq_sqrt hμpos.le]
  rw [h3] at h
  exact h

theorem b4_alpha_lower (b μ α : ℝ) (hμ : 16 ≤ μ) (hb : μ / Real.sqrt 2 ≤ b)
    (hα : 1 / (4 * μ) ≤ α) : μ * Real.sqrt μ ≤ b ^ 4 * α := by
  have hμpos : 0 < μ := by linarith
  have hαpos : 0 < α := by
    have h : 0 < 1/(4*μ) := by positivity
    linarith
  have h1 : μ ^ 3 / 16 ≤ b ^ 4 * α := by
    have h10 := mul_le_mul (fourth_lower b μ hμ hb) hα (by positivity) (by positivity)
    have h2 : μ ^ 4 / 4 * (1 / (4 * μ)) = μ ^ 3 / 16 := by
      have hμne : μ ≠ 0 := ne_of_gt hμpos
      field_simp
      ring
    linarith [h10, h2]
  have h3 : μ * Real.sqrt μ ≤ μ ^ 3 / 16 := mu_sqrt_le μ hμ
  linarith [h1, h3]

theorem bc_lower (b c μ α : ℝ) (hμ : 16 ≤ μ) (hb : μ / Real.sqrt 2 ≤ b)
    (hc : μ / Real.sqrt 2 ≤ c) (hα : 1 / (4 * μ) ≤ α) : μ ^ 3 / 16 ≤ b ^ 2 * c ^ 2 * α := by
  have hμpos : 0 < μ := by linarith
  have hαpos : 0 < α := by
    have h : 0 < 1/(4*μ) := by positivity
    linarith
  have h1 : (μ^2/2) * (μ^2/2) ≤ b^2 * c^2 :=
    mul_le_mul (sq_lower b μ hμ hb) (sq_lower c μ hμ hc) (by positivity) (by positivity)
  have h2 : (μ^2/2) * (μ^2/2) * (1/(4*μ)) ≤ b^2 * c^2 * α :=
    mul_le_mul h1 hα (by positivity) (by positivity)
  have h3 : (μ^2/2) * (μ^2/2) * (1/(4*μ)) = μ^3/16 := by
    have hμne : μ ≠ 0 := ne_of_gt hμpos
    field_simp
    ring
  linarith [h2, h3]

theorem n1_bound (b μ α : ℝ) (hμ : 16 ≤ μ) (hb : μ / Real.sqrt 2 ≤ b)
    (hα : 1 / (4 * μ) ≤ α) : 1 / (b ^ 4 * α) ≤ 100 / (μ * Real.sqrt μ) := by
  have hμpos : 0 < μ := by linarith
  have hb0 : 0 < b := by
    have h : 0 < μ / Real.sqrt 2 := by positivity
    linarith
  have hαpos : 0 < α := by
    have h : 0 < 1/(4*μ) := by positivity
    linarith
  have h1 : μ * Real.sqrt μ ≤ b ^ 4 * α := b4_alpha_lower b μ α hμ hb hα
  have hb4α : 0 ≤ b ^ 4 * α := le_of_lt (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc μ * Real.sqrt μ ≤ b ^ 4 * α := h1
    _ ≤ 100 * (b ^ 4 * α) := le_mul_of_one_le_left hb4α (by norm_num)

theorem n2_bound (b μ α δ : ℝ) (hμ : 16 ≤ μ) (hb : μ / Real.sqrt 2 ≤ b)
    (hα : 1 / (4 * μ) ≤ α) (hδ : 2 * δ ≤ Real.sqrt α) :
    2 * δ / (b ^ 2 * α) ≤ 100 / (μ * Real.sqrt μ) := by
  have hμpos : 0 < μ := by linarith
  have hb0 : 0 < b := by
    have h : 0 < μ / Real.sqrt 2 := by positivity
    linarith
  have hα0 : 0 ≤ α := by
    have h : 0 < 1/(4*μ) := by positivity
    linarith
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity : (0:ℝ) < 1/(4*μ)) hα
  have h1 : μ * Real.sqrt μ / 4 ≤ b ^ 2 * Real.sqrt α := b2_alpha_lower b μ α hμ hb hα
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 2 * δ * (μ * Real.sqrt μ) ≤ Real.sqrt α * (μ * Real.sqrt μ) :=
    mul_le_mul_of_nonneg_right hδ (by positivity)
  have h4 : Real.sqrt α * (μ * Real.sqrt μ / 4) ≤ Real.sqrt α * (b ^ 2 * Real.sqrt α) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h5 : Real.sqrt α * (b ^ 2 * Real.sqrt α) = b ^ 2 * α := by
    rw [show Real.sqrt α * (b ^ 2 * Real.sqrt α) = b^2 * (Real.sqrt α * Real.sqrt α) by ring,
      ← sq (Real.sqrt α), Real.sq_sqrt hα0]
  rw [h5] at h4
  have h4' : Real.sqrt α * (μ * Real.sqrt μ) ≤ 4 * (b ^ 2 * α) := by nlinarith [h4]
  have h6 : 4 * (b ^ 2 * α) ≤ 100 * (b ^ 2 * α) := by
    have hb2α : 0 ≤ b ^ 2 * α := by positivity
    nlinarith [hb2α]
  nlinarith [h2, h4', h6]

theorem n3_bound (b c μ α : ℝ) (hμ : 16 ≤ μ) (hb : μ / Real.sqrt 2 ≤ b)
    (hc : μ / Real.sqrt 2 ≤ c) (hα : 1 / (4 * μ) ≤ α) :
    1 / (b ^ 2 * c ^ 2 * α) ≤ 100 / (μ * Real.sqrt μ) := by
  have hμpos : 0 < μ := by linarith
  have hb0 : 0 < b := by
    have h : 0 < μ / Real.sqrt 2 := by positivity
    linarith
  have hc0 : 0 < c := by
    have h : 0 < μ / Real.sqrt 2 := by positivity
    linarith
  have hαpos : 0 < α := by
    have h : 0 < 1/(4*μ) := by positivity
    linarith
  have h1 : μ ^ 3 / 16 ≤ b ^ 2 * c ^ 2 * α := bc_lower b c μ α hμ hb hc hα
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h0 : μ * Real.sqrt μ ≤ 100 * (μ ^ 3 / 16) := by
    have h := mu_sqrt_le μ hμ
    have hx : 0 ≤ μ ^ 3 / 16 := le_of_lt (by positivity)
    calc μ * Real.sqrt μ ≤ μ ^ 3 / 16 := h
      _ ≤ 100 * (μ ^ 3 / 16) := le_mul_of_one_le_left hx (by norm_num)
  have h2 : 100 * (μ ^ 3 / 16) ≤ 100 * (b ^ 2 * c ^ 2 * α) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  linarith [h0, h2]

theorem n4_bound (b c μ α δ : ℝ) (hμ : 16 ≤ μ) (hb : μ / Real.sqrt 2 ≤ b)
    (hc : μ / Real.sqrt 2 ≤ c) (hα : 1 / (4 * μ) ≤ α) (hc1 : 1 ≤ c) (hδ0 : 0 ≤ δ)
    (hN2 : 2 * δ / (b ^ 2 * α) ≤ 100 / (μ * Real.sqrt μ)) :
    2 * δ / (b ^ 2 * c ^ 2 * α) ≤ 100 / (μ * Real.sqrt μ) := by
  have hμpos : 0 < μ := by linarith
  have hb0 : 0 < b := by
    have h : 0 < μ / Real.sqrt 2 := by positivity
    linarith
  have hαpos : 0 < α := by
    have h : 0 < 1/(4*μ) := by positivity
    linarith
  have hc0 : 0 < c := by linarith
  have h1 : 2 * δ / (b ^ 2 * c ^ 2 * α) ≤ 2 * δ / (b ^ 2 * α) := by
    apply div_le_div_of_nonneg_left (by linarith : (0:ℝ) ≤ 2 * δ) (by positivity)
    have hc2g : (1:ℝ) ≤ c ^ 2 := by nlinarith [hc1]
    have h2 := mul_le_mul_of_nonneg_right hc2g (by positivity : (0:ℝ) ≤ b ^ 2 * α)
    linarith [h2]
  linarith [h1, hN2]

theorem rho2_bound (b μ q : ℝ) (hμ : 16 ≤ μ) (hb : μ / Real.sqrt 2 ≤ b) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : |q - pOf b q / FOf b| ≤ 100 / (μ * Real.sqrt μ) := by
  have hμpos : 0 < μ := by linarith
  have hb0 : 0 < b := by
    have h : 0 < μ / Real.sqrt 2 := by positivity
    linarith
  have hb1 : 1 ≤ b := by
    have h1 : (1:ℝ) ≤ μ / Real.sqrt 2 := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, hμ]
    linarith
  have hb4 : μ ^ 4 / 4 ≤ b ^ 4 := fourth_lower b μ hμ hb
  have hp1 : pOf b q / FOf b - q = (b ^ 2)⁻¹ * (1 - 2 * q) / (b ^ 2 + (b ^ 2)⁻¹) := by
    rw [pOf, FOf]
    field_simp <;> ring
  have h2q : |1 - 2 * q| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hnum2 : |(b ^ 2)⁻¹ * (1 - 2 * q)| ≤ (b ^ 2)⁻¹ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (b^2)⁻¹)]
    calc (b ^ 2)⁻¹ * |1 - 2 * q| ≤ (b ^ 2)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h2q (by positivity)
      _ = (b ^ 2)⁻¹ := by ring
  have h3 : (b ^ 2)⁻¹ / (b ^ 2 + (b ^ 2)⁻¹) ≤ 1 / b ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h : (b ^ 2)⁻¹ * b ^ 4 = b ^ 2 := by
      have hbne : b ≠ 0 := ne_of_gt hb0
      field_simp <;> ring
    have hb2i : 0 < (b ^ 2)⁻¹ := by positivity
    nlinarith [h, hb2i]
  have h4 : 1 / b ^ 4 ≤ 100 / (μ * Real.sqrt μ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h5 : μ * Real.sqrt μ ≤ 100 * (μ ^ 4/4) := by
      have h := mu_sqrt_le μ hμ
      calc μ * Real.sqrt μ ≤ μ ^ 3 / 16 := h
        _ ≤ 100 * (μ ^ 4 / 4) := by
          have h1 : (1:ℝ) ≤ 200 * μ := by linarith
          have h2 : 0 ≤ μ ^ 3 / 16 := le_of_lt (by positivity)
          have h3 := mul_le_mul_of_nonneg_left h1 h2
          nlinarith [h3]
    have h6 : 100 * (μ ^ 4 / 4) ≤ 100 * b ^ 4 := mul_le_mul_of_nonneg_left hb4 (by norm_num)
    nlinarith [h5, h6]
  have hq1 : q - pOf b q / FOf b = -((b ^ 2)⁻¹ * (1 - 2 * q) / (b ^ 2 + (b ^ 2)⁻¹)) := by
    linarith [hp1]
  rw [hq1, abs_neg, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ b ^ 2 + (b ^ 2)⁻¹)]
  calc |(b ^ 2)⁻¹ * (1 - 2 * q)| / (b ^ 2 + (b ^ 2)⁻¹) ≤ (b ^ 2)⁻¹ / (b ^ 2 + (b ^ 2)⁻¹) :=
        div_le_div_of_nonneg_right hnum2 (by positivity)
    _ ≤ 1 / b ^ 4 := h3
    _ ≤ 100 / (μ * Real.sqrt μ) := h4

set_option maxHeartbeats 2000000 in
theorem core_ineq (a b c μ q α : ℝ) (u0 u1 : ℂ)
    (hμ : 10 ^ 6 ≤ μ)
    (hb : μ / Real.sqrt 2 ≤ b) (hc : μ / Real.sqrt 2 ≤ c) (ha : μ / Real.sqrt 2 ≤ a)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hα : 1 / (4 * μ) ≤ α)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hu0 : |‖u0‖ ^ 2 - (b ^ 2 * q * α + (b ^ 2)⁻¹ * (1 - q) * (1 - α))|
      ≤ 2 * Real.sqrt (q * α * (1 - q) * (1 - α)))
    (hu1 : |‖u1‖ ^ 2 - (b ^ 2 * q * (1 - α) + (b ^ 2)⁻¹ * (1 - q) * α)|
      ≤ 2 * Real.sqrt (q * (1 - α) * (1 - q) * α)) :
    |Phi a (c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2) (FZ b c α)
      - Phi a (pOf b q) (FOf b)| ≤ 500 / (μ * Real.sqrt μ) := by
  have hμpos : (0:ℝ) < μ := by linarith
  have hμ1 : (1:ℝ) ≤ μ := by linarith
  have hspos : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμpos
  have hsqμ : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμpos.le
  have hαpos : 0 < α := by
    have h : 0 < 1/(4*μ) := by positivity
    linarith
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity : 0 < μ / Real.sqrt 2) hb
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity : 0 < μ / Real.sqrt 2) hc
  have h1μ : (1:ℝ) ≤ μ / Real.sqrt 2 := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, hμ1]
  have ha1 : 1 ≤ a := le_trans h1μ ha
  have hb1 : 1 ≤ b := le_trans h1μ hb
  have hc1 : 1 ≤ c := le_trans h1μ hc
  have hb2m : μ ^ 2 / 2 ≤ b ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ μ / Real.sqrt 2) hb 2
    rwa [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h
  have hc2m : μ ^ 2 / 2 ≤ c ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ μ / Real.sqrt 2) hc 2
    rwa [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h
  have hb4 : μ ^ 4 / 4 ≤ b ^ 4 := by
    have h := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ μ^2/2) hb2m
    calc μ^4/4 = (μ^2/2)*(μ^2/2) := by ring
      _ ≤ b^2 * b^2 := h
      _ = b^4 := by ring
  set δ : ℝ := Real.sqrt (q * α * (1 - q) * (1 - α)) with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hδ2 : δ ^ 2 = q * α * (1 - q) * (1 - α) := by rw [hδdef, Real.sq_sqrt (by positivity)]
  have hδle : 4 * δ ^ 2 ≤ α := by
    rw [hδ2]
    have h1 : 4 * q * (1 - q) ≤ 1 := by nlinarith [sq_nonneg (2*q - 1)]
    have h3 : 0 ≤ 1 - α := by linarith
    have h4 : 4 * q * (1 - q) * (1 - α) ≤ 1 * 1 := mul_le_mul h1 (by linarith : 1 - α ≤ 1) h3 (by norm_num)
    nlinarith [h4, hα0]
  have hδhalf : 2 * δ ≤ Real.sqrt α := by
    have h1 : (2*δ)^2 ≤ (Real.sqrt α)^2 := by
      rw [mul_pow, Real.sq_sqrt hα0]; linarith
    calc 2*δ = Real.sqrt ((2*δ)^2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((Real.sqrt α)^2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt α := Real.sqrt_sq (Real.sqrt_nonneg α)
  set X0 : ℝ := ‖u0‖ ^ 2 - (b ^ 2 * q * α + (b ^ 2)⁻¹ * (1 - q) * (1 - α)) with hX0def
  set X1 : ℝ := ‖u1‖ ^ 2 - (b ^ 2 * q * (1 - α) + (b ^ 2)⁻¹ * (1 - q) * α) with hX1def
  have hU0 : ‖u0‖ ^ 2 = b ^ 2 * q * α + (b ^ 2)⁻¹ * (1 - q) * (1 - α) + X0 := by
    rw [hX0def]; ring
  have hU1 : ‖u1‖ ^ 2 = b ^ 2 * q * (1 - α) + (b ^ 2)⁻¹ * (1 - q) * α + X1 := by
    rw [hX1def]; ring
  have hX0b : |X0| ≤ 2 * δ := by rw [hX0def, hδdef]; exact hu0
  have hX1b : |X1| ≤ 2 * δ := by
    rw [hX1def, hδdef]
    have heq : Real.sqrt (q * α * (1 - q) * (1 - α)) = Real.sqrt (q * (1 - α) * (1 - q) * α) := by
      congr 1; ring
    rw [heq]; exact hu1
  have hnum : |c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2 - q * FZ b c α|
      ≤ c ^ 2 * (b ^ 2)⁻¹ + 2 * c ^ 2 * δ + 1 + 2 * δ := by
    have hid : c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2 - q * FZ b c α
        = c ^ 2 * (b ^ 2)⁻¹ * (1 - α) * (1 - 2 * q) + c ^ 2 * X0
          + (c ^ 2)⁻¹ * (b ^ 2)⁻¹ * α * (1 - 2 * q) + (c ^ 2)⁻¹ * X1 := by
      rw [hU0, hU1, FZ]; ring
    rw [hid]
    have h1α : 0 ≤ 1 - α := by linarith
    have h2q : |1 - 2 * q| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have hT1 : |c ^ 2 * (b ^ 2)⁻¹ * (1 - α) * (1 - 2 * q)| ≤ c ^ 2 * (b ^ 2)⁻¹ := by
      have hprod : (1 - α) * |1 - 2 * q| ≤ 1 := by
        nlinarith [h1α, hα1, h2q, abs_nonneg (1 - 2*q)]
      calc |c ^ 2 * (b ^ 2)⁻¹ * (1 - α) * (1 - 2 * q)|
          = c ^ 2 * (b ^ 2)⁻¹ * ((1 - α) * |1 - 2 * q|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity),
              abs_of_nonneg (by positivity), abs_of_nonneg h1α]
            ring
        _ ≤ c ^ 2 * (b ^ 2)⁻¹ * 1 := mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = c ^ 2 * (b ^ 2)⁻¹ := by ring
    have hT2 : |c ^ 2 * X0| ≤ 2 * c ^ 2 * δ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c ^ 2)]
      calc c ^ 2 * |X0| ≤ c ^ 2 * (2 * δ) := mul_le_mul_of_nonneg_left hX0b (by positivity)
        _ = 2 * c ^ 2 * δ := by ring
    have hA : |(c ^ 2)⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), inv_le_one₀ (by positivity)]
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hc1 2
    have hB : |(b ^ 2)⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), inv_le_one₀ (by positivity)]
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hb1 2
    have hT3 : |(c ^ 2)⁻¹ * (b ^ 2)⁻¹ * α * (1 - 2 * q)| ≤ 1 := by
      have hprod : α * |1 - 2 * q| ≤ 1 := by nlinarith [hα0, hα1, h2q, abs_nonneg (1 - 2*q)]
      calc |(c ^ 2)⁻¹ * (b ^ 2)⁻¹ * α * (1 - 2 * q)|
          = |(c ^ 2)⁻¹| * |(b ^ 2)⁻¹| * (α * |1 - 2 * q|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hα0]; ring
        _ ≤ 1 * 1 * 1 := by
            exact mul_le_mul (mul_le_mul hA hB (abs_nonneg _) (by norm_num)) hprod (by positivity) (by norm_num)
        _ = 1 := by ring
    have hT4 : |(c ^ 2)⁻¹ * X1| ≤ 2 * δ := by
      rw [abs_mul]
      calc |(c ^ 2)⁻¹| * |X1| ≤ 1 * (2 * δ) := mul_le_mul hA hX1b (abs_nonneg _) (by norm_num)
        _ = 2 * δ := by ring
    calc |c ^ 2 * (b ^ 2)⁻¹ * (1 - α) * (1 - 2 * q) + c ^ 2 * X0
            + (c ^ 2)⁻¹ * (b ^ 2)⁻¹ * α * (1 - 2 * q) + (c ^ 2)⁻¹ * X1|
        ≤ |c ^ 2 * (b ^ 2)⁻¹ * (1 - α) * (1 - 2 * q)| + |c ^ 2 * X0|
          + |(c ^ 2)⁻¹ * (b ^ 2)⁻¹ * α * (1 - 2 * q)| + |(c ^ 2)⁻¹ * X1| := by
          have h1 := abs_add_le (c ^ 2 * (b ^ 2)⁻¹ * (1 - α) * (1 - 2 * q) + c ^ 2 * X0
            + (c ^ 2)⁻¹ * (b ^ 2)⁻¹ * α * (1 - 2 * q)) ((c ^ 2)⁻¹ * X1)
          have h2 := abs_add_le (c ^ 2 * (b ^ 2)⁻¹ * (1 - α) * (1 - 2 * q) + c ^ 2 * X0)
            ((c ^ 2)⁻¹ * (b ^ 2)⁻¹ * α * (1 - 2 * q))
          have h3 := abs_add_le (c ^ 2 * (b ^ 2)⁻¹ * (1 - α) * (1 - 2 * q)) (c ^ 2 * X0)
          linarith
      _ ≤ c ^ 2 * (b ^ 2)⁻¹ + 2 * c ^ 2 * δ + 1 + 2 * δ := by linarith [hT1, hT2, hT3, hT4]
  have hFz_ge : b ^ 2 * c ^ 2 * α ≤ FZ b c α := by
    have h1α : 0 ≤ 1 - α := by linarith
    have h1 : 0 ≤ b ^ 2 * (c ^ 2)⁻¹ * (1 - α) := by positivity
    have h2 : 0 ≤ (b ^ 2)⁻¹ * c ^ 2 * (1 - α) := by positivity
    have h3 : 0 ≤ (b ^ 2)⁻¹ * (c ^ 2)⁻¹ * α := by positivity
    rw [FZ]; linarith
  have hFz_pos : 0 < FZ b c α := lt_of_lt_of_le (by positivity) hFz_ge
  have hF1_pos : 0 < FOf b := by rw [FOf]; positivity
  have hdiv : |(c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2 - q * FZ b c α) / FZ b c α|
      ≤ (c ^ 2 * (b ^ 2)⁻¹ + 2 * c ^ 2 * δ + 1 + 2 * δ) / (b ^ 2 * c ^ 2 * α) := by
    have hden : 0 < b ^ 2 * c ^ 2 * α := by positivity
    rw [abs_div, abs_of_pos hFz_pos]
    calc |c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2 - q * FZ b c α| / FZ b c α
        ≤ (c ^ 2 * (b ^ 2)⁻¹ + 2 * c ^ 2 * δ + 1 + 2 * δ) / FZ b c α :=
          div_le_div_of_nonneg_right hnum hFz_pos.le
      _ ≤ (c ^ 2 * (b ^ 2)⁻¹ + 2 * c ^ 2 * δ + 1 + 2 * δ) / (b ^ 2 * c ^ 2 * α) :=
          div_le_div_of_nonneg_left (by positivity) hden hFz_ge
  have hsplit : (c ^ 2 * (b ^ 2)⁻¹ + 2 * c ^ 2 * δ + 1 + 2 * δ) / (b ^ 2 * c ^ 2 * α)
      = 1/(b^4*α) + 2*δ/(b^2*α) + 1/(b^2*c^2*α) + 2*δ/(b^2*c^2*α) := by
    field_simp <;> ring
  have hN1 : 1 / (b ^ 4 * α) ≤ 100 / (μ * Real.sqrt μ) :=
    n1_bound b μ α (by linarith) hb hα
  have hN2 : 2 * δ / (b ^ 2 * α) ≤ 100 / (μ * Real.sqrt μ) :=
    n2_bound b μ α δ (by linarith) hb hα hδhalf
  have hN3 : 1 / (b ^ 2 * c ^ 2 * α) ≤ 100 / (μ * Real.sqrt μ) :=
    n3_bound b c μ α (by linarith) hb hc hα
  have hN4 : 2 * δ / (b ^ 2 * c ^ 2 * α) ≤ 100 / (μ * Real.sqrt μ) :=
    n4_bound b c μ α δ (by linarith) hb hc hα hc1 hδ0 hN2
  have hρ2 : |q - pOf b q / FOf b| ≤ 100 / (μ * Real.sqrt μ) :=
    rho2_bound b μ q (by linarith) hb hq0 hq1
  have hρ : |(c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2) / FZ b c α - pOf b q / FOf b|
      ≤ 500 / (μ * Real.sqrt μ) := by
    have hdecomp : (c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2) / FZ b c α - pOf b q / FOf b
        = (c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2 - q * FZ b c α) / FZ b c α
          + (q - pOf b q / FOf b) := by
      field_simp <;> ring
    rw [hdecomp]
    have hsum : |(c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2 - q * FZ b c α) / FZ b c α|
        + |q - pOf b q / FOf b| ≤ 500 / (μ * Real.sqrt μ) := by
      have hs : |(c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2 - q * FZ b c α) / FZ b c α|
          ≤ 400 / (μ * Real.sqrt μ) := by
        calc |(c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2 - q * FZ b c α) / FZ b c α|
            ≤ (c ^ 2 * (b ^ 2)⁻¹ + 2 * c ^ 2 * δ + 1 + 2 * δ) / (b ^ 2 * c ^ 2 * α) := hdiv
          _ = 1/(b^4*α) + 2*δ/(b^2*α) + 1/(b^2*c^2*α) + 2*δ/(b^2*c^2*α) := hsplit
          _ ≤ 100 / (μ * Real.sqrt μ) + 100 / (μ * Real.sqrt μ)
                + 100 / (μ * Real.sqrt μ) + 100 / (μ * Real.sqrt μ) := by
              linarith [hN1, hN2, hN3, hN4]
          _ = 400 / (μ * Real.sqrt μ) := by ring
      have h := add_le_add hs hρ2
      have h2 : 400 / (μ * Real.sqrt μ) + 100 / (μ * Real.sqrt μ) = 500 / (μ * Real.sqrt μ) := by
        rw [← add_div]; norm_num
      linarith [h, h2]
    calc |(c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2 - q * FZ b c α) / FZ b c α
            + (q - pOf b q / FOf b)|
        ≤ |(c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2 - q * FZ b c α) / FZ b c α|
          + |q - pOf b q / FOf b| := abs_add_le _ _
      _ ≤ 500 / (μ * Real.sqrt μ) := hsum
  calc |Phi a (c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2) (FZ b c α) - Phi a (pOf b q) (FOf b)|
      ≤ |(c ^ 2 * ‖u0‖ ^ 2 + (c ^ 2)⁻¹ * ‖u1‖ ^ 2) / FZ b c α - pOf b q / FOf b| :=
        Phi_sub_le a _ (FZ b c α) _ (FOf b) hFz_pos hF1_pos ha1
    _ ≤ 500 / (μ * Real.sqrt μ) := hρ

end Work.TMC7Core.Scale

namespace Work.TMC7Core.Scale

theorem ratio_bound' (b c : ℝ) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    b ^ 4 + c ^ 4 ≤ ((b ^ 4)⁻¹ + (c ^ 4)⁻¹) * ((b ^ 4 + 1) * (c ^ 4 + 1)) := by
  have hb4 : 0 < b ^ 4 := by positivity
  have hc4 : 0 < c ^ 4 := by positivity
  have hbc : b ^ 4 * c ^ 4 ≤ (b ^ 4 + 1) * (c ^ 4 + 1) := by nlinarith [hb4, hc4]
  have h2 : ((b ^ 4)⁻¹ + (c ^ 4)⁻¹) * (b ^ 4 * c ^ 4) = b ^ 4 + c ^ 4 := by
    field_simp <;> ring
  rw [← h2]
  have h3 : 0 ≤ (b ^ 4)⁻¹ + (c ^ 4)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left hbc h3

theorem alpha_lower (b c αV μ : ℝ) (hμ : 16 ≤ μ) (hb : μ / Real.sqrt 2 ≤ b)
    (hc : μ / Real.sqrt 2 ≤ c) (hαV0 : 0 ≤ αV) (hαV1 : αV ≤ 1)
    (h : 1 / (2 * μ) ≤
      (αV * (b ^ 4 * c ^ 4 + 1) + (1 - αV) * (b ^ 4 + c ^ 4)) / ((b ^ 4 + 1) * (c ^ 4 + 1))) :
    1 / (4 * μ) ≤ αV := by
  have hμpos : 0 < μ := by linarith
  have hb1 : 1 ≤ b := by
    have h : (1:ℝ) ≤ μ / Real.sqrt 2 := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, hμ]
    linarith
  have hc1 : 1 ≤ c := by
    have h : (1:ℝ) ≤ μ / Real.sqrt 2 := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, hμ]
    linarith
  have hden : 0 < (b ^ 4 + 1) * (c ^ 4 + 1) := by positivity
  have hbound : (αV * (b ^ 4 * c ^ 4 + 1) + (1 - αV) * (b ^ 4 + c ^ 4)) / ((b ^ 4 + 1) * (c ^ 4 + 1))
      ≤ αV + ((b ^ 4)⁻¹ + (c ^ 4)⁻¹) := by
    rw [div_le_iff₀ hden]
    have hA : αV * (b ^ 4 * c ^ 4 + 1) ≤ αV * ((b ^ 4 + 1) * (c ^ 4 + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hαV0
      nlinarith [show (0:ℝ) ≤ b ^ 4 by positivity, show (0:ℝ) ≤ c ^ 4 by positivity]
    have hB : (1 - αV) * (b ^ 4 + c ^ 4) ≤ ((b ^ 4)⁻¹ + (c ^ 4)⁻¹) * ((b ^ 4 + 1) * (c ^ 4 + 1)) := by
      have h1 : 1 - αV ≤ 1 := by linarith
      have h2 : (1 - αV) * (b ^ 4 + c ^ 4) ≤ 1 * (b ^ 4 + c ^ 4) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 := ratio_bound' b c hb1 hc1
      nlinarith [h2, h3]
    nlinarith [hA, hB]
  have hsmall : (b ^ 4)⁻¹ + (c ^ 4)⁻¹ ≤ 1 / (4 * μ) := by
    have hb4 : μ ^ 4 / 4 ≤ b ^ 4 := fourth_lower b μ hμ hb
    have hc4 : μ ^ 4 / 4 ≤ c ^ 4 := fourth_lower c μ hμ hc
    have hb4p : 0 < μ ^ 4 / 4 := by positivity
    have h1 : (b ^ 4)⁻¹ ≤ 4 / μ ^ 4 := by
      have h := (inv_le_inv₀ (by positivity : (0:ℝ) < b^4) hb4p).mpr hb4
      rwa [inv_div] at h
    have h2 : (c ^ 4)⁻¹ ≤ 4 / μ ^ 4 := by
      have h := (inv_le_inv₀ (by positivity : (0:ℝ) < c^4) hb4p).mpr hc4
      rwa [inv_div] at h
    have h3 : 4 / μ ^ 4 + 4 / μ ^ 4 ≤ 1 / (4 * μ) := by
      have h4 : 4 / μ ^ 4 + 4 / μ ^ 4 = 8 / μ ^ 4 := by ring
      have hμ3 : (32:ℝ) ≤ μ ^ 3 := by nlinarith [hμ, sq_nonneg (μ - 16)]
      rw [h4, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hμ3, hμpos]
    linarith [h1, h2, h3]
  have hrel : 1 / (2 * μ) - 1 / (4 * μ) = 1 / (4 * μ) := by
    field_simp <;> ring
  linarith [h, hbound, hsmall, hrel]

end Work.TMC7Core.Scale

namespace Work.TMC7Core.Scale

theorem div_sqrt2_le_of_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ 2 / 2 ≤ y ^ 2) :
    x / Real.sqrt 2 ≤ y := by
  have h3 : x / Real.sqrt 2 = Real.sqrt (x ^ 2 / 2) := by
    rw [show x ^ 2 / 2 = (x / Real.sqrt 2)^2 by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]]
    exact (Real.sqrt_sq (by positivity)).symm
  rw [h3]
  calc Real.sqrt (x^2/2) ≤ Real.sqrt (y^2) := Real.sqrt_le_sqrt h
    _ = y := Real.sqrt_sq hy

set_option maxHeartbeats 2000000 in
theorem rift_prod_le (W X M : Matrix (Fin 2) (Fin 2) ℂ) (μ : ℝ)
    (hW : W.det = 1) (hX : X.det = 1) (hM : M.det = 1)
    (hμ : 10 ^ 6 ≤ μ)
    (hWμ : μ ≤ frob W) (hXμ : μ ≤ frob X) (hMμ : μ ≤ frob M)
    (hα : 1 / (2 * μ) ≤ rift X M ^ 2) :
    |rift W (X * M) ^ 2 - rift W X ^ 2| ≤ 500 / (μ * Real.sqrt μ) := by
  have hμpos : (0:ℝ) < μ := by linarith
  have hμ16 : (16:ℝ) ≤ μ := by linarith
  have hμ1 : (1:ℝ) ≤ μ := by linarith
  obtain ⟨Uw, Vw, a, hUw1, hUw2, hVw1, hVw2, ha1, hWs⟩ := Work.TMC7Core.Avalanche.svd_ge_one W hW
  obtain ⟨Ux, Vx, b, hUx1, hUx2, hVx1, hVx2, hb1, hXs⟩ := Work.TMC7Core.Avalanche.svd_ge_one X hX
  obtain ⟨Um, Vm, c, hUm1, hUm2, hVm1, hVm2, hc1, hMs⟩ := Work.TMC7Core.Avalanche.svd_ge_one M hM
  have hbpos : 0 < b := by linarith
  have hcpos : 0 < c := by linarith
  have hVw' : Vwᴴ * (Vwᴴ)ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hVw1
  have hVx' : Vxᴴ * (Vxᴴ)ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hVx1
  have hVm' : Vmᴴ * (Vmᴴ)ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hVm1
  -- T = Vwᴴ Ux, R = Vxᴴ Um are unitary
  have hT1 : (Vwᴴ * Ux)ᴴ * (Vwᴴ * Ux) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Uxᴴ * Vw * (Vwᴴ * Ux) = Uxᴴ * (Vw * Vwᴴ) * Ux := by noncomm_ring
      _ = 1 := by rw [hVw2, mul_one, hUx1]
  have hT2 : (Vwᴴ * Ux) * (Vwᴴ * Ux)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Vwᴴ * Ux * (Uxᴴ * Vw) = Vwᴴ * (Ux * Uxᴴ) * Vw := by noncomm_ring
      _ = 1 := by rw [hUx2, mul_one, hVw1]
  have hR1 : (Vxᴴ * Um)ᴴ * (Vxᴴ * Um) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Umᴴ * Vx * (Vxᴴ * Um) = Umᴴ * (Vx * Vxᴴ) * Um := by noncomm_ring
      _ = 1 := by rw [hVx2, mul_one, hUm1]
  have hR2 : (Vxᴴ * Um) * (Vxᴴ * Um)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Vxᴴ * Um * (Umᴴ * Vx) = Vxᴴ * (Um * Umᴴ) * Vx := by noncomm_ring
      _ = 1 := by rw [hUm2, mul_one, hVx1]
  -- the matrix factorisations
  have hXM : X * M = Ux * (Dg b * (Vxᴴ * Um) * Dg c) * Vmᴴ := by
    rw [hXs, hMs]; noncomm_ring
  have hWX : W * X = Uw * (Dg a * ((Vwᴴ * Ux) * Dg b)) * Vxᴴ := by
    rw [hWs, hXs]; noncomm_ring
  have hWXM : W * (X * M) =
      Uw * (Dg a * ((Vwᴴ * Ux) * Dg b * (Vxᴴ * Um) * Dg c)) * Vmᴴ := by
    rw [hWs, hXs, hMs]; noncomm_ring
  have hfW : frob W ^ 2 = FOf a := by
    rw [hWs]
    rw [Work.TMC7Core.Avalanche.frob_mul_of_unitary (Uw * Dg a) Vwᴴ hVw']
    rw [Work.TMC7Core.Avalanche.frob_mul_unitary Uw (Dg a) hUw1]
    exact frob_Dg_sq a
  have hfX : frob X ^ 2 = FOf b := by
    rw [hXs]
    rw [Work.TMC7Core.Avalanche.frob_mul_of_unitary (Ux * Dg b) Vxᴴ hVx']
    rw [Work.TMC7Core.Avalanche.frob_mul_unitary Ux (Dg b) hUx1]
    exact frob_Dg_sq b
  have hfM : frob M ^ 2 = FOf c := by
    rw [hMs]
    rw [Work.TMC7Core.Avalanche.frob_mul_of_unitary (Um * Dg c) Vmᴴ hVm']
    rw [Work.TMC7Core.Avalanche.frob_mul_unitary Um (Dg c) hUm1]
    exact frob_Dg_sq c
  have hfXM : frob (X * M) ^ 2 = FZ b c (‖(Vxᴴ * Um) 0 0‖ ^ 2) := by
    rw [hXM]
    rw [Work.TMC7Core.Avalanche.frob_mul_of_unitary (Ux * (Dg b * (Vxᴴ * Um) * Dg c)) Vmᴴ hVm']
    rw [Work.TMC7Core.Avalanche.frob_mul_unitary Ux (Dg b * (Vxᴴ * Um) * Dg c) hUx1]
    exact frob_Dg_mul_Dg_sq b c (Vxᴴ * Um) hR1 hR2
  have hfrTDb : frob ((Vwᴴ * Ux) * Dg b) ^ 2 = FOf b := by
    rw [Work.TMC7Core.Avalanche.frob_mul_unitary (Vwᴴ * Ux) (Dg b) hT1]
    exact frob_Dg_sq b
  have hrowX : ‖((Vwᴴ * Ux) * Dg b) 0 0‖ ^ 2 + ‖((Vwᴴ * Ux) * Dg b) 0 1‖ ^ 2
      = pOf b (‖(Vwᴴ * Ux) 0 0‖ ^ 2) := row_norm_Dg_sq b (Vwᴴ * Ux) hT2
  have hfWX : frob (W * X) ^ 2
      = a ^ 2 * pOf b (‖(Vwᴴ * Ux) 0 0‖ ^ 2)
        + (a ^ 2)⁻¹ * (FOf b - pOf b (‖(Vwᴴ * Ux) 0 0‖ ^ 2)) := by
    rw [hWX]
    rw [Work.TMC7Core.Avalanche.frob_mul_of_unitary (Uw * (Dg a * ((Vwᴴ * Ux) * Dg b))) Vxᴴ hVx']
    rw [Work.TMC7Core.Avalanche.frob_mul_unitary Uw (Dg a * ((Vwᴴ * Ux) * Dg b)) hUw1]
    rw [frob_Dg_mul_sq' a ((Vwᴴ * Ux) * Dg b), hrowX, hfrTDb]
  have hfTR : frob ((Vwᴴ * Ux) * Dg b * (Vxᴴ * Um) * Dg c) ^ 2 = FZ b c (‖(Vxᴴ * Um) 0 0‖ ^ 2) := by
    rw [show (Vwᴴ * Ux) * Dg b * (Vxᴴ * Um) * Dg c
        = (Vwᴴ * Ux) * (Dg b * (Vxᴴ * Um) * Dg c) from by noncomm_ring]
    rw [Work.TMC7Core.Avalanche.frob_mul_unitary (Vwᴴ * Ux) (Dg b * (Vxᴴ * Um) * Dg c) hT1]
    exact frob_Dg_mul_Dg_sq b c (Vxᴴ * Um) hR1 hR2
  have hrowXM : ‖((Vwᴴ * Ux) * Dg b * (Vxᴴ * Um) * Dg c) 0 0‖ ^ 2
      + ‖((Vwᴴ * Ux) * Dg b * (Vxᴴ * Um) * Dg c) 0 1‖ ^ 2
      = c ^ 2 * ‖((b : ℝ) : ℂ) * (Vwᴴ * Ux) 0 0 * (Vxᴴ * Um) 0 0
            + (((b⁻¹ : ℝ)) : ℂ) * (Vwᴴ * Ux) 0 1 * (Vxᴴ * Um) 1 0‖ ^ 2
        + (c ^ 2)⁻¹ * ‖((b : ℝ) : ℂ) * (Vwᴴ * Ux) 0 0 * (Vxᴴ * Um) 0 1
            + (((b⁻¹ : ℝ)) : ℂ) * (Vwᴴ * Ux) 0 1 * (Vxᴴ * Um) 1 1‖ ^ 2 :=
    row_norm_Dg_mul_Dg_sq b c (Vwᴴ * Ux) (Vxᴴ * Um)
  have hfWXM : frob (W * (X * M)) ^ 2
      = a ^ 2 * (c ^ 2 * ‖((b : ℝ) : ℂ) * (Vwᴴ * Ux) 0 0 * (Vxᴴ * Um) 0 0
              + (((b⁻¹ : ℝ)) : ℂ) * (Vwᴴ * Ux) 0 1 * (Vxᴴ * Um) 1 0‖ ^ 2
          + (c ^ 2)⁻¹ * ‖((b : ℝ) : ℂ) * (Vwᴴ * Ux) 0 0 * (Vxᴴ * Um) 0 1
              + (((b⁻¹ : ℝ)) : ℂ) * (Vwᴴ * Ux) 0 1 * (Vxᴴ * Um) 1 1‖ ^ 2)
        + (a ^ 2)⁻¹ * (FZ b c (‖(Vxᴴ * Um) 0 0‖ ^ 2)
            - (c ^ 2 * ‖((b : ℝ) : ℂ) * (Vwᴴ * Ux) 0 0 * (Vxᴴ * Um) 0 0
                + (((b⁻¹ : ℝ)) : ℂ) * (Vwᴴ * Ux) 0 1 * (Vxᴴ * Um) 1 0‖ ^ 2
              + (c ^ 2)⁻¹ * ‖((b : ℝ) : ℂ) * (Vwᴴ * Ux) 0 0 * (Vxᴴ * Um) 0 1
                + (((b⁻¹ : ℝ)) : ℂ) * (Vwᴴ * Ux) 0 1 * (Vxᴴ * Um) 1 1‖ ^ 2)) := by
    rw [hWXM]
    rw [Work.TMC7Core.Avalanche.frob_mul_of_unitary
      (Uw * (Dg a * ((Vwᴴ * Ux) * Dg b * (Vxᴴ * Um) * Dg c))) Vmᴴ hVm']
    rw [Work.TMC7Core.Avalanche.frob_mul_unitary
      Uw (Dg a * ((Vwᴴ * Ux) * Dg b * (Vxᴴ * Um) * Dg c)) hUw1]
    rw [frob_Dg_mul_sq' a ((Vwᴴ * Ux) * Dg b * (Vxᴴ * Um) * Dg c), hrowXM, hfTR]
  have hriftX : rift W X ^ 2 = Phi a (pOf b (‖(Vwᴴ * Ux) 0 0‖ ^ 2)) (FOf b) := by
    unfold rift
    rw [div_pow, mul_pow, hfWX, hfW, hfX]
    simp only [Phi, FOf]
  have hriftM : rift W (X * M) ^ 2
      = Phi a (c ^ 2 * ‖((b : ℝ) : ℂ) * (Vwᴴ * Ux) 0 0 * (Vxᴴ * Um) 0 0
              + (((b⁻¹ : ℝ)) : ℂ) * (Vwᴴ * Ux) 0 1 * (Vxᴴ * Um) 1 0‖ ^ 2
          + (c ^ 2)⁻¹ * ‖((b : ℝ) : ℂ) * (Vwᴴ * Ux) 0 0 * (Vxᴴ * Um) 0 1
              + (((b⁻¹ : ℝ)) : ℂ) * (Vwᴴ * Ux) 0 1 * (Vxᴴ * Um) 1 1‖ ^ 2)
        (FZ b c (‖(Vxᴴ * Um) 0 0‖ ^ 2)) := by
    unfold rift
    rw [div_pow, mul_pow, hfWXM, hfW, hfXM]
    simp only [Phi, FOf, FZ]
  have hb2 : μ / Real.sqrt 2 ≤ b := by
    have h1 : μ ^ 2 ≤ FOf b := by
      have h2 : μ ^ 2 ≤ frob X ^ 2 := pow_le_pow_left₀ (by linarith) hXμ 2
      rw [hfX] at h2
      exact h2
    have h3 : (b ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      nlinarith [hb1]
    have h3' : (1:ℝ) ≤ b ^ 2 := by nlinarith [hb1]
    have h4 : FOf b ≤ 2 * b ^ 2 := by rw [FOf]; linarith
    have h5 : μ ^ 2 / 2 ≤ b ^ 2 := by linarith
    exact div_sqrt2_le_of_sq (by linarith) (by linarith) h5
  have hc2 : μ / Real.sqrt 2 ≤ c := by
    have h1 : μ ^ 2 ≤ FOf c := by
      have h2 : μ ^ 2 ≤ frob M ^ 2 := pow_le_pow_left₀ (by linarith) hMμ 2
      rw [hfM] at h2
      exact h2
    have h3 : (c ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      nlinarith [hc1]
    have h3' : (1:ℝ) ≤ c ^ 2 := by nlinarith [hc1]
    have h4 : FOf c ≤ 2 * c ^ 2 := by rw [FOf]; linarith
    have h5 : μ ^ 2 / 2 ≤ c ^ 2 := by linarith
    exact div_sqrt2_le_of_sq (by linarith) (by linarith) h5
  have ha2 : μ / Real.sqrt 2 ≤ a := by
    have h1 : μ ^ 2 ≤ FOf a := by
      have h2 : μ ^ 2 ≤ frob W ^ 2 := pow_le_pow_left₀ (by linarith) hWμ 2
      rw [hfW] at h2
      exact h2
    have h3 : (a ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      nlinarith [ha1]
    have h3' : (1:ℝ) ≤ a ^ 2 := by nlinarith [ha1]
    have h4 : FOf a ≤ 2 * a ^ 2 := by rw [FOf]; linarith
    have h5 : μ ^ 2 / 2 ≤ a ^ 2 := by linarith
    exact div_sqrt2_le_of_sq (by linarith) (by linarith) h5
  have hq0 : 0 ≤ ‖(Vwᴴ * Ux) 0 0‖ ^ 2 := sq_nonneg _
  have hq1 : ‖(Vwᴴ * Ux) 0 0‖ ^ 2 ≤ 1 := by
    have h := row_norm_sq_eq_one (Vwᴴ * Ux) hT2 0
    have h2 : 0 ≤ ‖(Vwᴴ * Ux) 0 1‖ ^ 2 := sq_nonneg _
    linarith
  have hα0 : 0 ≤ ‖(Vxᴴ * Um) 0 0‖ ^ 2 := sq_nonneg _
  obtain ⟨hUe11, hUe01, hUe10⟩ := Work.TMC7Core.Avalanche.unitary_entries (Vxᴴ * Um) hR1 hR2
  have hα1 : ‖(Vxᴴ * Um) 0 0‖ ^ 2 ≤ 1 := by
    have h2 : 0 ≤ ‖(Vxᴴ * Um) 0 1‖ ^ 2 := sq_nonneg _
    linarith [hUe01]
  have hα4 : 1 / (4 * μ) ≤ ‖(Vxᴴ * Um) 0 0‖ ^ 2 := by
    refine alpha_lower b c (‖(Vxᴴ * Um) 0 0‖ ^ 2) μ hμ16 hb2 hc2 hα0 hα1 ?_
    have hrf := Work.TMC7Core.Avalanche.rift_formula_svd X M Ux Vx Um Vm hUx1 hVx1 hUm1 hVm1
      hVx2 hUm2 hVm2 hbpos hcpos hXs hMs
    have hriftsq : rift X M ^ 2
        = (‖(Vxᴴ * Um) 0 0‖ ^ 2 * (b ^ 4 * c ^ 4 + 1)
            + (1 - ‖(Vxᴴ * Um) 0 0‖ ^ 2) * (b ^ 4 + c ^ 4)) / ((b ^ 4 + 1) * (c ^ 4 + 1)) := by
      unfold rift
      rw [div_pow, mul_pow]
      exact hrf
    rw [hriftsq] at hα
    exact hα
  have hub := u_bounds ((Vwᴴ * Ux) 0 0) ((Vwᴴ * Ux) 0 1) ((Vxᴴ * Um) 0 0) ((Vxᴴ * Um) 0 1)
      ((Vxᴴ * Um) 1 0) ((Vxᴴ * Um) 1 1) b (‖(Vwᴴ * Ux) 0 0‖ ^ 2) (‖(Vxᴴ * Um) 0 0‖ ^ 2)
      hbpos rfl (row_norm_sq_eq_one (Vwᴴ * Ux) hT2 0) rfl
      (row_norm_sq_eq_one (Vxᴴ * Um) hR2 0)
      (by rw [add_comm]; exact col_norm_sq_eq_one (Vxᴴ * Um) hR1 0)
      hUe11
  have hcore := core_ineq a b c μ (‖(Vwᴴ * Ux) 0 0‖ ^ 2) (‖(Vxᴴ * Um) 0 0‖ ^ 2)
      (((b : ℝ) : ℂ) * (Vwᴴ * Ux) 0 0 * (Vxᴴ * Um) 0 0
        + (((b⁻¹ : ℝ)) : ℂ) * (Vwᴴ * Ux) 0 1 * (Vxᴴ * Um) 1 0)
      (((b : ℝ) : ℂ) * (Vwᴴ * Ux) 0 0 * (Vxᴴ * Um) 0 1
        + (((b⁻¹ : ℝ)) : ℂ) * (Vwᴴ * Ux) 0 1 * (Vxᴴ * Um) 1 1)
      hμ hb2 hc2 ha2 hα0 hα1 hα4 hq0 hq1 hub.1 hub.2
  rw [hriftM, hriftX]
  exact hcore

end Work.TMC7Core.Scale

namespace Work.TMC7Core.Scale

theorem abs_log_sub_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    |Real.log a - Real.log b| ≤ |a - b| / min a b := by
  have hmin : 0 < min a b := lt_min ha hb
  rw [abs_le]
  constructor
  · have h1 : Real.log b - Real.log a ≤ |a - b| / min a b := by
      rw [← Real.log_div hb.ne' ha.ne']
      have h2 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have h3 : b / a - 1 = (b - a) / a := by
        field_simp <;> ring
      rw [h3] at h2
      rcases le_total a b with hle | hlt
      · rw [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub, min_eq_left hle]
        exact h2
      · have hnn : (b - a) / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt ha)
        have hpos : 0 ≤ |a - b| / min a b := div_nonneg (abs_nonneg _) (le_of_lt hmin)
        linarith
    linarith [h1]
  · have h1 : Real.log a - Real.log b ≤ |a - b| / min a b := by
      rw [← Real.log_div ha.ne' hb.ne']
      have h2 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have h3 : a / b - 1 = (a - b) / b := by
        field_simp <;> ring
      rw [h3] at h2
      rcases le_total b a with hle | hlt
      · rw [abs_of_nonneg (by linarith : 0 ≤ a - b), min_eq_right hle]
        exact h2
      · have hnn : (a - b) / b ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hb)
        have hpos : 0 ≤ |a - b| / min a b := div_nonneg (abs_nonneg _) (le_of_lt hmin)
        linarith
    exact h1

theorem one_div_sqrt_mu_le_rift (X Y : Matrix (Fin 2) (Fin 2) ℂ) (μ : ℝ)
    (hX : X.det = 1) (hY : Y.det = 1) (hμp : 0 < μ)
    (h : Real.log (frob X) + Real.log (frob Y) - Real.log (frob (X * Y)) ≤ Real.log μ / 2) :
    1 / Real.sqrt μ ≤ rift X Y := by
  have hXpos : 0 < frob X := Work.TMC7Core.Avalanche.frob_pos_of_det_one hX
  have hYpos : 0 < frob Y := Work.TMC7Core.Avalanche.frob_pos_of_det_one hY
  have hXYpos : 0 < frob (X * Y) := Work.TMC7Core.Avalanche.frob_pos_of_det_one (by rw [Matrix.det_mul, hX, hY, one_mul])
  have hrpos : 0 < rift X Y := div_pos hXYpos (by positivity)
  have hlog : Real.log (rift X Y)
      = -(Real.log (frob X) + Real.log (frob Y) - Real.log (frob (X * Y))) := by
    rw [rift, Real.log_div hXYpos.ne' (by positivity), Real.log_mul hXpos.ne' hYpos.ne']
    ring
  have hloginv : Real.log (1 / Real.sqrt μ) = -Real.log μ / 2 := by
    rw [Real.log_div one_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hμp)), Real.log_one,
      Real.log_sqrt (le_of_lt hμp)]
    ring
  have hle : Real.log (1 / Real.sqrt μ) ≤ Real.log (rift X Y) := by
    rw [hlog, hloginv]
    linarith
  calc 1 / Real.sqrt μ = Real.exp (Real.log (1 / Real.sqrt μ)) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (Real.log (rift X Y)) := Real.exp_le_exp.mpr hle
    _ = rift X Y := Real.exp_log hrpos

end Work.TMC7Core.Scale

namespace Work.TMC7Core.Scale

set_option maxHeartbeats 2000000 in
theorem avalanche_weak (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (m : ℕ) (μ : ℝ)
    (hdet : ∀ j, (A j).det = 1) (hm : 2 ≤ m) (hμ : 10 ^ 6 ≤ μ)
    (hnorm : ∀ j, Work.TMC7Core.frob (A j) ≥ μ)
    (hpair : ∀ j, j + 1 < m →
      Real.log (Work.TMC7Core.frob (A (j + 1))) + Real.log (Work.TMC7Core.frob (A j))
        - Real.log (Work.TMC7Core.frob (A (j + 1) * A j)) ≤ Real.log μ / 2) :
    |Real.log (Work.TMC7Core.frob (Work.TMC7Core.matProd A m))
      + ∑ j ∈ Finset.Icc 1 (m - 2), Real.log (Work.TMC7Core.frob (A j))
      - ∑ j ∈ Finset.range (m - 1), Real.log (Work.TMC7Core.frob (A (j + 1) * A j))|
      ≤ 1000 * (m : ℝ) / Real.sqrt μ := by
  have hμpos : (0:ℝ) < μ := by linarith
  have hμ1 : (1:ℝ) ≤ μ := by linarith
  have hpair_rift : ∀ j, j + 1 < m → 1 / Real.sqrt μ ≤ rift (A (j + 1)) (A j) := by
    intro j hj
    exact one_div_sqrt_mu_le_rift (A (j + 1)) (A j) μ (hdet (j + 1)) (hdet j) hμpos (hpair j hj)
  have hsq1 : ∀ (x : ℝ), 1 / Real.sqrt μ ≤ x → 1 / μ ≤ x ^ 2 := by
    intro x hx
    have h2 : (1 / Real.sqrt μ)^2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hx 2
    have h3 : (1 / Real.sqrt μ)^2 = 1 / μ := by
      rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hμpos)]
    linarith [h2, h3]
  have hsmall : 500 / (μ * Real.sqrt μ) ≤ 1 / (2 * μ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h10 : (1000:ℝ) ≤ Real.sqrt μ := by
      nlinarith [Real.sq_sqrt (le_of_lt hμpos), Real.sqrt_nonneg μ, hμ]
    nlinarith [h10, hμpos, Real.sqrt_nonneg μ]
  have key : ∀ k, k ≤ m - 1 → (1 ≤ k →
      (1 / (2 * μ) ≤ rift (A k) (matProd A k) ^ 2 ∧
       μ ≤ frob (matProd A k) ∧
       |rift (A k) (matProd A k) ^ 2 - rift (A k) (A (k - 1)) ^ 2|
         ≤ 500 / (μ * Real.sqrt μ))) := by
    intro k
    induction k with
    | zero => intro hkm h1; omega
    | succ k ih =>
      intro hkm h1k
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        have hP1 : matProd A 1 = A 0 := by rw [matProd_succ, matProd_zero, mul_one]
        have hp0 : 1 / Real.sqrt μ ≤ rift (A 1) (A 0) := hpair_rift 0 (by omega)
        refine ⟨?_, ?_, ?_⟩
        · rw [hP1]
          exact le_trans (by rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith :
            1 / (2 * μ) ≤ 1 / μ) (hsq1 _ hp0)
        · rw [hP1]; exact hnorm 0
        · rw [hP1, show (1:ℕ) - 1 = 0 from rfl, sub_self, abs_zero]
          positivity
      · have hkm' : k ≤ m - 1 := by omega
        obtain ⟨hii, hiii, hiv⟩ := ih hkm' hkpos
        have hPk1 : matProd A (k + 1) = A k * matProd A k := matProd_succ A k
        have hcore := rift_prod_le (A (k + 1)) (A k) (matProd A k) μ (hdet (k + 1)) (hdet k)
          (det_matProd A hdet k) hμ (hnorm (k + 1)) (hnorm k) hiii hii
        rw [← hPk1] at hcore
        have hp0 : 1 / Real.sqrt μ ≤ rift (A (k + 1)) (A k) := hpair_rift k (by omega)
        have hsq2 : 1 / μ ≤ rift (A (k + 1)) (A k) ^ 2 := hsq1 _ hp0
        have hfrob : μ ≤ frob (matProd A (k + 1)) := by
          rw [hPk1]
          have hr0 : 0 ≤ rift (A k) (matProd A k) := by
            rw [rift]
            exact div_nonneg (le_of_lt (Work.TMC7Core.Avalanche.frob_pos_of_det_one
              (by rw [Matrix.det_mul, hdet k, det_matProd A hdet k, one_mul])))
              (le_of_lt (mul_pos (Work.TMC7Core.Avalanche.frob_pos_of_det_one (hdet k))
                (Work.TMC7Core.Avalanche.frob_pos_of_det_one (det_matProd A hdet k))))
          have hrift_ge : Real.sqrt (1 / (2 * μ)) ≤ rift (A k) (matProd A k) := by
            rw [← Real.sqrt_sq hr0]
            exact Real.sqrt_le_sqrt hii
          have hval : frob (A k * matProd A k)
              = rift (A k) (matProd A k) * (frob (A k) * frob (matProd A k)) := by
            have hne : frob (A k) * frob (matProd A k) ≠ 0 :=
              (mul_pos (Work.TMC7Core.Avalanche.frob_pos_of_det_one (hdet k))
                (Work.TMC7Core.Avalanche.frob_pos_of_det_one (det_matProd A hdet k))).ne'
            rw [rift]
            exact (div_mul_cancel₀ _ hne).symm
          rw [hval]
          have h5 : Real.sqrt (1 / (2*μ)) * (μ * μ)
              ≤ rift (A k) (matProd A k) * (frob (A k) * frob (matProd A k)) := by
            apply mul_le_mul hrift_ge _ (mul_nonneg (le_of_lt hμpos) (le_of_lt hμpos)) hr0
            exact mul_le_mul (hnorm k) hiii (le_of_lt hμpos)
              (le_of_lt (Work.TMC7Core.Avalanche.frob_pos_of_det_one (hdet k)))
          have h7 : 1/μ ≤ Real.sqrt (1 / (2*μ)) := by
            have h8 : (1/μ)^2 ≤ (Real.sqrt (1/(2*μ)))^2 := by
              have h9 : (Real.sqrt (1/(2*μ)))^2 = 1/(2*μ) := Real.sq_sqrt (by positivity)
              have h10 : (1/μ)^2 = 1/μ^2 := by rw [div_pow, one_pow]
              rw [h9, h10, div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith [hμ, hμpos]
            calc 1/μ = Real.sqrt ((1/μ)^2) := (Real.sqrt_sq (by positivity)).symm
              _ ≤ Real.sqrt ((Real.sqrt (1/(2*μ)))^2) := Real.sqrt_le_sqrt h8
              _ = Real.sqrt (1/(2*μ)) := Real.sqrt_sq (by positivity)
          have h6 : μ ≤ Real.sqrt (1 / (2*μ)) * (μ * μ) := by
            have h9 : μ * (1/μ) = 1 := by field_simp
            calc μ = μ * (μ * (1/μ)) := by rw [h9]; ring
              _ ≤ μ * (μ * Real.sqrt (1/(2*μ))) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  exact mul_le_mul_of_nonneg_left h7 (by positivity)
              _ = Real.sqrt (1/(2*μ)) * (μ * μ) := by ring
          linarith [h5, h6]
        refine ⟨?_, hfrob, hcore⟩
        · have hle := (abs_le.mp hcore).1
          have hrel : 1 / μ - 1 / (2*μ) = 1 / (2*μ) := by field_simp <;> ring
          linarith [hle, hsq2, hsmall, hrel]
  have perTerm : ∀ k, 1 ≤ k → k ≤ m - 1 →
      |Real.log (rift (A k) (matProd A k)) - Real.log (rift (A k) (A (k - 1)))| ≤ 500 / Real.sqrt μ := by
    intro k hk1 hk2
    obtain ⟨hii, _, hiv⟩ := key k hk2 hk1
    have hp0 : 1 / Real.sqrt μ ≤ rift (A k) (A (k - 1)) := by
      have hm1 : (k - 1) + 1 < m := by omega
      have h := hpair_rift (k - 1) hm1
      rwa [show k - 1 + 1 = k from by omega] at h
    have hsq2 : 1 / μ ≤ rift (A k) (A (k - 1)) ^ 2 := hsq1 _ hp0
    have hpos1 : 0 < rift (A k) (matProd A k) :=
      div_pos (Work.TMC7Core.Avalanche.frob_pos_of_det_one
        (by rw [Matrix.det_mul, hdet k, det_matProd A hdet k, one_mul]))
        (mul_pos (Work.TMC7Core.Avalanche.frob_pos_of_det_one (hdet k))
          (Work.TMC7Core.Avalanche.frob_pos_of_det_one (det_matProd A hdet k)))
    have hpos2 : 0 < rift (A k) (A (k - 1)) :=
      div_pos (Work.TMC7Core.Avalanche.frob_pos_of_det_one
        (by rw [Matrix.det_mul, hdet k, hdet (k - 1), one_mul]))
        (mul_pos (Work.TMC7Core.Avalanche.frob_pos_of_det_one (hdet k))
          (Work.TMC7Core.Avalanche.frob_pos_of_det_one (hdet (k - 1))))
    have hlog := abs_log_sub_le (rift (A k) (matProd A k) ^ 2) (rift (A k) (A (k - 1)) ^ 2)
      (pow_pos hpos1 2) (pow_pos hpos2 2)
    have hhalf : 1 / (2*μ) ≤ 1/μ := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hmin : 1 / (2*μ) ≤ min (rift (A k) (matProd A k) ^ 2) (rift (A k) (A (k - 1)) ^ 2) :=
      le_min hii (le_trans hhalf hsq2)
    have hbound : |rift (A k) (matProd A k) ^ 2 - rift (A k) (A (k - 1)) ^ 2|
        / min (rift (A k) (matProd A k) ^ 2) (rift (A k) (A (k - 1)) ^ 2) ≤ 1000 / Real.sqrt μ := by
      have h1 : |rift (A k) (matProd A k) ^ 2 - rift (A k) (A (k - 1)) ^ 2|
          ≤ 500 / (μ * Real.sqrt μ) := hiv
      have h2 : (500 / (μ * Real.sqrt μ)) / (1/(2*μ)) ≤ 1000 / Real.sqrt μ := by
        have h3 : 500 / (μ * Real.sqrt μ) / (1/(2*μ)) = 1000 / Real.sqrt μ := by
          field_simp <;> ring
        linarith [h3]
      calc |rift (A k) (matProd A k) ^ 2 - rift (A k) (A (k - 1)) ^ 2|
            / min (rift (A k) (matProd A k) ^ 2) (rift (A k) (A (k - 1)) ^ 2)
          ≤ (500 / (μ * Real.sqrt μ))
            / min (rift (A k) (matProd A k) ^ 2) (rift (A k) (A (k - 1)) ^ 2) :=
            div_le_div_of_nonneg_right h1 (by positivity)
        _ ≤ (500 / (μ * Real.sqrt μ)) / (1/(2*μ)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hmin
        _ ≤ 1000 / Real.sqrt μ := h2
    have hlog2 : |Real.log (rift (A k) (matProd A k)^2) - Real.log (rift (A k) (A (k - 1))^2)|
        ≤ 1000 / Real.sqrt μ := le_trans hlog hbound
    rw [Real.log_pow (rift (A k) (matProd A k)) 2, Real.log_pow (rift (A k) (A (k - 1))) 2] at hlog2
    have heq : |2 * Real.log (rift (A k) (matProd A k)) - 2 * Real.log (rift (A k) (A (k - 1)))|
        = 2 * |Real.log (rift (A k) (matProd A k)) - Real.log (rift (A k) (A (k - 1)))| := by
      rw [← mul_sub, abs_mul, abs_two]
    have hlog3 : 2 * |Real.log (rift (A k) (matProd A k)) - Real.log (rift (A k) (A (k - 1)))| ≤ 1000 / Real.sqrt μ := by
      calc 2 * |Real.log (rift (A k) (matProd A k)) - Real.log (rift (A k) (A (k - 1)))|
          = |2 * Real.log (rift (A k) (matProd A k)) - 2 * Real.log (rift (A k) (A (k - 1)))| := by
            rw [← mul_sub, abs_mul, abs_two]
        _ ≤ 1000 / Real.sqrt μ := hlog2
    have hrel : 1000 / Real.sqrt μ = 2 * (500 / Real.sqrt μ) := by ring
    linarith [hlog3, hrel]
  have hass := Work.TMC7Core.Avalanche.assembly A m hm hdet
  simp only [Work.TMC7Core.Avalanche.bOf, Work.TMC7Core.Avalanche.cOf] at hass
  rw [hass]
  calc |∑ k ∈ Finset.Icc 1 (m - 1),
          (Work.TMC7Core.Avalanche.dOf A (k - 1) - Work.TMC7Core.Avalanche.dlOf A k)|
      ≤ ∑ k ∈ Finset.Icc 1 (m - 1),
          |Work.TMC7Core.Avalanche.dOf A (k - 1) - Work.TMC7Core.Avalanche.dlOf A k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 (m - 1), (500 / Real.sqrt μ) := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        rw [Work.TMC7Core.Avalanche.dOf_sub_dlOf_eq A k hk1]
        simp only [Work.TMC7Core.Avalanche.rift, rift]
        exact perTerm k hk1 hk2
    _ = ((Finset.Icc 1 (m - 1)).card : ℝ) * (500 / Real.sqrt μ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1000 * (m : ℝ) / Real.sqrt μ := by
        have hcard : (Finset.Icc 1 (m - 1)).card ≤ m := by
          rw [Nat.card_Icc]; omega
        have hcard' : ((Finset.Icc 1 (m - 1)).card : ℝ) ≤ (m : ℝ) := by exact_mod_cast hcard
        have hx0 : 0 ≤ (Real.sqrt μ)⁻¹ := by positivity
        have h3 : ((Finset.Icc 1 (m - 1)).card : ℝ) * (500 / Real.sqrt μ)
            = 500 * (((Finset.Icc 1 (m - 1)).card : ℝ) * (Real.sqrt μ)⁻¹) := by ring
        have h5 : ((Finset.Icc 1 (m - 1)).card : ℝ) * (Real.sqrt μ)⁻¹
            ≤ (m : ℝ) * (Real.sqrt μ)⁻¹ := mul_le_mul_of_nonneg_right hcard' hx0
        have h6 : 500 * (((Finset.Icc 1 (m - 1)).card : ℝ) * (Real.sqrt μ)⁻¹)
            ≤ 500 * ((m : ℝ) * (Real.sqrt μ)⁻¹) := mul_le_mul_of_nonneg_left h5 (by norm_num)
        have h7 : 500 * ((m : ℝ) * (Real.sqrt μ)⁻¹) ≤ 1000 * ((m : ℝ) * (Real.sqrt μ)⁻¹) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        calc ((Finset.Icc 1 (m - 1)).card : ℝ) * (500 / Real.sqrt μ)
            = 500 * (((Finset.Icc 1 (m - 1)).card : ℝ) * (Real.sqrt μ)⁻¹) := h3
          _ ≤ 500 * ((m : ℝ) * (Real.sqrt μ)⁻¹) := h6
          _ ≤ 1000 * ((m : ℝ) * (Real.sqrt μ)⁻¹) := h7
          _ = 1000 * (m : ℝ) / Real.sqrt μ := by rw [div_eq_mul_inv]; ring

end Work.TMC7Core.Scale
