import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1pairingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB.pinQCl_add_int` — additivity of the `pinQCl` lattice row in the weight

`Work.BoseBoxFock.pinQCl ℓ W y` is the lattice series

    ∑'_n  Ŵ(kmomInt ℓ n) · χ̂(ℓ • kmomInt ℓ n) · e^{−i⟪kmomInt ℓ n, y⟫} ,

whose only dependence on the kernel `W` is through the Fourier transform `chat W`, an integral
linear in `W`.  Hence it is additive in `W` on integrable kernels.

The mathematical content is the **summability** of the two lattice families (needed to apply
`Summable.tsum_add`): the summand is bounded by `|Ŵ|·|χ̂| ≤ B·C·(1+‖vec n‖²)^{-52}` since `Ŵ` is
uniformly bounded by its `L¹` mass and `χ̂` decays at order `52`, and `Σ_n (1+‖vec n‖²)^{-52}`
converges on `ℤ³` (`Work.BoseBoxFock.summable_vec_inv_one_add_norm_sq`).

The argument is the `pinQCl` instance of the private `pinQCl_add` of
`Submission/Work/BoseBoxFock/limit_rows_add.lean`, restated here for *integrable* (not
compactly supported) kernels, which is the form the `K1dirB` error rows use.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.K1dirB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Helpers (summability of the lattice family and linearity of `chat`) -/

/-- The norm of a real number seen in `ℂ`. -/
private lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- `chat` is additive in its kernel, in the `W + U` spelling (`chat` is an integral). -/
private lemma chat_add' {W U : E3 → ℝ} (hW : MeasureTheory.Integrable W)
    (hU : MeasureTheory.Integrable U) (k : E3) :
    Work.BoseFixR.chat (W + U) k = Work.BoseFixR.chat W k + Work.BoseFixR.chat U k := by
  rw [show (W + U) = fun x => W x + U x from funext fun x => rfl]
  exact Work.BoseRowsFS.CoulBilin.chat_add hW hU k

/-- `ℓ • kmomInt ℓ n = vec n` for `ℓ ≠ 0`. -/
private lemma smul_kmomInt {ℓ : ℝ} (hℓ : ℓ ≠ 0) (n : Fin 3 → ℤ) :
    ℓ • kmomInt ℓ n = Work.BoseB4.vec n := by
  rw [kmomInt, smul_smul, mul_inv_cancel₀ hℓ, one_smul]

/-- The conjugate exponential of a purely imaginary phase has norm `1`. -/
private lemma norm_exp_neg_I_mul_ofReal (r : ℝ) :
    ‖Complex.exp (-(Complex.I * (r : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (-(Complex.I * (r : ℂ))).re = 0 := by simp
  rw [h, Real.exp_zero]

/-- Multiplication by a unimodular phase preserves summability. -/
private lemma summable_mul_phase {f : (Fin 3 → ℤ) → ℂ} (hf : Summable f)
    {phase : (Fin 3 → ℤ) → ℂ} (hphase : ∀ n, ‖phase n‖ ≤ 1) :
    Summable (fun n => f n * phase n) := by
  refine Summable.of_norm_bounded hf.norm (fun n => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hphase n)

/-- **Summability of the `χ̂`-weighted lattice family.**  For `ℓ > 0`, the family
`n ↦ Ŵ(kmomInt ℓ n)·χ̂(ℓ • kmomInt ℓ n)^k` (`k ≥ 1`) is summable, by the uniform `L¹` bound on
`Ŵ` and the order-`52` decay of `χ̂`. -/
private lemma summable_hatChi_core {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ k) := by
  obtain ⟨B, hB0, hB⟩ := chat_abs_le_uniform (W := W)
  obtain ⟨C, hC0, hC⟩ := hatChi_decay_52
  have h52 : 2 ≤ 52 * k := by omega
  have hsumg : Summable (fun n : Fin 3 → ℤ =>
      (B * C ^ k) * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (52 * k))⁻¹) :=
    (summable_vec_inv_one_add_norm_sq h52).mul_left (B * C ^ k)
  refine Summable.of_norm_bounded hsumg (fun n => ?_)
  rw [smul_kmomInt (ne_of_gt hℓ) n, norm_mul, norm_pow, norm_ofReal_complex,
    norm_ofReal_complex]
  have h1 : |Work.BoseFixR.chat W (kmomInt ℓ n)|
        * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)| ^ k
      ≤ B * (C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) ^ k :=
    mul_le_mul (hB _) (pow_le_pow_left₀ (abs_nonneg _) (hC _) k)
      (pow_nonneg (abs_nonneg _) k) hB0
  refine le_trans h1 ?_
  have hEq : B * (C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) ^ k
      = B * C ^ k * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (52 * k))⁻¹ := by
    rw [mul_pow, inv_pow, ← pow_mul, ← mul_assoc]
  exact le_of_eq hEq

/-- The `pinQCl` summand family of a kernel `W` is summable. -/
private lemma summable_cl {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (y : E3) :
    Summable (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))) := by
  have h := summable_mul_phase (f := fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 1)
    (summable_hatChi_core hℓ W 1 le_rfl) (phase := fun n =>
      Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ))))
    (fun n => le_of_eq (norm_exp_neg_I_mul_ofReal _))
  simpa only [pow_one] using h

/-! ## The additivity theorem -/

theorem pinQCl_add_int {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hIa : MeasureTheory.Integrable Wa) (hIb : MeasureTheory.Integrable Wb)
    (y : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.pinQCl ℓ (Wa + Wb) y
      = Work.BoseBoxFock.pinQCl ℓ Wa y + Work.BoseBoxFock.pinQCl ℓ Wb y := by
  have hsumA := summable_cl hℓ Wa y
  have hsumB := summable_cl hℓ Wb y
  have hpt : ∀ n : Fin 3 → ℤ,
      ((Work.BoseFixR.chat (Wa + Wb) (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))
      = (((Work.BoseFixR.chat Wa (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ))))
        + (((Work.BoseFixR.chat Wb (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))) := by
    intro n
    rw [chat_add' hIa hIb (kmomInt ℓ n)]
    push_cast
    ring
  rw [pinQCl]
  rw [show (fun n : Fin 3 → ℤ =>
        ((Work.BoseFixR.chat (Wa + Wb) (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ))))
      = fun n : Fin 3 → ℤ =>
        (((Work.BoseFixR.chat Wa (kmomInt ℓ n) : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ))))
          + (((Work.BoseFixR.chat Wb (kmomInt ℓ n) : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))) from
      funext hpt]
  rw [Summable.tsum_add hsumA hsumB]
  rfl

end Work.BoseBoxFock.K1dirB
