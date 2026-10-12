import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Submission.Work.BoseBoxFock.PCFU.UnivFrames
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.G_boxFacts`

The elementary *facts* about the atom-1 integrand of the `(χ,χ)` channel,

    `x ↦ Θ x · χ_Λ(x i) · χ_Λ(x j) · KfrU (x j − x i)`

(`Θ` a bounded measurable function supported in the `n`-particle box, `χ_Λ` the corpus
box localisation, `KfrU` the `univ`-summed `k`-frame of `PCFU/UnivFrames.lean`): it is
measurable, pointwise dominated by

    `Cθ · (√∫χ_base²)⁻¹ · (√∫χ_base²)⁻¹ · Σ_k |Ŵ₁(k)|`,

and its support still lies in the box.

The two inputs are the *normalisation* of the two `χ_Λ`-factors
(`χ_Λ = χ_base(·/ℓ)/√chiNormSq`, `|χ_base| ≤ 1`, `Submission/CubicChi.lean`) and the
triangle inequality for the finite frame sum (every summand has norm `|Ŵ₁(k)|`, the
exponential being purely imaginary).  The support statement is the elementary fact that
the support of a product is contained in the support of each factor.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **The normalisation of the corpus box localisation.**  `χ_Λ(z) = χ_base(z/ℓ)/√chiNormSq`
with `|χ_base| ≤ 1`, hence `|χ_Λ(z)| ≤ (√chiNormSq)⁻¹` for every `ℓ` (no positivity of `ℓ`
is needed). -/
lemma norm_chiLam_le (ℓ : ℝ) (z : Ω) :
    ‖((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
      ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
  have hsqrt : 0 < Real.sqrt Submission.BoseGases.chiNormSq :=
    Real.sqrt_pos.mpr Submission.BoseGases.chiNormSq_pos
  have hval : Work.BoseK15.corpusBox.chiLam ℓ z
      = Submission.BoseGases.chiBase (ℓ⁻¹ • z) / Real.sqrt Submission.BoseGases.chiNormSq := by
    simp only [Work.BoseB4.BoxData.chiLam, Work.BoseK15.corpusBox_chi, Submission.BoseGases.chi]
  have hb : |Submission.BoseGases.chiBase (ℓ⁻¹ • z)| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [Submission.BoseGases.chiBase_nonneg (ℓ⁻¹ • z)],
      Submission.BoseGases.chiBase_le_one _⟩
  rw [show ‖((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)‖
      = |Work.BoseK15.corpusBox.chiLam ℓ z| from by simp]
  rw [hval, abs_div, abs_of_pos hsqrt]
  rw [div_le_iff₀ hsqrt, inv_mul_cancel₀ (ne_of_gt hsqrt)]
  exact hb

/-- **The triangle inequality for the `univ` `k`-frame**: every summand of `KfrU` has norm
`|Ŵ₁(k)|` (the phase factor is purely imaginary, hence of modulus one). -/
lemma norm_KfrU_le (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (z : Ω) :
    ‖KfrU v h μ fu N z‖
      ≤ ∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k| := by
  rw [KfrU]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  have hexp : ‖Complex.exp (Complex.I * ((inner ℝ
      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) z : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [hexp, mul_one,
    show ‖(((Work.BoseBoxFock.W1h v h μ fu N k : ℝ)) : ℂ)‖
      = |Work.BoseBoxFock.W1h v h μ fu N k| from by simp]

/-- The `univ` `k`-frame is a finite sum of continuous phase factors. -/
lemma continuous_KfrU (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) :
    Continuous fun z : Ω => KfrU v h μ fu N z := by
  rw [show (fun z : Ω => KfrU v h μ fu N z)
      = (fun z : Ω => ∑ k : Work.BoseBoxFock.Lab N,
          ((Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ
                (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) z : ℝ) : ℂ)))
      from by funext z; rfl]
  fun_prop

/-- Measurability of the `univ` `k`-frame as a function of the position. -/
lemma measurable_KfrU (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) :
    Measurable fun z : Ω => KfrU v h μ fu N z :=
  (continuous_KfrU v h μ fu N).measurable

theorem G_boxFacts {n : ℕ} {i j : Fin n} {ℓ : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {fu : Work.BoseBoxFix.LowCut} {N : ℕ} (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (Cθ : ℝ) (hΘb : ∀ x, |Θ x| ≤ Cθ)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    (Measurable (fun x : Submission.BoseGases.X n =>
        ((Θ x : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)))
    ∧ (∀ x, ‖((Θ x : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)‖
        ≤ Cθ * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
            * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
            * ∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|)
    ∧ (Function.support (fun x : Submission.BoseGases.X n =>
        ((Θ x : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)) ⊆ Submission.BoseGases.abox n ℓ) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Measurable fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp hΘm
    have h2 : Measurable fun x : Submission.BoseGases.X n =>
        ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp
        (((Work.BoseB4.BoxData.chiLam_cont _ ℓ).measurable).comp (measurable_pi_apply i))
    have h3 : Measurable fun x : Submission.BoseGases.X n =>
        ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp
        (((Work.BoseB4.BoxData.chiLam_cont _ ℓ).measurable).comp (measurable_pi_apply j))
    have h4 : Measurable fun x : Submission.BoseGases.X n =>
        KfrU v h μ fu N (x j - x i) :=
      (measurable_KfrU v h μ fu N).comp ((measurable_pi_apply j).sub (measurable_pi_apply i))
    exact ((h1.mul h2).mul h3).mul h4
  · intro x
    have hA : ‖((Θ x : ℝ) : ℂ)‖ ≤ Cθ := by
      rw [show ‖((Θ x : ℝ) : ℂ)‖ = |Θ x| from by simp]; exact hΘb x
    have hCθ : 0 ≤ Cθ := le_trans (abs_nonneg _) (hΘb x)
    have hC : (0:ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    rw [show ‖((Θ x : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)
          * KfrU v h μ fu N (x j - x i)‖
        = ‖((Θ x : ℝ) : ℂ)‖
          * ‖((Work.BoseK15.corpusBox.chiLam ℓ (x i) : ℝ) : ℂ)‖
          * ‖((Work.BoseK15.corpusBox.chiLam ℓ (x j) : ℝ) : ℂ)‖
          * ‖KfrU v h μ fu N (x j - x i)‖ from by
      rw [norm_mul, norm_mul, norm_mul]]
    exact mul_le_mul
      (mul_le_mul (mul_le_mul hA (norm_chiLam_le ℓ (x i)) (norm_nonneg _) hCθ)
        (norm_chiLam_le ℓ (x j)) (norm_nonneg _) (mul_nonneg hCθ hC))
      (norm_KfrU_le v h μ fu N (x j - x i)) (norm_nonneg _)
      (mul_nonneg (mul_nonneg hCθ hC) hC)
  · intro x hx
    apply hΘs
    intro h0
    exact hx (by simp [h0])

end Work.BoseBoxFock.PCFU
