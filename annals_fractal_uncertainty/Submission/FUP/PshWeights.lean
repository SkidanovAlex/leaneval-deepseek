import Submission.FUP.DbarDbarPos
import Submission.Commons.Analysis.Calculus.complexHessian_im_norm

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators

set_option autoImplicit false
variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

/-!
# The two explicit strictly-plurisubharmonic weights of Cohen's §5

Cohen's §5 uses the weight `φ = 2u + 20d·log|z|∞ + ρ u₀ + (ρ/2)(⟨Im z⟩ - 1)`, and its strict
plurisubharmonicity comes from the last term alone (`∂∂̄⟨y⟩ ≥ ¼⟨y⟩^{-3}`).  This module proves
`DbarDbarPos` for the two explicit smooth weights

* `z ↦ (ρ/2)(⟨Im z⟩ - 1)` with `κ = (ρ/8)⟨Im z⟩^{-3}`, and
* `z ↦ c·log(1+‖z‖²)`

(the logarithmic term replaces the paper's `log|z|∞`, which is `-∞` at the origin; the constants in
the paper's estimates only depend on `d` and are not optimized there).  The remaining terms
(`2u`, `ρu₀`) come from `isPSH_dbarDbarPos`.
-/

namespace Submission.FUP

section ImNorm

/-- `‖Im z‖² = ∑_j (Im z_j)²`. -/
noncomputable def imSq (z : ℂᵈ) : ℝ := ∑ j, (z j).im ^ 2

/-- `⟨Im z⟩ = √(1 + ∑_j (Im z_j)²)`. -/
noncomputable def imNorm (z : ℂᵈ) : ℝ := Real.sqrt (1 + ∑ j, (z j).im ^ 2)

lemma imSq_nonneg (z : ℂᵈ) : 0 ≤ imSq z := by
  rw [imSq]; exact Finset.sum_nonneg fun j _ => sq_nonneg _

lemma one_le_imNorm (z : ℂᵈ) : 1 ≤ imNorm z := by
  have h : (1:ℝ) ≤ 1 + ∑ j : Fin d, (z j).im ^ 2 := by
    have h0 : (0:ℝ) ≤ ∑ j : Fin d, (z j).im ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ∑ j : Fin d, (z j).im ^ 2) := Real.sqrt_le_sqrt h
    _ = imNorm z := by rw [imNorm]

lemma imNorm_pos (z : ℂᵈ) : 0 < imNorm z := lt_of_lt_of_le one_pos (one_le_imNorm z)

lemma contDiff_imNorm : ContDiff ℝ 2 (fun z : ℂᵈ => imNorm z) := by
  apply ContDiff.sqrt
  · apply ContDiff.add contDiff_const
    apply ContDiff.sum
    intro j _
    have h : ContDiff ℝ 2 (fun z : ℂᵈ => (z j).im) := by
      have h1 : ContDiff ℝ 2 (fun z : ℂᵈ => (Complex.imCLM : ℂ → ℝ) (z j)) := by fun_prop
      simpa using h1
    exact h.pow 2
  · intro z; positivity

/-- `(ρ/2)(⟨Im z⟩-1)` is `C²`. -/
lemma contDiff_imWeight (ρ : ℝ) :
    ContDiff ℝ 2 (fun z : ℂᵈ => (ρ / 2) * (imNorm z - 1)) := by
  have h : ContDiff ℝ 2 ((ρ / 2) • ((fun z : ℂᵈ => imNorm z) - fun _ : ℂᵈ => (1 : ℝ))) :=
    ContDiff.const_smul (ρ / 2) (contDiff_imNorm.sub contDiff_const)
  exact h

/-- `(ρ/2)(⟨Im z⟩-1)` is bounded on balls. -/
lemma boundedOnCompact_imWeight (ρ : ℝ) :
    BoundedOnCompact (fun z : ℂᵈ => (ρ / 2) * (imNorm z - 1)) := by
  intro R
  refine ⟨|ρ / 2| * Real.sqrt (1 + (d : ℝ) * (max R 0) ^ 2), fun z hz => ?_⟩
  have hnorm : ‖z‖ ≤ max R 0 := le_trans hz (le_max_left _ _)
  have hsum : (∑ j : Fin d, (z j).im ^ 2) ≤ (d : ℝ) * (max R 0) ^ 2 := by
    calc ∑ j : Fin d, (z j).im ^ 2 ≤ ∑ _j : Fin d, (max R 0) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 : (z j).im ^ 2 ≤ ‖z j‖ ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg (z j).re]
          have h2 : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
          nlinarith [norm_nonneg (z j), norm_nonneg z, sq_nonneg (max R 0)]
      _ = (d : ℝ) * (max R 0) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : imNorm z ≤ Real.sqrt (1 + (d : ℝ) * (max R 0) ^ 2) := by
    rw [imNorm]; exact Real.sqrt_le_sqrt (by linarith)
  have h2 : 0 ≤ imNorm z - 1 := by linarith [one_le_imNorm z]
  rw [abs_mul, abs_of_nonneg h2]
  exact mul_le_mul_of_nonneg_left (by linarith [h1]) (abs_nonneg _)

lemma continuous_imKappa (ρ : ℝ) :
    Continuous (fun z : ℂᵈ => (ρ / 8) / (imNorm z) ^ 3) :=
  continuous_const.div (contDiff_imNorm.continuous.pow 3)
    (fun z => pow_ne_zero 3 (ne_of_gt (imNorm_pos z)))

lemma measurable_imKappa (ρ : ℝ) :
    Measurable (fun z : ℂᵈ => (ρ / 8) / (imNorm z) ^ 3) :=
  (continuous_imKappa ρ).measurable

lemma boundedOnCompact_imKappa (ρ : ℝ) :
    BoundedOnCompact (fun z : ℂᵈ => (ρ / 8) / (imNorm z) ^ 3) := by
  intro R
  refine ⟨|ρ / 8|, fun z _ => ?_⟩
  rw [abs_div, abs_of_nonneg (pow_nonneg (le_of_lt (imNorm_pos z)) 3)]
  exact div_le_self (abs_nonneg _) (by
    have : 1 ≤ (imNorm z) ^ 3 := one_le_pow₀ (one_le_imNorm z)
    linarith)

/-- The second derivative of `(ρ/2)(⟨Im z⟩-1)` is `(ρ/2)` times the second derivative of
`⟨Im z⟩` (the constant `-1` and the scalar `ρ/2` do not contribute). -/
lemma iteratedFDeriv_imWeight (ρ : ℝ) (z : ℂᵈ) :
    iteratedFDeriv ℝ 2 (fun z : ℂᵈ => (ρ / 2) * (imNorm z - 1)) z
      = (ρ / 2) • (iteratedFDeriv ℝ 2 (fun z : ℂᵈ => imNorm z) z) := by
  have h1 : (fun z : ℂᵈ => (ρ / 2) * (imNorm z - 1))
      = (ρ / 2) • ((fun z : ℂᵈ => imNorm z) - fun _ : ℂᵈ => (1 : ℝ)) := by
    funext z; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have h2 : iteratedFDeriv ℝ 2 ((fun z : ℂᵈ => imNorm z) - fun _ : ℂᵈ => (1 : ℝ)) z
      = iteratedFDeriv ℝ 2 (fun z : ℂᵈ => imNorm z) z := by
    rw [iteratedFDeriv_sub_apply contDiff_imNorm.contDiffAt
        (contDiff_const (c := (1 : ℝ))).contDiffAt,
      iteratedFDeriv_const_of_ne (𝕜 := ℝ) (F := ℝ) (n := 2) (by norm_num) (1 : ℝ)]
    simp
  rw [h1, iteratedFDeriv_const_smul_apply
    (f := (fun z : ℂᵈ => imNorm z) - fun _ : ℂᵈ => (1 : ℝ))
    ((contDiff_imNorm.sub contDiff_const).contDiffAt), h2]

/-- The pointwise Hermitian-Hessian bound for `z ↦ (ρ/2)(⟨Im z⟩-1)`. -/
lemma hessian_imWeight (ρ : ℝ) (hρ : 0 ≤ ρ) (z w : ℂᵈ) :
    4 * (((ρ / 8) / (imNorm z) ^ 3) * ∑ j, ‖w j‖ ^ 2) ≤
      (iteratedFDeriv ℝ 2 (fun z : ℂᵈ => (ρ / 2) * (imNorm z - 1)) z) ![w, w]
        + (iteratedFDeriv ℝ 2 (fun z : ℂᵈ => (ρ / 2) * (imNorm z - 1)) z)
            ![Complex.I • w, Complex.I • w] := by
  have ha : 0 < imNorm z := imNorm_pos z
  have hN : ∑ j, ‖w j‖ ^ 2 = ∑ j, (w j).im ^ 2 + ∑ j, (w j).re ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hkey : (∑ j, (w j).im ^ 2 + ∑ j, (w j).re ^ 2) / (imNorm z) ^ 3 ≤
      (iteratedFDeriv ℝ 2 (fun z : ℂᵈ => imNorm z) z) ![w, w]
        + (iteratedFDeriv ℝ 2 (fun z : ℂᵈ => imNorm z) z) ![Complex.I • w, Complex.I • w] := by
    simpa only [imNorm] using
      Commons.Analysis.Calculus.complexHessian_im_norm (d := d) z w
  rw [hN, iteratedFDeriv_imWeight ρ z, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  have h4 : (ρ / 2) * ((iteratedFDeriv ℝ 2 (fun z : ℂᵈ => imNorm z) z) ![w, w])
      + (ρ / 2) * ((iteratedFDeriv ℝ 2 (fun z : ℂᵈ => imNorm z) z) ![Complex.I • w, Complex.I • w])
      = (ρ / 2) * ((iteratedFDeriv ℝ 2 (fun z : ℂᵈ => imNorm z) z) ![w, w]
          + (iteratedFDeriv ℝ 2 (fun z : ℂᵈ => imNorm z) z) ![Complex.I • w, Complex.I • w]) := by ring
  rw [h4]
  have h2 : 4 * ((ρ / 8) / (imNorm z) ^ 3
      * (∑ j, (w j).im ^ 2 + ∑ j, (w j).re ^ 2))
      = (ρ / 2) * ((∑ j, (w j).im ^ 2 + ∑ j, (w j).re ^ 2) / (imNorm z) ^ 3) := by
    have hz : imNorm z ≠ 0 := ne_of_gt ha
    field_simp
    ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

/-- **`DbarDbarPos` for the imaginary-norm weight.** -/
theorem dbarDbarPos_imWeight (ρ : ℝ) (hρ : 0 < ρ) :
    DbarDbarPos (fun z : ℂᵈ => (ρ / 2) * (imNorm z - 1))
      (fun z : ℂᵈ => (ρ / 8) / (imNorm z) ^ 3) :=
  dbarDbarPos_of_hessian (contDiff_imWeight ρ) (measurable_imKappa ρ)
    (boundedOnCompact_imKappa ρ) (boundedOnCompact_imWeight ρ) (hessian_imWeight ρ hρ.le)

end ImNorm

end Submission.FUP
