import Mathlib
import Submission.Work.NN.Newton.pushforward_norms

/-!
# `mNorm` is controlled by the two `vNorm`-sums of the basis families

The componentwise operator norm `mNorm 1 α T Ω` (see
`Submission/Work/NN/Newton/pushforward_norms.lean`) is the sum of two blocks:

* the two families `T z (e_j)`, `T z (i e_j)` evaluated on the real basis of `ℂⁿ`, and
* the `ℂ`-linear and `ℂ`-antilinear coefficient vectors `linCoef (T z) p`, `antiCoef (T z) p`.

The coefficient vectors are explicit `ℂ`-linear combinations of the basis values,

  `linCoef (T z) p = ½ (T z (e_p) - i (T z (i e_p)))`,
  `antiCoef (T z) p = ½ (T z (e_p) + i (T z (i e_p)))`,

so each of their components has `holderNorm` at most `½` times the sum of the corresponding
component norms of `T z (e_p)` and `T z (i e_p)`.  Summing over the components and over `p`
shows that the whole coefficient block is bounded by the two basis blocks, whence

  `mNorm 1 α T Ω ≤ 2 * (B1 + B2)`

whenever the two basis blocks are bounded by `B1`, `B2`.  This is the "reverse" reading of
`mNorm`: knowing only the basis values of `T` already bounds the full componentwise norm.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff

namespace Work.NN.Newton.AopAux

variable {n : ℕ} {α : ℝ} {Ω : Set (Work.NN.Core.Cn n)}

/-- `ofReal ‖½‖ = ½` in `ℝ≥0∞`. -/
private lemma ofReal_norm_half : ENNReal.ofReal ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ≥0∞) := by
  rw [show ‖(1 / 2 : ℂ)‖ = (2 : ℝ)⁻¹ by norm_num]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp

/-- `½ + ½ = 1` in `ℝ≥0∞`. -/
private lemma half_add_half : ((1 / 2 : ℝ≥0∞) + 1 / 2) = 1 := by
  rw [show (1 / 2 : ℝ≥0∞) = 2⁻¹ by norm_num [one_div], ENNReal.inv_two_add_inv_two]

/-- Componentwise bound for the `ℂ`-linear coefficients: the `j`-th component of
`linCoef (T z) p` is `½ ((T z (e_p))_j - i (T z (i e_p))_j)`, whose `C^{1,α}`-norm is at most
`½` times the sum of the component norms of the two basis families. -/
private lemma linCoef_component_holderNorm_le
    {T : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hΩ : UniqueDiffOn ℝ Ω) (hT : ContDiffOn ℝ 1 T Ω) (p j : Fin n) :
    Work.CR.Flat.holderNorm 1 α (fun z => (Work.NN.Newton.linCoef (T z) p) j) Ω
      ≤ (1 / 2 : ℝ≥0∞) *
        (Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
          + Work.CR.Flat.holderNorm 1 α
              (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω) := by
  have hA : ContDiffOn ℝ (1 : ℕ∞) (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω :=
    Work.NN.Newton.contDiffOn_clm_component hT _ j
  have hB : ContDiffOn ℝ (1 : ℕ∞) (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω :=
    Work.NN.Newton.contDiffOn_clm_component hT _ j
  have key : (fun z => (Work.NN.Newton.linCoef (T z) p) j)
      = (1 / 2 : ℂ) • ((fun z => (T z (Pi.single p (1 : ℂ))) j)
          + (-Complex.I) • (fun z => (T z (Pi.single p (Complex.I : ℂ))) j)) := by
    funext z
    simp only [Work.NN.Newton.linCoef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hF : ContDiffOn ℝ (1 : ℕ∞) ((fun z => (T z (Pi.single p (1 : ℂ))) j)
      + (-Complex.I) • (fun z => (T z (Pi.single p (Complex.I : ℂ))) j)) Ω :=
    hA.add (hB.const_smul (-Complex.I))
  calc Work.CR.Flat.holderNorm 1 α (fun z => (Work.NN.Newton.linCoef (T z) p) j) Ω
      = ENNReal.ofReal ‖(1 / 2 : ℂ)‖ * Work.CR.Flat.holderNorm 1 α
          ((fun z => (T z (Pi.single p (1 : ℂ))) j)
            + (-Complex.I) • (fun z => (T z (Pi.single p (Complex.I : ℂ))) j)) Ω := by
        rw [key, Work.CR.Flat.Holder.holderNorm_smul (1 / 2 : ℂ) hF hΩ]
    _ ≤ ENNReal.ofReal ‖(1 / 2 : ℂ)‖ *
          (Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
            + Work.CR.Flat.holderNorm 1 α
                (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω) := by
        refine mul_le_mul_right ?_ _
        calc Work.CR.Flat.holderNorm 1 α ((fun z => (T z (Pi.single p (1 : ℂ))) j)
              + (-Complex.I) • (fun z => (T z (Pi.single p (Complex.I : ℂ))) j)) Ω
            ≤ Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
              + Work.CR.Flat.holderNorm 1 α
                  ((-Complex.I) • (fun z => (T z (Pi.single p (Complex.I : ℂ))) j)) Ω :=
              Work.CR.Flat.Holder.holderNorm_add_le hA (hB.const_smul (-Complex.I)) hΩ
          _ = Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
              + Work.CR.Flat.holderNorm 1 α
                  (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω := by
              rw [Work.CR.Flat.Holder.holderNorm_smul (-Complex.I) hB hΩ]
              norm_num
    _ = (1 / 2 : ℝ≥0∞) *
          (Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
            + Work.CR.Flat.holderNorm 1 α
                (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω) := by
        rw [ofReal_norm_half]

/-- Componentwise bound for the `ℂ`-antilinear coefficients: the `j`-th component of
`antiCoef (T z) p` is `½ ((T z (e_p))_j + i (T z (i e_p))_j)`, whose `C^{1,α}`-norm is at most
`½` times the sum of the component norms of the two basis families. -/
private lemma antiCoef_component_holderNorm_le
    {T : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hΩ : UniqueDiffOn ℝ Ω) (hT : ContDiffOn ℝ 1 T Ω) (p j : Fin n) :
    Work.CR.Flat.holderNorm 1 α (fun z => (Work.NN.Newton.antiCoef (T z) p) j) Ω
      ≤ (1 / 2 : ℝ≥0∞) *
        (Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
          + Work.CR.Flat.holderNorm 1 α
              (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω) := by
  have hA : ContDiffOn ℝ (1 : ℕ∞) (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω :=
    Work.NN.Newton.contDiffOn_clm_component hT _ j
  have hB : ContDiffOn ℝ (1 : ℕ∞) (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω :=
    Work.NN.Newton.contDiffOn_clm_component hT _ j
  have key : (fun z => (Work.NN.Newton.antiCoef (T z) p) j)
      = (1 / 2 : ℂ) • ((fun z => (T z (Pi.single p (1 : ℂ))) j)
          + (Complex.I) • (fun z => (T z (Pi.single p (Complex.I : ℂ))) j)) := by
    funext z
    simp only [Work.NN.Newton.antiCoef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hF : ContDiffOn ℝ (1 : ℕ∞) ((fun z => (T z (Pi.single p (1 : ℂ))) j)
      + (Complex.I) • (fun z => (T z (Pi.single p (Complex.I : ℂ))) j)) Ω :=
    hA.add (hB.const_smul (Complex.I))
  calc Work.CR.Flat.holderNorm 1 α (fun z => (Work.NN.Newton.antiCoef (T z) p) j) Ω
      = ENNReal.ofReal ‖(1 / 2 : ℂ)‖ * Work.CR.Flat.holderNorm 1 α
          ((fun z => (T z (Pi.single p (1 : ℂ))) j)
            + (Complex.I) • (fun z => (T z (Pi.single p (Complex.I : ℂ))) j)) Ω := by
        rw [key, Work.CR.Flat.Holder.holderNorm_smul (1 / 2 : ℂ) hF hΩ]
    _ ≤ ENNReal.ofReal ‖(1 / 2 : ℂ)‖ *
          (Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
            + Work.CR.Flat.holderNorm 1 α
                (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω) := by
        refine mul_le_mul_right ?_ _
        calc Work.CR.Flat.holderNorm 1 α ((fun z => (T z (Pi.single p (1 : ℂ))) j)
              + (Complex.I) • (fun z => (T z (Pi.single p (Complex.I : ℂ))) j)) Ω
            ≤ Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
              + Work.CR.Flat.holderNorm 1 α
                  ((Complex.I) • (fun z => (T z (Pi.single p (Complex.I : ℂ))) j)) Ω :=
              Work.CR.Flat.Holder.holderNorm_add_le hA (hB.const_smul (Complex.I)) hΩ
          _ = Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
              + Work.CR.Flat.holderNorm 1 α
                  (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω := by
              rw [Work.CR.Flat.Holder.holderNorm_smul (Complex.I) hB hΩ]
              norm_num
    _ = (1 / 2 : ℝ≥0∞) *
          (Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
            + Work.CR.Flat.holderNorm 1 α
                (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω) := by
        rw [ofReal_norm_half]

/-- The `vNorm` of the `p`-th `ℂ`-linear coefficient family is bounded by `½` times the sum of
the `vNorm`s of the two `p`-th basis families. -/
private lemma vNorm_linCoef_le
    {T : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hΩ : UniqueDiffOn ℝ Ω) (hT : ContDiffOn ℝ 1 T Ω) (p : Fin n) :
    Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.linCoef (T z) p) Ω
      ≤ (1 / 2 : ℝ≥0∞) *
        (Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single p (1 : ℂ))) Ω
          + Work.NN.Newton.vNorm 1 α
              (fun z => T z (Pi.single p (Complex.I : ℂ))) Ω) := by
  refine (Work.NN.Newton.vNorm_le_sum 1 α _ Ω
    (fun j => (1 / 2 : ℝ≥0∞) *
      (Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
        + Work.CR.Flat.holderNorm 1 α
            (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω))
    (fun j => linCoef_component_holderNorm_le (α := α) hΩ hT p j)).trans (le_of_eq ?_)
  simp only [Work.NN.Newton.vNorm, mul_add, Finset.mul_sum, Finset.sum_add_distrib]

/-- The `vNorm` of the `p`-th `ℂ`-antilinear coefficient family is bounded by `½` times the sum
of the `vNorm`s of the two `p`-th basis families. -/
private lemma vNorm_antiCoef_le
    {T : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hΩ : UniqueDiffOn ℝ Ω) (hT : ContDiffOn ℝ 1 T Ω) (p : Fin n) :
    Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.antiCoef (T z) p) Ω
      ≤ (1 / 2 : ℝ≥0∞) *
        (Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single p (1 : ℂ))) Ω
          + Work.NN.Newton.vNorm 1 α
              (fun z => T z (Pi.single p (Complex.I : ℂ))) Ω) := by
  refine (Work.NN.Newton.vNorm_le_sum 1 α _ Ω
    (fun j => (1 / 2 : ℝ≥0∞) *
      (Work.CR.Flat.holderNorm 1 α (fun z => (T z (Pi.single p (1 : ℂ))) j) Ω
        + Work.CR.Flat.holderNorm 1 α
            (fun z => (T z (Pi.single p (Complex.I : ℂ))) j) Ω))
    (fun j => antiCoef_component_holderNorm_le (α := α) hΩ hT p j)).trans (le_of_eq ?_)
  simp only [Work.NN.Newton.vNorm, mul_add, Finset.mul_sum, Finset.sum_add_distrib]

/-- **The basis values control the coefficient block.**  The sum over `p` of the `vNorm`s of the
`ℂ`-linear and `ℂ`-antilinear coefficient families is bounded by the sum of the two basis blocks. -/
private lemma sum_coef_le_sum_basis
    {T : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hΩ : UniqueDiffOn ℝ Ω) (hT : ContDiffOn ℝ 1 T Ω) :
    (∑ p, (Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.linCoef (T z) p) Ω
        + Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.antiCoef (T z) p) Ω))
      ≤ (∑ j, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j (1 : ℂ))) Ω)
        + (∑ j, Work.NN.Newton.vNorm 1 α
            (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω) := by
  calc ∑ p, (Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.linCoef (T z) p) Ω
        + Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.antiCoef (T z) p) Ω)
      ≤ ∑ p, (((1 / 2 : ℝ≥0∞) *
            (Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single p (1 : ℂ))) Ω
              + Work.NN.Newton.vNorm 1 α
                  (fun z => T z (Pi.single p (Complex.I : ℂ))) Ω))
          + ((1 / 2 : ℝ≥0∞) *
            (Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single p (1 : ℂ))) Ω
              + Work.NN.Newton.vNorm 1 α
                  (fun z => T z (Pi.single p (Complex.I : ℂ))) Ω))) :=
        Finset.sum_le_sum fun p _ =>
          add_le_add (vNorm_linCoef_le hΩ hT p) (vNorm_antiCoef_le hΩ hT p)
    _ = ∑ p, ((Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single p (1 : ℂ))) Ω)
          + (Work.NN.Newton.vNorm 1 α
              (fun z => T z (Pi.single p (Complex.I : ℂ))) Ω)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← add_mul, half_add_half, one_mul]
    _ = (∑ j, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j (1 : ℂ))) Ω)
          + (∑ j, Work.NN.Newton.vNorm 1 α
              (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω) := by
        rw [Finset.sum_add_distrib]

/-- **The basis values control `mNorm`.**  If the two basis blocks are bounded by `B1` and `B2`,
then `mNorm 1 α T Ω ≤ 2 * (B1 + B2)`. -/
theorem mNorm_le_two_vNorm_basis {n : ℕ} {α : ℝ} {Ω : Set (Work.NN.Core.Cn n)}
    (hΩ : UniqueDiffOn ℝ Ω)
    {T : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hT : ContDiffOn ℝ 1 T Ω) {B1 B2 : ENNReal}
    (h1 : (∑ j, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j 1)) Ω) ≤ B1)
    (h2 : (∑ j, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω) ≤ B2) :
    Work.NN.Newton.mNorm 1 α T Ω ≤ 2 * (B1 + B2) := by
  unfold Work.NN.Newton.mNorm
  calc (∑ j, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j (1 : ℂ))) Ω)
        + (∑ j, Work.NN.Newton.vNorm 1 α
            (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω)
        + ∑ p, (Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.linCoef (T z) p) Ω
            + Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.antiCoef (T z) p) Ω)
      ≤ (∑ j, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j (1 : ℂ))) Ω)
        + (∑ j, Work.NN.Newton.vNorm 1 α
            (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω)
        + ((∑ j, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j (1 : ℂ))) Ω)
          + (∑ j, Work.NN.Newton.vNorm 1 α
              (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω)) :=
        add_le_add le_rfl (sum_coef_le_sum_basis hΩ hT)
    _ = 2 * ((∑ j, Work.NN.Newton.vNorm 1 α (fun z => T z (Pi.single j (1 : ℂ))) Ω)
          + (∑ j, Work.NN.Newton.vNorm 1 α
              (fun z => T z (Pi.single j (Complex.I : ℂ))) Ω)) := by
        rw [two_mul]
    _ ≤ 2 * (B1 + B2) := mul_le_mul' le_rfl (add_le_add h1 h2)

end Work.NN.Newton.AopAux
