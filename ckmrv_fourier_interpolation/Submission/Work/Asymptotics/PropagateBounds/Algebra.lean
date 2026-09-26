/-
# The change of basis `M6 → M'` at even weight

Auxiliary algebra for `Work.Asymptotics.bound_of_propagates`: the six elements
`M6 = (I, T, TS, S, ST, STS)` of `Work.Residues` expressed in the second basis
`M' = (I, T⁻¹, STS, S, ST⁻¹, TS)` (`Work.Asymptotics.MpR`) used by the propagation argument.
Because the slash action is a *left* action (`slash k (r * s) F = slash k s (slash k r F)`), the
correction terms of the change of basis are themselves carries of the defect equations.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Residues.Basic
import Submission.Work.Asymptotics.PropagateMpDefs
import Submission.Work.Asymptotics.PropagateCarries
import Submission.Work.Asymptotics.PropagateBounds.Defs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

lemma R_T_mul_R_Tinv : (R_T : R) * R_Tinv = 1 := by
  rw [R_T, R_Tinv, MonoidAlgebra.single_mul_single]
  simp [MonoidAlgebra.one_def]

lemma R_Tinv_mul_R_T : (R_Tinv : R) * R_T = 1 := by
  rw [R_T, R_Tinv, MonoidAlgebra.single_mul_single]
  simp [MonoidAlgebra.one_def]

/-- `T = 2 - T⁻¹ + (T-1)² T⁻¹` in `R = ℂ[SL(2,ℤ)]`, i.e. the relation `T⁻¹ ≡ 2 - T (mod 𝓘)`
solved for `T`. -/
lemma R_T_eq : (R_T : R) = 2 - R_Tinv + (R_T - 1) ^ 2 * R_Tinv := by
  have h : (R_T - 1) ^ 2 * R_Tinv = R_T - 2 + R_Tinv := by
    calc (R_T - 1) ^ 2 * R_Tinv
        = R_T * R_T * R_Tinv - 2 * (R_T * R_Tinv) + R_Tinv := by noncomm_ring
      _ = R_T * (R_T * R_Tinv) - 2 * (R_T * R_Tinv) + R_Tinv := by rw [mul_assoc]
      _ = R_T - 2 + R_Tinv := by rw [R_T_mul_R_Tinv]; simp
  rw [h]; abel

/-- `ST = 2 S - S T⁻¹ + S (T-1)² T⁻¹` in `R = ℂ[SL(2,ℤ)]`. -/
lemma R_S_mul_R_T_eq : (R_S * R_T : R) = 2 * R_S - R_S * R_Tinv + R_S * (R_T - 1) ^ 2 * R_Tinv := by
  have h : (R_T - 1) ^ 2 * R_Tinv = R_T - 2 + R_Tinv := by
    calc (R_T - 1) ^ 2 * R_Tinv
        = R_T * R_T * R_Tinv - 2 * (R_T * R_Tinv) + R_Tinv := by noncomm_ring
      _ = R_T * (R_T * R_Tinv) - 2 * (R_T * R_Tinv) + R_Tinv := by rw [mul_assoc]
      _ = R_T - 2 + R_Tinv := by rw [R_T_mul_R_Tinv]; simp
  rw [mul_assoc R_S ((R_T - 1) ^ 2) R_Tinv, h]
  noncomm_ring

/-- The coefficients of the change of basis `M6 → M'`. -/
def dvec (σ : Fin 6 → ℂ) : Fin 6 → ℂ :=
  ![σ 0 + 2 * σ 1, -σ 1, σ 5, σ 3 + 2 * σ 4, -σ 4, σ 2]

@[simp] lemma dvec_zero (σ : Fin 6 → ℂ) : dvec σ 0 = σ 0 + 2 * σ 1 := rfl
@[simp] lemma dvec_one (σ : Fin 6 → ℂ) : dvec σ 1 = -σ 1 := rfl
@[simp] lemma dvec_two (σ : Fin 6 → ℂ) : dvec σ 2 = σ 5 := rfl
@[simp] lemma dvec_three (σ : Fin 6 → ℂ) : dvec σ 3 = σ 3 + 2 * σ 4 := rfl
@[simp] lemma dvec_four (σ : Fin 6 → ℂ) : dvec σ 4 = -σ 4 := rfl
@[simp] lemma dvec_five (σ : Fin 6 → ℂ) : dvec σ 5 = σ 2 := rfl

lemma dvec_apply (σ : Fin 6 → ℂ) (j : Fin 6) :
    ‖dvec σ j‖ ≤ 3 * (∑ i : Fin 6, ‖σ i‖) := by
  have hσ : ∀ i : Fin 6, ‖σ i‖ ≤ ∑ i : Fin 6, ‖σ i‖ := fun i =>
    Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ i)
  have hsum0 : (0:ℝ) ≤ ∑ i : Fin 6, ‖σ i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  fin_cases j
  · show ‖σ 0 + 2 * σ 1‖ ≤ 3 * _
    calc ‖σ 0 + 2 * σ 1‖ ≤ ‖σ 0‖ + ‖(2 : ℂ) * σ 1‖ := norm_add_le _ _
      _ = ‖σ 0‖ + 2 * ‖σ 1‖ := by rw [norm_mul, h2]
      _ ≤ 3 * _ := by nlinarith [hσ 0, hσ 1, hsum0]
  · show ‖-σ 1‖ ≤ 3 * _
    rw [norm_neg]
    nlinarith [hσ 1, hsum0]
  · show ‖σ 5‖ ≤ 3 * _
    nlinarith [hσ 5, hsum0]
  · show ‖σ 3 + 2 * σ 4‖ ≤ 3 * _
    calc ‖σ 3 + 2 * σ 4‖ ≤ ‖σ 3‖ + ‖(2 : ℂ) * σ 4‖ := norm_add_le _ _
      _ = ‖σ 3‖ + 2 * ‖σ 4‖ := by rw [norm_mul, h2]
      _ ≤ 3 * _ := by nlinarith [hσ 3, hσ 4, hsum0]
  · show ‖-σ 4‖ ≤ 3 * _
    rw [norm_neg]
    nlinarith [hσ 4, hsum0]
  · show ‖σ 2‖ ≤ 3 * _
    nlinarith [hσ 2, hsum0]

/-- `M6 0 = M' 0`. -/
lemma M6_zero' : Work.Residues.M6 (0 : Fin 6) = MpR 0 := by
  rw [Work.Residues.M6_zero, MpR_zero]

/-- `M6 1 = 2 M' 0 - M' 1 + (T-1)² T⁻¹`. -/
lemma M6_one' : (Work.Residues.M6 (1 : Fin 6) : R)
    = MpR 0 + MpR 0 - MpR 1 + (R_T - 1) ^ 2 * R_Tinv := by
  rw [Work.Residues.M6_one, MpR_zero, MpR_one]
  conv_lhs => rw [R_T_eq]
  have h2 : (2 : R) = 1 + 1 := by norm_num
  rw [h2]

/-- `M6 2 = M' 5`. -/
lemma M6_two' : Work.Residues.M6 (2 : Fin 6) = MpR 5 := by
  rw [Work.Residues.M6_two, MpR_five]

/-- `M6 3 = M' 3`. -/
lemma M6_three' : Work.Residues.M6 (3 : Fin 6) = MpR 3 := by
  rw [Work.Residues.M6_three, MpR_three]

/-- `M6 4 = 2 M' 3 - M' 4 + S (T-1)² T⁻¹`. -/
lemma M6_four' : (Work.Residues.M6 (4 : Fin 6) : R)
    = MpR 3 + MpR 3 - MpR 4 + (R_S * (R_T - 1) ^ 2) * R_Tinv := by
  rw [Work.Residues.M6_four, MpR_three, MpR_four]
  conv_lhs => rw [R_S_mul_R_T_eq]
  rw [two_mul]

/-- `M6 5 = M' 2`. -/
lemma M6_five' : Work.Residues.M6 (5 : Fin 6) = MpR 2 := by
  rw [Work.Residues.M6_five, MpR_two]

/-- **The change of basis.**  The `M6`-combination `∑ j, σ j • M6 j` is the `M'`-combination
with coefficients `dvec σ`, plus two carries along `(T-1)²` and `S(T-1)²`. -/
lemma M6_eq_Mp (σ : Fin 6 → ℂ) :
    (∑ j : Fin 6, σ j • Work.Residues.M6 j)
      = (∑ i : Fin 6, dvec σ i • MpR i)
        + (R_T - 1) ^ 2 * (σ 1 • R_Tinv)
        + (R_S * (R_T - 1) ^ 2) * (σ 4 • R_Tinv) := by
  rw [Fin.sum_univ_six, Fin.sum_univ_six]
  simp only [M6_zero', M6_one', M6_two', M6_three', M6_four', M6_five',
    dvec_zero, dvec_one, dvec_two, dvec_three, dvec_four, dvec_five]
  simp only [smul_add, smul_sub, mul_smul_comm]
  module


/-- **Expansion of the slash operator in the support of the group-algebra element.** -/
lemma slash_apply_eq_sum (k : ℤ) (A : R) (h : ℍ → ℂ) (τ : ℍ) :
    slash k A h τ = ∑ δ ∈ A.coeff.support, A.coeff δ * (h ∣[k] δ) τ := by
  rw [Work.Kernels.slash, Finsupp.sum]
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun δ _ => by rw [Pi.smul_apply, smul_eq_mul]

/-- The slash of a function with a bounded group-algebra element is bounded by the `ℓ¹`-norm of
the element times a uniform bound for the slashes of the monomials in its support. -/
lemma norm_slash_le (k : ℤ) (A : R) (h : ℍ → ℂ) (τ : ℍ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ δ ∈ A.coeff.support, ‖(h ∣[k] δ) τ‖ ≤ L) :
    ‖slash k A h τ‖ ≤ coeffNorm A * L := by
  rw [slash_apply_eq_sum]
  calc ‖∑ δ ∈ A.coeff.support, A.coeff δ * (h ∣[k] δ) τ‖
      ≤ ∑ δ ∈ A.coeff.support, ‖A.coeff δ * (h ∣[k] δ) τ‖ := norm_sum_le _ _
    _ = ∑ δ ∈ A.coeff.support, ‖A.coeff δ‖ * ‖(h ∣[k] δ) τ‖ := by
        exact Finset.sum_congr rfl fun δ _ => norm_mul _ _
    _ ≤ ∑ δ ∈ A.coeff.support, ‖A.coeff δ‖ * L :=
        Finset.sum_le_sum fun δ hδ => mul_le_mul_of_nonneg_left (hL δ hδ) (norm_nonneg _)
    _ = (∑ δ ∈ A.coeff.support, ‖A.coeff δ‖) * L := by rw [Finset.sum_mul]
    _ = coeffNorm A * L := rfl

end Work.Asymptotics
