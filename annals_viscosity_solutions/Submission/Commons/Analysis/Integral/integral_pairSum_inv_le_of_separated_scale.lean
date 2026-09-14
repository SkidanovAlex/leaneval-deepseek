/-
Scaled version of `Commons.Analysis.Integral.integral_pairSum_inv_le_of_separated`.

The reference lemma (`integral_pairSum_inv_le_of_separated`) treats configurations
`z a : EuclideanSpace ℝ (Fin N)` with `‖a‖ = 1`.  Here we work in an arbitrary finite
dimensional real inner product space `F` (so `EuclideanSpace F (Fin N)`) and we replace the
normalisation `‖a‖ = 1` by a scale bound `‖a‖ ≤ K`.  The proof is the same: the angle
condition `(1/2)‖q‖‖e‖ ≤ ⟪q,e⟫` gives `‖q + s•e‖ ≥ ‖q‖ + s‖e‖/2`, the per-pair integral is
estimated against `∫_ν^{2KT+2‖z‖} t⁻¹`, and the `C(N,2)` pairs cost at most `N²`.
-/
import Submission.Commons.Analysis.Integral.integral_pairSum_inv_le_of_separated
import Mathlib.Analysis.Normed.Lp.PiLp

open MeasureTheory Set
open scoped BigOperators

namespace Commons.Analysis.Integral

theorem integral_pairSum_inv_le_of_separated_scale {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {N : ℕ} (hN : 2 ≤ N)
    (z a : EuclideanSpace F (Fin N)) {ν K : ℝ} (hν : 0 < ν) (hK : 0 < K) (ha : ‖a‖ ≤ K)
    (hsepa : ∀ i j, i ≠ j → ν ≤ ‖a i - a j‖) (hsepz : ∀ i j, i ≠ j → ν ≤ ‖z i - z j‖)
    (hangle : ∀ i j, i ≠ j →
      (1 / 2) * (‖z i - z j‖ * ‖a i - a j‖) ≤ inner ℝ (z i - z j) (a i - a j))
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ s in (0:ℝ)..T, ∑ j, ∑ i ∈ Finset.Iio j, (‖(z i - z j) + s • (a i - a j)‖)⁻¹
      ≤ (N:ℝ)^2 * (ν⁻¹ * ∫ t in ν..(2 * K * T + 2 * ‖z‖), t⁻¹) := by
  set M : ℝ := 2 * K * T + 2 * ‖z‖ with hMdef
  have hzi : ∀ i : Fin N, ‖z i‖ ≤ ‖z‖ := fun i => PiLp.norm_apply_le z i
  have hai : ∀ i : Fin N, ‖a i‖ ≤ K := fun i => le_trans (PiLp.norm_apply_le a i) ha
  have hbound : ∀ i j : Fin N, i ≠ j → ‖(z i - z j) + T • (a i - a j)‖ ≤ M := by
    intro i j _
    calc ‖(z i - z j) + T • (a i - a j)‖
        ≤ ‖z i - z j‖ + ‖T • (a i - a j)‖ := norm_add_le _ _
      _ = ‖z i - z j‖ + T * ‖a i - a j‖ := by rw [norm_smul, Real.norm_of_nonneg hT]
      _ ≤ (‖z‖ + ‖z‖) + T * (K + K) := by
            have h1 : ‖z i - z j‖ ≤ ‖z‖ + ‖z‖ :=
              le_trans (norm_sub_le _ _) (add_le_add (hzi i) (hzi j))
            have h2 : ‖a i - a j‖ ≤ K + K :=
              le_trans (norm_sub_le _ _) (add_le_add (hai i) (hai j))
            have h3 : T * ‖a i - a j‖ ≤ T * (K + K) := mul_le_mul_of_nonneg_left h2 hT
            linarith
      _ = M := by rw [hMdef]; ring
  have hpair : ∀ j : Fin N, ∀ i ∈ Finset.Iio j,
      ∫ s in (0:ℝ)..T, (‖(z i - z j) + s • (a i - a j)‖)⁻¹
        ≤ 2 * (ν⁻¹ * ∫ t in ν..M, t⁻¹) := by
    intro j i hi
    have hij : i ≠ j := ne_of_lt (Finset.mem_Iio.mp hi)
    have := integral_inv_norm_add_smul_le_inv_mul (q := z i - z j) (e := a i - a j)
      hν (hsepa i j hij) (hsepz i j hij) (hangle i j hij) hT (hbound i j hij)
    simpa only [mul_assoc] using this
  have hInt : ∀ i j : Fin N, i ≠ j →
      IntervalIntegrable (fun s : ℝ => (‖(z i - z j) + s • (a i - a j)‖)⁻¹) volume 0 T :=
    fun i j hij =>
      intervalIntegrable_inv_norm_add_smul hν (hsepa i j hij) (hsepz i j hij) (hangle i j hij) hT
  have hsplit : ∫ s in (0:ℝ)..T, (∑ j : Fin N, ∑ i ∈ Finset.Iio j,
        (‖(z i - z j) + s • (a i - a j)‖)⁻¹)
      = ∑ j : Fin N, ∑ i ∈ Finset.Iio j,
          ∫ s in (0:ℝ)..T, (‖(z i - z j) + s • (a i - a j)‖)⁻¹ := by
    have h1 : ∫ s in (0:ℝ)..T, (∑ j : Fin N, ∑ i ∈ Finset.Iio j,
          (‖(z i - z j) + s • (a i - a j)‖)⁻¹)
        = ∑ j : Fin N, ∫ s in (0:ℝ)..T, (∑ i ∈ Finset.Iio j,
            (‖(z i - z j) + s • (a i - a j)‖)⁻¹) := by
      refine intervalIntegral.integral_finsetSum (s := Finset.univ) (fun j _ => ?_)
      have hsum := IntervalIntegrable.sum (Finset.Iio j)
        (f := fun i => fun s : ℝ => (‖(z i - z j) + s • (a i - a j)‖)⁻¹)
        (fun i hi => hInt i j (ne_of_lt (Finset.mem_Iio.mp hi)))
      rw [show (fun s : ℝ => ∑ i ∈ Finset.Iio j, (‖(z i - z j) + s • (a i - a j)‖)⁻¹)
            = (∑ i ∈ Finset.Iio j, fun s : ℝ => (‖(z i - z j) + s • (a i - a j)‖)⁻¹) from by
              ext s
              rw [Finset.sum_apply]]
      exact hsum
    have h2 : ∀ j : Fin N, (∫ s in (0:ℝ)..T, (∑ i ∈ Finset.Iio j,
          (‖(z i - z j) + s • (a i - a j)‖)⁻¹))
        = ∑ i ∈ Finset.Iio j, ∫ s in (0:ℝ)..T, (‖(z i - z j) + s • (a i - a j)‖)⁻¹ := by
      intro j
      refine intervalIntegral.integral_finsetSum (fun i hi => ?_)
      exact hInt i j (ne_of_lt (Finset.mem_Iio.mp hi))
    rw [h1, Finset.sum_congr rfl (fun j _ => h2 j)]
  rw [hsplit]
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp
  have hνM : ν ≤ M := by
    have h1 : ν ≤ ‖z ⟨0, by omega⟩ - z ⟨1, by omega⟩‖ := hsepz _ _ h01
    have h2 : ‖z ⟨0, by omega⟩ - z ⟨1, by omega⟩‖ ≤ 2 * ‖z‖ := by
      calc ‖z ⟨0, by omega⟩ - z ⟨1, by omega⟩‖
          ≤ ‖z ⟨0, by omega⟩‖ + ‖z ⟨1, by omega⟩‖ := norm_sub_le _ _
        _ ≤ ‖z‖ + ‖z‖ := add_le_add (hzi _) (hzi _)
        _ = 2 * ‖z‖ := by ring
    have h3 : 2 * ‖z‖ ≤ M := by rw [hMdef]; nlinarith [mul_nonneg hK.le hT]
    linarith
  have hInn : 0 ≤ ∫ t in ν..M, t⁻¹ :=
    intervalIntegral.integral_nonneg hνM (fun u hu => inv_nonneg.mpr (le_trans hν.le hu.1))
  have hc : 0 ≤ ν⁻¹ * ∫ t in ν..M, t⁻¹ := mul_nonneg (inv_nonneg.mpr hν.le) hInn
  calc ∑ j : Fin N, ∑ i ∈ Finset.Iio j,
        ∫ s in (0:ℝ)..T, (‖(z i - z j) + s • (a i - a j)‖)⁻¹
      ≤ ∑ j : Fin N, ∑ i ∈ Finset.Iio j, 2 * (ν⁻¹ * ∫ t in ν..M, t⁻¹) :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i hi => hpair j i hi))
    _ ≤ (N:ℝ)^2 * (ν⁻¹ * ∫ t in ν..M, t⁻¹) := sum_Iio_two_mul_le N _ hc
    _ = (N:ℝ)^2 * (ν⁻¹ * ∫ t in ν..(2 * K * T + 2 * ‖z‖), t⁻¹) := by rw [hMdef]

end Commons.Analysis.Integral
