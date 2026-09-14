import Submission.NBody.LYZPsi
import Submission.NBody.LYZGeometry
import Submission.Commons.Analysis.Integral.integral_pairSum_inv_le_of_separated_scale
import Mathlib

/-!
# The potential integral along a ray (Liu--Yan--Zhou, Lemma 3.2)

If `z` and the direction `b` are both `ν`-separated and all the pairwise angles
`∠(zᵢ - zⱼ, bᵢ - bⱼ)` are at most `π/2`, then

    `∫₀^T U(z + t b) dt ≤ (∑ᵢ mᵢ)² N² ν⁻¹ ∫_ν^{2KT + 2|z|} dt/t`,

where `K` bounds the Euclidean norm of the direction.  This is the second ingredient of the
length bound of Liu--Yan--Zhou (their Corollary 3.2.2), and it is where the Newtonian
integrability of `1/|xᵢ - xⱼ|` is used.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

/-- Along a ray with non-negative pairwise angles the pair distances do not decrease, so the
configuration stays collision free and the potential is continuous. -/
lemma continuousOn_U_comp_add_smul {m : Fin N → ℝ} {z b : EN E N} {T : ℝ}
    (hsepz : ∀ i j, i ≠ j → 0 < ‖z i - z j‖)
    (hangle : ∀ i j, i ≠ j → 0 ≤ inner ℝ (z i - z j) (b i - b j)) :
    ContinuousOn (fun t : ℝ => U m (z + t • b)) (Set.Icc 0 T) := by
  have hnc : ∀ t ∈ Set.Icc (0:ℝ) T, WithoutCollisions (z + t • b) := by
    intro t ht i j hij
    have h1 := dist_add_smul_ge (z := z) (b := b) hangle ht.1 i j hij
    have h2 : 0 < dist (z i) (z j) := by
      simpa [dist_eq_norm] using hsepz i j hij
    have h3 : 0 < dist ((z + t • b) i) ((z + t • b) j) := lt_of_lt_of_le h2 h1
    show r (z + t • b) i j ≠ 0
    rw [r]
    exact ne_of_gt h3
  have hcont : ContinuousOn (fun t : ℝ => z + t • b) (Set.Icc 0 T) := by fun_prop
  exact continuousOn_U.comp hcont hnc

/-- **The potential integral along a ray.** -/
theorem potentialIntegral_le_log {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (hN : 2 ≤ N)
    {z b : EN E N} {ν K Msz T : ℝ} (hν : 0 < ν) (hK : 0 < K)
    (hKb : ‖b‖ ≤ K) (hKz : ‖z‖ ≤ Msz)
    (hsepz : ∀ i j, i ≠ j → ν ≤ ‖z i - z j‖)
    (hsepb : ∀ i j, i ≠ j → ν ≤ ‖b i - b j‖)
    (hangle : ∀ i j, i ≠ j →
      (1 / 2) * (‖z i - z j‖ * ‖b i - b j‖) ≤ inner ℝ (z i - z j) (b i - b j))
    (hT : 0 ≤ T) (hνz : ν ≤ 2 * K * T + 2 * ‖z‖) (hνM : ν ≤ 2 * K * T + 2 * Msz) :
    ∫ t in (0:ℝ)..T, U m (z + t • b) ≤
      (∑ i, m i) ^ 2 * (N:ℝ) ^ 2 * ν⁻¹ * (Real.log (2 * K * T + 2 * Msz) - Real.log ν) := by
  have hM0 : 0 ≤ ∑ i, m i := Finset.sum_nonneg fun i _ => hm i
  have hangle0 : ∀ i j, i ≠ j → 0 ≤ inner ℝ (z i - z j) (b i - b j) := by
    intro i j hij
    have h1 := hangle i j hij
    have h2 : 0 ≤ ‖z i - z j‖ * ‖b i - b j‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith
  have hsepzpos : ∀ i j, i ≠ j → 0 < ‖z i - z j‖ := by
    intro i j hij
    exact lt_of_lt_of_le hν (hsepz i j hij)
  -- pointwise bound by the extended pair sum
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) T,
      U m (z + t • b) ≤ (∑ i, m i) ^ 2 *
        (∑ j, ∑ i ∈ Finset.Iio j, (‖(z i - z j) + t • (b i - b j)‖)⁻¹) := by
    intro t ht
    have hpdist : ∀ i j : Fin N, i ≠ j → 0 < ‖(z i - z j) + t • (b i - b j)‖ := by
      intro i j hij
      have h1 : ‖z i - z j‖ ≤ ‖(z i - z j) + t • (b i - b j)‖ := by
        have h2 : 0 ≤ inner ℝ (z i - z j) (t • (b i - b j)) := by
          rw [real_inner_smul_right]
          exact mul_nonneg ht.1 (hangle0 i j hij)
        nlinarith [norm_add_sq_real (z i - z j) (t • (b i - b j)), norm_nonneg (z i - z j),
          norm_nonneg ((z i - z j) + t • (b i - b j))]
      exact lt_of_lt_of_le (hsepzpos i j hij) h1
    have hkey : U m (z + t • b)
        = ∑ j, ∑ i ∈ Finset.Iio j, m i * m j * (‖(z i - z j) + t • (b i - b j)‖)⁻¹ := by
      rw [U]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
      have hij : i ≠ j := ne_of_lt (Finset.mem_Iio.mp hi)
      have : (z + t • b) i - (z + t • b) j = (z i - z j) + t • (b i - b j) := by
        simp only [PiLp.add_apply, PiLp.smul_apply]
        module
      rw [r, dist_eq_norm, this]
    rw [hkey, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hij : i ≠ j := ne_of_lt (Finset.mem_Iio.mp hi)
    have hmi : m i ≤ ∑ k, m k := Finset.single_le_sum (fun k _ => hm k) (Finset.mem_univ i)
    have hmj : m j ≤ ∑ k, m k := Finset.single_le_sum (fun k _ => hm k) (Finset.mem_univ j)
    have hle : m i * m j ≤ (∑ k, m k) ^ 2 := by
      have h1 : m i * m j ≤ (∑ k, m k) * (∑ k, m k) := by
        exact mul_le_mul hmi hmj (hm j) hM0
      simpa [sq] using h1
    have h2 : 0 ≤ (‖(z i - z j) + t • (b i - b j)‖)⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    calc m i * m j * (‖(z i - z j) + t • (b i - b j)‖)⁻¹
        ≤ (∑ k, m k) ^ 2 * (‖(z i - z j) + t • (b i - b j)‖)⁻¹ :=
          mul_le_mul_of_nonneg_right hle h2
      _ = (∑ k, m k) ^ 2 * (‖(z i - z j) + t • (b i - b j)‖)⁻¹ := rfl
  -- integrability of both sides
  have hcontU : ContinuousOn (fun t : ℝ => U m (z + t • b)) (Set.Icc 0 T) :=
    continuousOn_U_comp_add_smul (m := m) hsepzpos hangle0
  have hcontR : ContinuousOn
      (fun t : ℝ => ∑ j, ∑ i ∈ Finset.Iio j, (‖(z i - z j) + t • (b i - b j)‖)⁻¹)
      (Set.Icc 0 T) := by
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun i hi => ?_
    have hij : i ≠ j := ne_of_lt (Finset.mem_Iio.mp hi)
    refine ContinuousOn.inv₀ ?_ ?_
    · have hlin : Continuous (fun t : ℝ => (z i - z j) + t • (b i - b j)) := by fun_prop
      exact (hlin.norm).continuousOn
    · intro t ht
      have h1 : ‖z i - z j‖ ≤ ‖(z i - z j) + t • (b i - b j)‖ := by
        have h2 : 0 ≤ inner ℝ (z i - z j) (t • (b i - b j)) := by
          rw [real_inner_smul_right]
          exact mul_nonneg ht.1 (hangle0 i j hij)
        nlinarith [norm_add_sq_real (z i - z j) (t • (b i - b j)), norm_nonneg (z i - z j),
          norm_nonneg ((z i - z j) + t • (b i - b j))]
      exact ne_of_gt (lt_of_lt_of_le (hsepzpos i j hij) h1)
  have hiU : IntervalIntegrable (fun t : ℝ => U m (z + t • b)) volume (0:ℝ) T :=
    hcontU.intervalIntegrable_of_Icc hT
  have hiR : IntervalIntegrable
      (fun t : ℝ => ∑ j, ∑ i ∈ Finset.Iio j, (‖(z i - z j) + t • (b i - b j)‖)⁻¹)
      volume (0:ℝ) T :=
    hcontR.intervalIntegrable_of_Icc hT
  have hmono := intervalIntegral.integral_mono_on hT hiU
    (hiR.const_mul ((∑ i, m i) ^ 2)) (fun t ht => by
      simpa [mul_comm] using hpt t ht)
  -- the extended pair-sum bound
  have hpair : ∫ s in (0:ℝ)..T, ∑ j, ∑ i ∈ Finset.Iio j, (‖(z i - z j) + s • (b i - b j)‖)⁻¹
      ≤ (N:ℝ) ^ 2 * (ν⁻¹ * ∫ t in ν..(2 * K * T + 2 * ‖z‖), t⁻¹) :=
    Commons.Analysis.Integral.integral_pairSum_inv_le_of_separated_scale (F := E) (N := N) hN z b hν hK hKb
      hsepb hsepz hangle hT
  -- enlarging the upper limit and evaluating the `t⁻¹` integral
  have hI1 : ∫ t in ν..(2 * K * T + 2 * ‖z‖), t⁻¹
      = Real.log (2 * K * T + 2 * ‖z‖) - Real.log ν := by
    rw [integral_inv (by
        rw [Set.mem_uIcc]; rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith),
      Real.log_div (by linarith) (ne_of_gt hν)]
  have hI2 : ∫ t in ν..(2 * K * T + 2 * Msz), t⁻¹
      = Real.log (2 * K * T + 2 * Msz) - Real.log ν := by
    rw [integral_inv (by
        rw [Set.mem_uIcc]; rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith),
      Real.log_div (by linarith) (ne_of_gt hν)]
  have hlog_le : Real.log (2 * K * T + 2 * ‖z‖) ≤ Real.log (2 * K * T + 2 * Msz) :=
    Real.log_le_log (by linarith) (by linarith)
  have hint_le : ∫ t in ν..(2 * K * T + 2 * ‖z‖), t⁻¹
      ≤ ∫ t in ν..(2 * K * T + 2 * Msz), t⁻¹ := by
    rw [hI1, hI2]; linarith
  calc ∫ t in (0:ℝ)..T, U m (z + t • b)
      ≤ (∑ i, m i) ^ 2 * ∫ t in (0:ℝ)..T,
          ∑ j, ∑ i ∈ Finset.Iio j, (‖(z i - z j) + t • (b i - b j)‖)⁻¹ := by
        rw [← intervalIntegral.integral_const_mul]
        exact hmono
    _ ≤ (∑ i, m i) ^ 2 * ((N:ℝ) ^ 2 * (ν⁻¹ * ∫ t in ν..(2 * K * T + 2 * ‖z‖), t⁻¹)) := by
        refine mul_le_mul_of_nonneg_left hpair (by positivity)
    _ ≤ (∑ i, m i) ^ 2 * ((N:ℝ) ^ 2 * (ν⁻¹ * ∫ t in ν..(2 * K * T + 2 * Msz), t⁻¹)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hint_le (inv_nonneg.mpr hν.le)
    _ = (∑ i, m i) ^ 2 * (N:ℝ) ^ 2 * ν⁻¹ * (Real.log (2 * K * T + 2 * Msz) - Real.log ν) := by
        rw [hI2]; ring

end Submission.NBody
