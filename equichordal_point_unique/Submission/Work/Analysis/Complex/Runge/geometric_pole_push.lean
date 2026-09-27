import Mathlib

/-!
# Pole pushing via the geometric series (first brick of the Runge approximation)

Classical Runge approximation replaces the poles of a rational function -- which lie outside the
compact set K -- by poles further away, uniformly on K.  The elementary tool is the geometric
expansion of the kernel: if the pole a lies in the open disc of radius R, then on the closed
exterior {z | R <= norm z} one has

    (z - a)^-1 = sum_n a^n / z^(n+1),

a series whose partial sums are rational functions with the single pole 0 instead of a, and whose
tails are bounded by (norm a / R)^N / (R - norm a).

* partialSum_sub_inv : the finite geometric identity
    sum_{n<N} a^n / z^(n+1) = (1 - a^N / z^N) / (z - a);
* tendstoUniformlyOn_partialSum_pole : uniform convergence of the partial sums to (z - a)^-1 on
  {z | R <= norm z}, whenever norm a < R.

Second brick (to come): the Cauchy-integral / partition step producing an approximation of a
function holomorphic on a neighbourhood of K by rational functions with poles outside K.
-/

open scoped Topology
open Filter Finset

noncomputable section

namespace Work.Analysis.Complex.Runge

/-- The finite geometric identity behind pole pushing. -/
theorem partialSum_sub_inv (a z : ℂ) (hz : z ≠ 0) (hza : z ≠ a) (N : ℕ) :
    (∑ n ∈ Finset.range N, a ^ n / z ^ (n + 1)) = (1 - a ^ N / z ^ N) / (z - a) := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [pow_succ]
    field_simp
    ring

/-- Uniform convergence of the pole-pushing partial sums. -/
theorem tendstoUniformlyOn_partialSum_pole {a : ℂ} {R : ℝ} (ha : ‖a‖ < R) :
    TendstoUniformlyOn (fun (N : ℕ) (z : ℂ) => ∑ n ∈ Finset.range N, a ^ n / z ^ (n + 1))
      (fun z : ℂ => (z - a)⁻¹) atTop {z : ℂ | R ≤ ‖z‖} := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg a) ha
  have hlt : ‖a‖ / R < 1 := (div_lt_one hR).mpr ha
  have hsubpos : 0 < R - ‖a‖ := sub_pos.mpr ha
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h0 : Tendsto (fun N : ℕ => (‖a‖ / R) ^ N / (R - ‖a‖)) atTop (nhds 0) := by
    have hb : Tendsto (fun N : ℕ => (‖a‖ / R) ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ ‖a‖ / R) hlt
    have hdiv := hb.div_const (R - ‖a‖)
    simpa using hdiv
  obtain ⟨N, hN⟩ := (h0.eventually (eventually_lt_nhds hε)).exists
  refine Filter.eventually_atTop.mpr ⟨N, fun M hM z hz => ?_⟩
  have hnorm : R ≤ ‖z‖ := hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [norm_zero] at hnorm
    linarith
  have hza : z ≠ a := by
    intro h
    rw [h] at hnorm
    linarith
  have hkey := partialSum_sub_inv a z hz0 hza M
  have hdiff : (z - a)⁻¹ - (∑ n ∈ Finset.range M, a ^ n / z ^ (n + 1))
      = a ^ M / (z ^ M * (z - a)) := by
    rw [hkey]
    field_simp
    ring
  rw [dist_eq_norm, hdiff, norm_div, norm_mul, norm_pow, norm_pow]
  have hsub : R - ‖a‖ ≤ ‖z - a‖ := by
    have h1 := norm_sub_norm_le z a
    linarith
  have hden : R ^ M * (R - ‖a‖) ≤ ‖z‖ ^ M * ‖z - a‖ := by
    have h1 : R ^ M * (R - ‖a‖) ≤ ‖z‖ ^ M * (R - ‖a‖) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR.le hnorm M) hsubpos.le
    have h2 : ‖z‖ ^ M * (R - ‖a‖) ≤ ‖z‖ ^ M * ‖z - a‖ :=
      mul_le_mul_of_nonneg_left hsub (by positivity)
    exact le_trans h1 h2
  have hdenpos : 0 < R ^ M * (R - ‖a‖) := by positivity
  calc ‖a‖ ^ M / (‖z‖ ^ M * ‖z - a‖)
      ≤ ‖a‖ ^ M / (R ^ M * (R - ‖a‖)) :=
        div_le_div_of_nonneg_left (by positivity) hdenpos hden
    _ = (‖a‖ / R) ^ M / (R - ‖a‖) := by
        rw [div_pow]
        field_simp
    _ ≤ (‖a‖ / R) ^ N / (R - ‖a‖) :=
        div_le_div_of_nonneg_right (pow_le_pow_of_le_one (by positivity) hlt.le hM) hsubpos.le
    _ < ε := hN

end Work.Analysis.Complex.Runge
