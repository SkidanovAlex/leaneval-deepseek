import Submission.NBody.MarchalBumpEstimates
import Submission.Commons.Analysis.Integral.potential_gain_bound_stdVar_measurable
import Submission.NBody.MarchalPairRatio

/-!
# The potential gain of the symmetric bump

Part of the assembly of Marchal's theorem (`Submission/ROADMAP.md`, SESSION 29): the *potential*
half of the action difference of the symmetric bump.

The symmetric bump moves `i₀` by `(1 - mᵢ₀/m_k)·v` and every other body of the cluster `k` by
`-(mᵢ₀/m_k)·v`, so the difference `qᵢ₀ - qⱼ` changes by exactly the standard variation
`stdVar δ T t`.  Hence the cluster potential difference is a sum over the pairs through `i₀`
(`clusterPotential_bump_diff`), and each pair's contribution is controlled by Ferrario--Terracini's
one-sided estimate (`Commons.Analysis.Integral.potential_gain_bound_stdVar_measurable`).

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

lemma clusterPotential_eq_double (m : Fin N → ℝ) (k : Finset (Fin N)) (y : EN E N) :
    clusterPotential m k y
      = ∑ i ∈ k, ∑ j ∈ k, (if i < j then m i * m j * (r y i j)⁻¹ else 0) := by
  rw [clusterPotential, Finset.sum_filter]
  simp only [pairFinset]
  rw [Finset.sum_filter]
  have hprod : (∑ a ∈ (Finset.univ : Finset (Fin N × Fin N)), (if a.1 < a.2 then
      (if a.1 ∈ k ∧ a.2 ∈ k then m a.1 * m a.2 * (r y a.1 a.2)⁻¹ else 0) else 0))
      = ∑ i ∈ (Finset.univ : Finset (Fin N)), ∑ j ∈ (Finset.univ : Finset (Fin N)),
          (if i < j then (if i ∈ k ∧ j ∈ k then m i * m j * (r y i j)⁻¹ else 0) else 0) := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [hprod]
  rw [← Finset.sum_subset (Finset.subset_univ k) (by
      intro i _ hi
      simp [hi])]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_subset (Finset.subset_univ k) (by
      intro j _ hj
      simp [hj])]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp [hi, hj]

/-- Splitting the potential into the pairs through `i₀` and the rest. -/
lemma clusterPotential_split (m : Fin N → ℝ) (k : Finset (Fin N)) {i₀ : Fin N} (hi₀ : i₀ ∈ k)
    (y : EN E N) :
    clusterPotential m k y
      = (∑ j ∈ k.erase i₀, m i₀ * m j * (r y i₀ j)⁻¹)
        + ∑ i ∈ k.erase i₀, ∑ j ∈ k.erase i₀,
            (if i < j then m i * m j * (r y i j)⁻¹ else 0) := by
  classical
  rw [clusterPotential_eq_double]
  rw [← Finset.add_sum_erase k (fun i => ∑ j ∈ k, (if i < j then m i * m j * (r y i j)⁻¹ else 0))
    hi₀]
  -- the i₀-row: drop the `j = i₀` term
  have hrow : (∑ j ∈ k, (if i₀ < j then m i₀ * m j * (r y i₀ j)⁻¹ else 0))
      = ∑ j ∈ k.erase i₀, (if i₀ < j then m i₀ * m j * (r y i₀ j)⁻¹ else 0) := by
    rw [← Finset.sum_subset (s₁ := k.erase i₀) (s₂ := k) (Finset.erase_subset _ _)]
    intro j hj hjn
    simp only [Finset.mem_erase, not_and] at hjn
    rw [if_neg]
    intro hlt
    exact hjn (ne_of_gt hlt) hj
  rw [hrow]
  -- each remaining row: split the inner sum at i₀
  have hroot : ∀ i ∈ k.erase i₀,
      (∑ j ∈ k, (if i < j then m i * m j * (r y i j)⁻¹ else 0))
        = (if i < i₀ then m i * m i₀ * (r y i i₀)⁻¹ else 0)
          + ∑ j ∈ k.erase i₀, (if i < j then m i * m j * (r y i j)⁻¹ else 0) := by
    intro i hi
    rw [← Finset.add_sum_erase k (fun j => (if i < j then m i * m j * (r y i j)⁻¹ else 0)) hi₀]
  have houter : (∑ i ∈ k.erase i₀, ∑ j ∈ k, (if i < j then m i * m j * (r y i j)⁻¹ else 0))
      = (∑ i ∈ k.erase i₀, (if i < i₀ then m i * m i₀ * (r y i i₀)⁻¹ else 0))
        + ∑ i ∈ k.erase i₀, ∑ j ∈ k.erase i₀,
            (if i < j then m i * m j * (r y i j)⁻¹ else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hroot
  rw [houter, ← add_assoc]
  congr 1
  -- the combination
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_erase] at hj
  have hne : r y j i₀ = r y i₀ j := by
    rw [r_eq_norm_sub, r_eq_norm_sub, norm_sub_rev]
  by_cases hlt : i₀ < j
  · rw [if_pos hlt, if_neg (not_lt.mpr hlt.le), add_zero]
  · rw [if_neg hlt]
    have hlt' : j < i₀ := lt_of_le_of_ne (le_of_not_gt hlt) hj.1
    rw [if_pos hlt', zero_add, hne, mul_comm (m j) (m i₀)]

end Submission.NBody

namespace Submission.NBody

lemma stdPertVec_sub_of_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ i j : Fin N}
    (hi : i ∈ k) (hj : j ∈ k) (hii : i ≠ i₀) (hjj : j ≠ i₀) (v : E) :
    stdPertVec m k i₀ v i = stdPertVec m k i₀ v j := by
  rw [stdPertVec_apply_of_mem hi, stdPertVec_apply_of_mem hj, if_neg hii, if_neg hjj]

/-- The difference of two coordinates of the rescaled standard perturbation is the standard
variation of the displacement of `i₀` relative to `j`. -/
lemma stdPert_sub_i₀ {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ j : Fin N} (hi₀ : i₀ ∈ k)
    (hj : j ∈ k) (hjne : j ≠ i₀) (δ : E) (T t : ℝ) :
    stdPert m k i₀ δ T t i₀ - stdPert m k i₀ δ T t j = stdVar δ T t := by
  rw [stdPert_eq_smul_stdPertVec, PiLp.smul_apply (fun _ : Fin N => E),
    PiLp.smul_apply (fun _ : Fin N => E), ← smul_sub, stdPertVec_sub_i₀ hi₀ hj hjne,
    stdVar]

/-- The difference of two coordinates not involving `i₀` is unchanged by the perturbation. -/
lemma stdPert_coord_sub_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ i j : Fin N}
    (hi : i ∈ k) (hj : j ∈ k) (hii : i ≠ i₀) (hjj : j ≠ i₀) (δ : E) (T t : ℝ) :
    stdPert m k i₀ δ T t i - stdPert m k i₀ δ T t j = 0 := by
  rw [stdPert_eq_smul_stdPertVec, PiLp.smul_apply (fun _ : Fin N => E),
    PiLp.smul_apply (fun _ : Fin N => E), ← smul_sub,
    stdPertVec_sub_of_notMem hi hj hii hjj, sub_self, smul_zero]

end Submission.NBody

namespace Submission.NBody

/-- **The potential difference of the symmetric bump.**  The symmetric bump only changes the
difference between `i₀` and the other bodies of the cluster, and changes it exactly by the standard
variation `stdVar δ T t`. -/
lemma clusterPotential_bump_diff (m : Fin N → ℝ) (k : Finset (Fin N)) {i₀ : Fin N} (hi₀ : i₀ ∈ k)
    (q : EN E N) (δ : E) (T t : ℝ) :
    clusterPotential m k (q + stdPert m k i₀ δ T t) - clusterPotential m k q
      = ∑ j ∈ k.erase i₀, m i₀ * m j *
          ((‖(q i₀ - q j) + stdVar δ T t‖)⁻¹ - (‖q i₀ - q j‖)⁻¹) := by
  classical
  have hR : (∑ i ∈ k.erase i₀, ∑ j ∈ k.erase i₀,
        (if i < j then m i * m j * (r (q + stdPert m k i₀ δ T t) i j)⁻¹ else 0))
      = ∑ i ∈ k.erase i₀, ∑ j ∈ k.erase i₀,
        (if i < j then m i * m j * (r q i j)⁻¹ else 0) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_erase] at hi hj
    have hsub : stdPert m k i₀ δ T t i = stdPert m k i₀ δ T t j :=
      sub_eq_zero.mp (stdPert_coord_sub_notMem hi.2 hj.2 hi.1 hj.1 δ T t)
    have hzero : (q + stdPert m k i₀ δ T t) i - (q + stdPert m k i₀ δ T t) j = q i - q j := by
      rw [PiLp.add_apply, PiLp.add_apply, hsub]
      abel
    rw [r_eq_norm_sub, r_eq_norm_sub, hzero]
  have hPhi : (∑ j ∈ k.erase i₀, m i₀ * m j * (r (q + stdPert m k i₀ δ T t) i₀ j)⁻¹)
      - (∑ j ∈ k.erase i₀, m i₀ * m j * (r q i₀ j)⁻¹)
      = ∑ j ∈ k.erase i₀, m i₀ * m j *
          ((‖(q i₀ - q j) + stdVar δ T t‖)⁻¹ - (‖q i₀ - q j‖)⁻¹) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_erase] at hj
    have heq : (q + stdPert m k i₀ δ T t) i₀ - (q + stdPert m k i₀ δ T t) j
        = (q i₀ - q j) + stdVar δ T t := by
      rw [PiLp.add_apply, PiLp.add_apply]
      rw [show q.ofLp i₀ + (stdPert m k i₀ δ T t).ofLp i₀ - (q.ofLp j + (stdPert m k i₀ δ T t).ofLp j)
          = (q.ofLp i₀ - q.ofLp j)
              + ((stdPert m k i₀ δ T t).ofLp i₀ - (stdPert m k i₀ δ T t).ofLp j) from by abel,
        stdPert_sub_i₀ hi₀ hj.2 hj.1 δ T t]
    rw [r_eq_norm_sub, r_eq_norm_sub, heq]
    ring
  rw [clusterPotential_split m k hi₀ (q + stdPert m k i₀ δ T t),
      clusterPotential_split m k hi₀ q, hR, add_sub_add_right_eq_sub, hPhi]

end Submission.NBody

namespace Submission.NBody

/-- The standard variation written with an explicit case distinction. -/
lemma stdVar_eq_ite {δ : E} (hδ : δ ≠ 0) (T t : ℝ) :
    stdVar δ T t = if t ≤ T - ‖δ‖ then δ else if t ≤ T then ((T - t) / ‖δ‖) • δ else 0 := by
  by_cases h1 : t ≤ T - ‖δ‖
  · rw [if_pos h1, stdVar_of_le hδ h1]
  · rw [if_neg h1]
    by_cases h2 : t ≤ T
    · rw [if_pos h2, stdVar_of_mem hδ (le_of_not_ge h1) h2]
    · rw [if_neg h2, stdVar_of_ge hδ (le_of_not_ge h2)]

end Submission.NBody

namespace Submission.NBody

/-- **The potential gain of the symmetric bump** (rescaled form).  Under the two-sided bounds and
the outward-sign condition for every pair through `i₀`, the potential difference produced by the
symmetric bump is bounded by `-(mass) * Θ(‖δ‖^{1/2}) + (mass) * Θ(‖δ‖)`. -/
theorem bump_potential_bound {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    (hi₀ : i₀ ∈ k) (δ : E) (hδ : δ ≠ 0) {T c C : ℝ} (hT : 0 < T) (hc : 0 < c) (hCc : c < C)
    (hδT : ‖δ‖ ≤ T / 4) (htA : (‖δ‖ / C) ^ ((3:ℝ)/2) ≤ T / 2)
    (htB : (‖δ‖ / c) ^ ((3:ℝ)/2) ≤ T / 2) (q : ℝ → EN E N)
    (hbound : ∀ t ∈ Set.Ioc (0:ℝ) T, ∀ j ∈ k.erase i₀,
      c * t ^ ((2:ℝ)/3) ≤ ‖q t i₀ - q t j‖ ∧ ‖q t i₀ - q t j‖ ≤ C * t ^ ((2:ℝ)/3))
    (hsign : ∀ t ∈ Set.Ioc (0:ℝ) T, ∀ j ∈ k.erase i₀, 0 ≤ inner ℝ (q t i₀ - q t j) δ)
    (hmeas : ∀ j ∈ k.erase i₀,
      MeasureTheory.AEStronglyMeasurable (fun t => q t i₀ - q t j)
        (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T)))
    (hint : ∀ j ∈ k.erase i₀, IntervalIntegrable
      (fun t => (‖(q t i₀ - q t j) + stdVar δ T t‖)⁻¹ - (‖q t i₀ - q t j‖)⁻¹)
      MeasureTheory.volume (0:ℝ) T) :
    ∫ t in (0:ℝ)..T, (clusterPotential m k (q t + stdPert m k i₀ δ T t) - clusterPotential m k (q t))
      ≤ -(∑ j ∈ k.erase i₀, m i₀ * m j)
          * (‖δ‖ ^ ((1:ℝ)/2) * (1 - c ^ 2 / C ^ 2) / (2 * C ^ ((3:ℝ)/2)))
        + (∑ j ∈ k.erase i₀, m i₀ * m j)
          * (2 * ‖δ‖ / (c * (T / 2) ^ ((2:ℝ)/3))) := by
  set A : ℝ := -‖δ‖ ^ ((1:ℝ)/2) * (1 - c ^ 2 / C ^ 2) / (2 * C ^ ((3:ℝ)/2)) with hA
  set B : ℝ := 2 * ‖δ‖ / (c * (T / 2) ^ ((2:ℝ)/3)) with hB
  have hpt : ∀ t : ℝ,
      clusterPotential m k (q t + stdPert m k i₀ δ T t) - clusterPotential m k (q t)
        = ∑ j ∈ k.erase i₀, m i₀ * m j *
            ((‖(q t i₀ - q t j) + stdVar δ T t‖)⁻¹ - (‖q t i₀ - q t j‖)⁻¹) :=
    fun t => clusterPotential_bump_diff m k hi₀ (q t) δ T t
  have hpair : ∀ j ∈ k.erase i₀,
      ∫ t in (0:ℝ)..T, ((‖(q t i₀ - q t j) + stdVar δ T t‖)⁻¹ - (‖q t i₀ - q t j‖)⁻¹) ≤ A + B := by
    intro j hj
    have h1 := Commons.Analysis.Integral.potential_gain_bound_stdVar_measurable
      (fun t : ℝ => q t i₀ - q t j) δ T c C hT hc hCc hδ hδT htA htB
      (fun t ht => hbound t ht j hj) (fun t ht => hsign t ht j hj) (hmeas j hj)
    rw [show (∫ t in (0:ℝ)..T,
          (‖(q t i₀ - q t j) + (if t ≤ T - ‖δ‖ then δ else if t ≤ T then ((T - t) / ‖δ‖) • δ else 0)‖)⁻¹
            - (‖q t i₀ - q t j‖)⁻¹)
        = ∫ t in (0:ℝ)..T, ((‖(q t i₀ - q t j) + stdVar δ T t‖)⁻¹ - (‖q t i₀ - q t j‖)⁻¹) from
      intervalIntegral.integral_congr (fun t _ => by rw [stdVar_eq_ite hδ])] at h1
    rw [hA, hB]
    exact h1
  have hsplt : ∫ t in (0:ℝ)..T, (clusterPotential m k (q t + stdPert m k i₀ δ T t)
        - clusterPotential m k (q t))
      = ∑ j ∈ k.erase i₀, m i₀ * m j *
          ∫ t in (0:ℝ)..T, ((‖(q t i₀ - q t j) + stdVar δ T t‖)⁻¹ - (‖q t i₀ - q t j‖)⁻¹) := by
    rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [intervalIntegral.integral_const_mul]
    · intro j hj
      exact (hint j hj).const_mul _
  rw [hsplt]
  calc ∑ j ∈ k.erase i₀, m i₀ * m j *
        ∫ t in (0:ℝ)..T, ((‖(q t i₀ - q t j) + stdVar δ T t‖)⁻¹ - (‖q t i₀ - q t j‖)⁻¹)
      ≤ ∑ j ∈ k.erase i₀, m i₀ * m j * (A + B) :=
        Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_left (hpair j hj) (mul_nonneg (hm i₀).le (hm j).le)
    _ = (∑ j ∈ k.erase i₀, m i₀ * m j) * (A + B) := by
        rw [Finset.sum_mul]
    _ = -(∑ j ∈ k.erase i₀, m i₀ * m j)
          * (‖δ‖ ^ ((1:ℝ)/2) * (1 - c ^ 2 / C ^ 2) / (2 * C ^ ((3:ℝ)/2)))
        + (∑ j ∈ k.erase i₀, m i₀ * m j)
          * (2 * ‖δ‖ / (c * (T / 2) ^ ((2:ℝ)/3))) := by
        rw [hA, hB]; ring

end Submission.NBody

