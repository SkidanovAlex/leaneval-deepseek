import Mathlib
import Submission.Commons.Analysis.MeasureTheory.polar_integral
import Submission.Commons.Analysis.Gaussian.euclidean_gaussian_integral_pi
import Submission.Commons.Measure.Integral.integrable_exp_neg_mul_sq_norm_scaled
import Submission.Commons.GeometryOfNumbers.brunn_minkowski_add
import Submission.Commons.GeometryOfNumbers.volume_real_le_integral_support

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Pointwise Real Topology

namespace Commons.GeometryOfNumbers

section SupportFunction

variable {n : ℕ}

/-- The support function of a set `K` in direction `u`,
`sSup {⟨y, u⟩ | y ∈ K}`. -/
noncomputable def supp (K : Set (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun y => inner ℝ y u) '' K)

variable {K : Set (EuclideanSpace ℝ (Fin n))} {R : ℝ}

lemma bddAbove_supp_image (hR : ∀ y ∈ K, ‖y‖ ≤ R) (u : EuclideanSpace ℝ (Fin n)) :
    BddAbove ((fun y => inner ℝ y u) '' K) :=
  ⟨R * ‖u‖, by
    rintro b ⟨y, hy, rfl⟩
    exact le_trans (real_inner_le_norm y u) (mul_le_mul_of_nonneg_right (hR y hy) (norm_nonneg u))⟩

lemma supp_le_of_norm_le (hne : K.Nonempty) (hR : ∀ y ∈ K, ‖y‖ ≤ R)
    (u : EuclideanSpace ℝ (Fin n)) : supp K u ≤ R * ‖u‖ := by
  rw [supp]
  refine csSup_le (hne.image _) ?_
  rintro b ⟨y, hy, rfl⟩
  exact le_trans (real_inner_le_norm y u) (mul_le_mul_of_nonneg_right (hR y hy) (norm_nonneg u))

lemma neg_mul_norm_le_supp (hne : K.Nonempty) (hR : ∀ y ∈ K, ‖y‖ ≤ R)
    (u : EuclideanSpace ℝ (Fin n)) : -(R * ‖u‖) ≤ supp K u := by
  obtain ⟨y₀, hy₀⟩ := hne
  have h1 : -(R * ‖u‖) ≤ inner ℝ y₀ u := by
    have h3 : -(R * ‖u‖) ≤ -(‖y₀‖ * ‖u‖) := by
      have : ‖y₀‖ * ‖u‖ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right (hR y₀ hy₀) (norm_nonneg u)
      linarith
    have h2 : -(‖y₀‖ * ‖u‖) ≤ inner ℝ y₀ u := by
      have := abs_real_inner_le_norm y₀ u
      linarith [neg_abs_le (inner ℝ y₀ u)]
    linarith
  rw [supp]
  exact le_trans h1 (le_csSup (bddAbove_supp_image hR u) ⟨y₀, hy₀, rfl⟩)

lemma abs_supp_le (hne : K.Nonempty) (hR : ∀ y ∈ K, ‖y‖ ≤ R) (u : EuclideanSpace ℝ (Fin n)) :
    |supp K u| ≤ R * ‖u‖ :=
  abs_le.mpr ⟨neg_mul_norm_le_supp hne hR u, supp_le_of_norm_le hne hR u⟩

lemma supp_sub_le (hne : K.Nonempty) (hR : ∀ y ∈ K, ‖y‖ ≤ R) (u v : EuclideanSpace ℝ (Fin n)) :
    supp K u ≤ supp K v + R * ‖u - v‖ := by
  rw [supp]
  refine csSup_le (hne.image _) ?_
  rintro b ⟨y, hy, rfl⟩
  have h1 : inner ℝ y u = inner ℝ y v + inner ℝ y (u - v) := by
    rw [← inner_add_right]; congr 1; abel
  have h2 : inner ℝ y v ≤ supp K v := by
    rw [supp]; exact le_csSup (bddAbove_supp_image hR v) ⟨y, hy, rfl⟩
  have h3 : inner ℝ y (u - v) ≤ R * ‖u - v‖ :=
    le_trans (real_inner_le_norm y (u - v)) (mul_le_mul_of_nonneg_right (hR y hy) (norm_nonneg _))
  linarith

lemma abs_supp_sub_le (hne : K.Nonempty) (hR : ∀ y ∈ K, ‖y‖ ≤ R)
    (u v : EuclideanSpace ℝ (Fin n)) : |supp K u - supp K v| ≤ R * ‖u - v‖ := by
  rw [abs_sub_le_iff]
  refine ⟨by linarith [supp_sub_le hne hR u v], ?_⟩
  have h := supp_sub_le hne hR v u
  rw [norm_sub_rev] at h
  linarith

lemma lipschitzWith_supp (hne : K.Nonempty) (hR : ∀ y ∈ K, ‖y‖ ≤ R) :
    LipschitzWith (Real.toNNReal R) (supp K) := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR _ hne.some_mem)
  refine LipschitzWith.of_dist_le_mul ?_
  intro u v
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal R hR0]
  exact abs_supp_sub_le hne hR u v

lemma continuous_supp (hne : K.Nonempty) (hR : ∀ y ∈ K, ‖y‖ ≤ R) :
    Continuous (supp K) :=
  (lipschitzWith_supp hne hR).continuous

end SupportFunction

end Commons.GeometryOfNumbers

namespace Commons.GeometryOfNumbers

section Main

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

lemma supp_ball (u : E) : supp (Metric.ball (0 : E) 1) u = ‖u‖ := by
  rw [supp]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (Set.Nonempty.image _ ⟨0, by rw [Metric.mem_ball]; simp⟩) ?_ ?_
  · rintro a ⟨y, hy, rfl⟩
    have hy1 : ‖y‖ ≤ 1 := le_of_lt (by rw [Metric.mem_ball, dist_zero_right] at hy; exact hy)
    calc inner ℝ y u ≤ ‖y‖ * ‖u‖ := real_inner_le_norm y u
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hy1 (norm_nonneg u)
      _ = ‖u‖ := one_mul _
  · intro w hw
    rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
    · refine ⟨0, ⟨0, by rw [Metric.mem_ball]; simp, by simp⟩, ?_⟩
      rw [← h0] at hw; simpa using hw
    · obtain ⟨t, ht1, ht2⟩ := exists_between (show max w 0 < ‖u‖ from max_lt hw hpos)
      have ht0 : 0 < t := lt_of_le_of_lt (le_max_right w 0) ht1
      have hu2 : (0:ℝ) < ‖u‖ ^ 2 := pow_pos hpos 2
      have hnorm : ‖(t / ‖u‖ ^ 2) • u‖ = t / ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ht0 hu2)]
        field_simp
      have hinner : inner ℝ ((t / ‖u‖ ^ 2) • u) u = t := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp
      refine ⟨t, ⟨(t / ‖u‖ ^ 2) • u, ?_, hinner⟩, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, hnorm]
        exact (div_lt_one hpos).mpr ht2
      · exact lt_of_le_of_lt (le_max_left w 0) ht1


lemma norm_coe_sphere {θ : Metric.sphere (0 : E) 1} : ‖(θ : E)‖ = 1 := by
  have h := θ.2
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
  exact h

lemma norm_dir {θ : E} (hθ : ‖θ‖ = 1) {r : ℝ} (hr : 0 < r) : ‖r • θ‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hθ, mul_one]

lemma supp_dir {K : Set E} {θ : E} (hθ : ‖θ‖ = 1) {r : ℝ} (hr : 0 < r) :
    supp K ((‖r • θ‖)⁻¹ • (r • θ)) = supp K θ := by
  have h1 : ‖r • θ‖ = r := norm_dir hθ hr
  rw [h1, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

lemma integrable_dir_supp {K : Set E} (hne : K.Nonempty) {R : ℝ} (hR : ∀ y ∈ K, ‖y‖ ≤ R) :
    Integrable (fun x : E => supp K ((‖x‖)⁻¹ • x) * Real.exp (-Real.pi * ‖x‖ ^ 2)) volume := by
  have hExp : Integrable (fun x : E => Real.exp (-Real.pi * ‖x‖ ^ 2)) volume := by
    have h := Commons.Measure.Integral.integrable_exp_neg_mul_sq_norm_scaled
      (V := E) Real.pi_pos (1 : ℝ) one_ne_zero
    simpa using h
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR _ hne.some_mem)
  have hmeas1 : Measurable (fun x : E => supp K ((‖x‖)⁻¹ • x)) :=
    (continuous_supp hne hR).measurable.comp ((measurable_norm.inv).smul measurable_id)
  have hmeas : AEStronglyMeasurable
      (fun x : E => supp K ((‖x‖)⁻¹ • x) * Real.exp (-Real.pi * ‖x‖ ^ 2)) volume :=
    (hmeas1.mul (by fun_prop : Measurable (fun x : E => Real.exp (-Real.pi * ‖x‖ ^ 2)))).aestronglyMeasurable
  refine Integrable.mono' (hExp.const_mul R) hmeas ?_
  filter_upwards with x
  have hdir : ‖(‖x‖)⁻¹ • x‖ ≤ 1 := by
    calc ‖(‖x‖)⁻¹ • x‖ = |(‖x‖)⁻¹| * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = (‖x‖)⁻¹ * ‖x‖ := by rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      _ ≤ 1 := by
          rcases eq_or_ne x 0 with rfl | hx
          · simp
          · exact le_of_eq (inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx))
  have hbound : |supp K ((‖x‖)⁻¹ • x)| ≤ R := by
    calc |supp K ((‖x‖)⁻¹ • x)| ≤ R * ‖(‖x‖)⁻¹ • x‖ := abs_supp_le hne hR _
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left hdir hR0
      _ = R := mul_one R
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le


lemma integral_dir_supp (hn : 0 < n) {K : Set E} (hne : K.Nonempty) {R : ℝ}
    (hR : ∀ y ∈ K, ‖y‖ ≤ R) :
    (∫ x : E, supp K ((‖x‖)⁻¹ • x) * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = (∫ r : Set.Ioi (0 : ℝ), Real.exp (-Real.pi * (r : ℝ) ^ 2)
            ∂(Measure.volumeIoiPow (n - 1)))
        * (∫ θ : Metric.sphere (0 : E) 1, supp K (θ : E)
            ∂(MeasureTheory.volume.toSphere)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hInt := integrable_dir_supp hne hR
  rw [Commons.Analysis.MeasureTheory.polar_integral E
      (fun x : E => supp K ((‖x‖)⁻¹ • x) * Real.exp (-Real.pi * ‖x‖ ^ 2)) hInt]
  simp only [finrank_euclideanSpace_fin]
  rw [show (∫ θ : Metric.sphere (0 : E) 1,
        ∫ r : Set.Ioi (0 : ℝ),
          supp K ((‖(r : ℝ) • (θ : E)‖)⁻¹ • ((r : ℝ) • (θ : E)))
            * Real.exp (-Real.pi * ‖(r : ℝ) • (θ : E)‖ ^ 2)
          ∂(Measure.volumeIoiPow (n - 1)) ∂(MeasureTheory.volume.toSphere))
      = ∫ θ : Metric.sphere (0 : E) 1,
          (∫ r : Set.Ioi (0 : ℝ), Real.exp (-Real.pi * (r : ℝ) ^ 2)
              ∂(Measure.volumeIoiPow (n - 1))) * supp K (θ : E)
          ∂(MeasureTheory.volume.toSphere) from ?_]
  · rw [integral_const_mul]
  · refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only []
    rw [show (fun r : Set.Ioi (0 : ℝ) =>
          supp K ((‖(r : ℝ) • (θ : E)‖)⁻¹ • ((r : ℝ) • (θ : E)))
            * Real.exp (-Real.pi * ‖(r : ℝ) • (θ : E)‖ ^ 2))
        = (fun r : Set.Ioi (0 : ℝ) =>
            Real.exp (-Real.pi * (r : ℝ) ^ 2) * supp K (θ : E)) from funext fun r => ?_]
    · rw [integral_mul_const]
    · have hθ := norm_coe_sphere (θ := θ)
      have hr : 0 < (r : ℝ) := r.2
      rw [show ‖(r : ℝ) • (θ : E)‖ ^ 2 = (r : ℝ) ^ 2 by rw [norm_dir hθ hr, sq]]
      rw [supp_dir hθ hr]
      ring


lemma integral_gauss_radial (hn : 0 < n) :
    (∫ r : Set.Ioi (0 : ℝ), Real.exp (-Real.pi * (r : ℝ) ^ 2)
        ∂(Measure.volumeIoiPow (n - 1)))
      = ((n : ℝ) * volume.real (Metric.ball (0 : E) 1))⁻¹ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hExpInt : Integrable (fun x : E => Real.exp (-Real.pi * ‖x‖ ^ 2)) volume := by
    have h := Commons.Measure.Integral.integrable_exp_neg_mul_sq_norm_scaled
      (V := E) Real.pi_pos (1 : ℝ) one_ne_zero
    simpa using h
  have hgauss : (∫ x : E, Real.exp (-Real.pi * ‖x‖ ^ 2)) = 1 := by
    have h := Commons.Analysis.Gaussian.euclidean_gaussian_integral_pi n 1 one_pos
    simpa using h
  have hsigma : (MeasureTheory.volume.toSphere :
        Measure (Metric.sphere (0 : E) 1)).real univ
      = (n : ℝ) * volume.real (Metric.ball (0 : E) 1) := by
    rw [Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
  have key : (∫ x : E, Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ((n : ℝ) * volume.real (Metric.ball (0 : E) 1))
        * (∫ r : Set.Ioi (0 : ℝ), Real.exp (-Real.pi * (r : ℝ) ^ 2)
            ∂(Measure.volumeIoiPow (n - 1))) := by
    rw [Commons.Analysis.MeasureTheory.polar_integral E
      (fun x : E => Real.exp (-Real.pi * ‖x‖ ^ 2)) hExpInt]
    simp only [finrank_euclideanSpace_fin]
    rw [show (∫ θ : Metric.sphere (0 : E) 1,
          ∫ r : Set.Ioi (0 : ℝ), Real.exp (-Real.pi * ‖(r : ℝ) • (θ : E)‖ ^ 2)
            ∂(Measure.volumeIoiPow (n - 1)) ∂(MeasureTheory.volume.toSphere))
        = ∫ θ : Metric.sphere (0 : E) 1,
            (∫ r : Set.Ioi (0 : ℝ), Real.exp (-Real.pi * (r : ℝ) ^ 2)
              ∂(Measure.volumeIoiPow (n - 1))) ∂(MeasureTheory.volume.toSphere)
        from ?_]
    · rw [integral_const, hsigma]
      simp [smul_eq_mul]
    · refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only []
      congr 1
      ext r
      rw [show ‖(r : ℝ) • (θ : E)‖ ^ 2 = (r : ℝ) ^ 2 by
        rw [norm_dir (norm_coe_sphere (θ := θ)) r.2, sq]]
  have hone : ((n : ℝ) * volume.real (Metric.ball (0 : E) 1))
      * (∫ r : Set.Ioi (0 : ℝ), Real.exp (-Real.pi * (r : ℝ) ^ 2)
          ∂(Measure.volumeIoiPow (n - 1))) = 1 := by
    rw [← key, hgauss]
  exact eq_inv_of_mul_eq_one_right hone

section Core

lemma volume_real_closedBall_eq_ball (hn : 0 < n) :
    volume.real (Metric.closedBall (0 : E) 1) = volume.real (Metric.ball (0 : E) 1) := by
  haveI : Nontrivial E := by haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩; infer_instance
  rw [Measure.real_def, Measure.real_def, Measure.addHaar_closedBall_eq_addHaar_ball volume 0 1]

lemma supp_closedBall (u : E) : supp (Metric.closedBall (0 : E) 1) u = ‖u‖ := by
  rw [supp]
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (Set.Nonempty.image _ ⟨0, by simp⟩) ?_ ?_
  · rintro a ⟨y, hy, rfl⟩
    have hy1 : ‖y‖ ≤ 1 := by rw [Metric.mem_closedBall, dist_zero_right] at hy; exact hy
    calc inner ℝ y u ≤ ‖y‖ * ‖u‖ := real_inner_le_norm y u
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hy1 (norm_nonneg u)
      _ = ‖u‖ := one_mul _
  · intro w hw
    rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
    · refine ⟨0, ⟨0, by simp, by simp⟩, ?_⟩
      rw [← h0] at hw; simpa using hw
    · have hmem : (‖u‖⁻¹) • u ∈ Metric.closedBall (0 : E) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)), inv_mul_cancel₀ hpos.ne']
      have hinner : inner ℝ ((‖u‖⁻¹) • u) u = ‖u‖ := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp
      exact ⟨‖u‖, ⟨(‖u‖⁻¹) • u, hmem, hinner⟩, hw⟩

lemma pow_one_add_sub_one_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n - 1 ≤ (n : ℝ) * u * (1 + u) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp
  · have h1u : 1 ≤ 1 + u := by linarith
    have hgeom : (∑ i ∈ Finset.range n, (1 + u) ^ i) * u = (1 + u) ^ n - 1 := by
      have h := geom_sum_mul (1 + u) n
      rwa [show (1 + u) - 1 = u by ring] at h
    rw [← hgeom]
    calc (∑ i ∈ Finset.range n, (1 + u) ^ i) * u
        ≤ ((n : ℝ) * (1 + u) ^ (n - 1)) * u := by
          apply mul_le_mul_of_nonneg_right _ hu
          calc ∑ i ∈ Finset.range n, (1 + u) ^ i
              ≤ ∑ _i ∈ Finset.range n, (1 + u) ^ (n - 1) := by
                apply Finset.sum_le_sum
                intro i hi
                rw [Finset.mem_range] at hi
                exact pow_le_pow_right₀ h1u (by omega)
            _ = (n : ℝ) * (1 + u) ^ (n - 1) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = (n : ℝ) * u * (1 + u) ^ (n - 1) := by ring

theorem urysohn_core (hn : 0 < n) (K : Set E)
    (hKcvx : Convex ℝ K) (hKcpt : IsCompact K) (hKsymm : (-K : Set E) = K)
    (hvol : volume.real K = 1) :
    (n : ℝ) * (volume.real (Metric.ball (0 : E) 1)) ^ (((n : ℝ) - 1) / (n : ℝ))
      ≤ ∫ θ : Metric.sphere (0 : E) 1, supp K (θ : E) ∂(MeasureTheory.volume.toSphere) := by
  haveI : Nontrivial E := by haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩; infer_instance
  have hnne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hKne : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h
    rw [h] at hvol; simp at hvol
  have h0K : (0 : E) ∈ K := by
    obtain ⟨y, hy⟩ := hKne
    have hy' : -y ∈ K := by rw [← hKsymm, Set.mem_neg]; simpa using hy
    have hc := hKcvx hy hy' (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1:ℝ)/2 + 1/2 = 1)
    simpa using hc
  have hKfin : volume K ≠ ⊤ := by
    intro h; rw [Measure.real_def, h] at hvol; simp at hvol
  obtain ⟨y₀, hy₀, hmax⟩ := hKcpt.exists_isMaxOn hKne continuous_norm.continuousOn
  set R : ℝ := ‖y₀‖ with hRdef
  have hR : ∀ y ∈ K, ‖y‖ ≤ R := fun y hy => hmax hy
  have hR0 : 0 ≤ R := norm_nonneg _
  set B : Set E := Metric.closedBall (0 : E) 1 with hBdef
  set V : ℝ := volume.real (Metric.ball (0 : E) 1) with hVdef
  have hBV : volume.real B = V := by rw [hBdef, hVdef]; exact volume_real_closedBall_eq_ball hn
  have hVpos : 0 < V := by
    rw [hVdef, Measure.real_def]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume (0:E) one_pos).ne'
      MeasureTheory.measure_ball_lt_top.ne
  set N : ℝ := ∫ θ : Metric.sphere (0 : E) 1, supp K (θ : E)
      ∂(MeasureTheory.volume.toSphere) with hNdef
  have hBR : ∀ y ∈ B, ‖y‖ ≤ 1 := by
    intro y hy; rw [hBdef, Metric.mem_closedBall, dist_zero_right] at hy; exact hy
  have hsuppKnn : ∀ θ : Metric.sphere (0 : E) 1, 0 ≤ supp K (θ : E) :=
    fun θ => le_csSup (bddAbove_supp_image hR _) ⟨0, h0K, by simp⟩
  have hleK : ∀ θ : Metric.sphere (0 : E) 1, supp K (θ : E) ≤ R := by
    intro θ
    have := supp_le_of_norm_le (K := K) hKne hR (θ : E)
    rwa [norm_coe_sphere, mul_one] at this
  set s : ℝ := V ^ ((1 : ℝ) / (n : ℝ)) with hs_def
  have hs_pos : 0 < s := by rw [hs_def]; exact Real.rpow_pos_of_pos hVpos _
  have hsn : s ^ n = V := by
    rw [hs_def, one_div]
    exact Real.rpow_inv_natCast_pow hVpos.le hn.ne'
  have hsp : s ^ (n - 1) = V ^ (((n : ℝ) - 1) / (n : ℝ)) := by
    rw [← Real.rpow_natCast s (n - 1), hs_def, ← Real.rpow_mul hVpos.le]
    congr 1
    rw [Nat.cast_sub (show 1 ≤ n from hn), one_div]
    field_simp
    simp
  have hpow_div : s ^ n / s = s ^ (n - 1) := by
    have h1 : n = (n - 1) + 1 := (Nat.succ_pred_eq_of_pos hn).symm
    rw [h1, pow_succ]
    exact mul_div_cancel_right₀ (s ^ (n - 1)) hs_pos.ne'
  have key : ∀ t : ℝ, 0 < t →
      (n : ℝ) * V ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ (1 + t * R) ^ (n - 1) * N := by
    intro t ht
    set C : Set E := B + t • K with hCdef
    have hCcpt : IsCompact C := by
      rw [hCdef]; exact (isCompact_closedBall (0:E) (1:ℝ)).add (hKcpt.image (continuous_const_smul t))
    have h0C : (0 : E) ∈ C := by
      rw [hCdef, Set.mem_add]
      exact ⟨0, by rw [hBdef]; simp, 0, by rw [Set.mem_smul_set]; exact ⟨0, h0K, by simp⟩, by simp⟩
    have hCbd : ∀ y ∈ C, ‖y‖ ≤ 1 + t * R := by
      intro y hy
      rw [hCdef, Set.mem_add] at hy
      obtain ⟨b, hbB, k, hkK, hbk⟩ := hy
      rw [Set.mem_smul_set] at hkK
      obtain ⟨k₀, hk₀K, hk₀eq⟩ := hkK
      rw [← hbk, ← hk₀eq]
      calc ‖b + t • k₀‖ ≤ ‖b‖ + ‖t • k₀‖ := norm_add_le _ _
        _ ≤ 1 + t * R := by
            gcongr
            · exact hBR b hbB
            · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
              exact mul_le_mul_of_nonneg_left (hR k₀ hk₀K) ht.le
    have hsupC : ∀ θ : Metric.sphere (0 : E) 1, supp C (θ : E) ≤ 1 + t * supp K (θ : E) := by
      intro θ
      rw [supp]
      refine csSup_le (Set.Nonempty.image _ ⟨0, h0C⟩) ?_
      rintro a ⟨y, hy, rfl⟩
      rw [hCdef, Set.mem_add] at hy
      obtain ⟨b, hbB, k, hkK, hbk⟩ := hy
      rw [Set.mem_smul_set] at hkK
      obtain ⟨k₀, hk₀K, hk₀eq⟩ := hkK
      have hθ : ‖(θ : E)‖ = 1 := norm_coe_sphere
      have hb_le : inner ℝ b (θ : E) ≤ supp B (θ : E) :=
        le_csSup (bddAbove_supp_image (K := B) (R := 1) hBR _) ⟨b, hbB, rfl⟩
      have hk_le : inner ℝ k₀ (θ : E) ≤ supp K (θ : E) :=
        le_csSup (bddAbove_supp_image hR _) ⟨k₀, hk₀K, rfl⟩
      have hBval : supp B (θ : E) = 1 := by rw [hBdef, supp_closedBall, hθ]
      have hy_eq : inner ℝ y (θ : E) = inner ℝ b (θ : E) + t * inner ℝ k₀ (θ : E) := by
        rw [← hbk, ← hk₀eq, inner_add_left, real_inner_smul_left]
      simp only []
      rw [hy_eq]
      calc inner ℝ b (θ:E) + t * inner ℝ k₀ (θ:E)
          ≤ supp B (θ:E) + t * supp K (θ:E) :=
            add_le_add hb_le (mul_le_mul_of_nonneg_left hk_le ht.le)
        _ = 1 + t * supp K (θ:E) := by rw [hBval]
    have hsuppCnn : ∀ θ : Metric.sphere (0 : E) 1, 0 ≤ supp C (θ : E) :=
      fun θ => le_csSup (bddAbove_supp_image hCbd _) ⟨0, h0C, by simp⟩
    have hint1 : Integrable (fun θ : Metric.sphere (0 : E) 1 => (supp C (θ : E)) ^ n)
        MeasureTheory.volume.toSphere := by
      refine Integrable.of_bound ?_ ((1 + t * R) ^ n) ?_
      · exact (((continuous_supp (K := C) (⟨0, h0C⟩ : C.Nonempty) hCbd).comp
          continuous_subtype_val).pow n).aestronglyMeasurable
      · filter_upwards with θ
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hsuppCnn θ) n)]
        exact pow_le_pow_left₀ (hsuppCnn θ)
          (le_trans (hsupC θ) (by have h := mul_le_mul_of_nonneg_left (hleK θ) ht.le; linarith)) n
    have hint2 : Integrable (fun θ : Metric.sphere (0 : E) 1 => (1 + t * supp K (θ : E)) ^ n)
        MeasureTheory.volume.toSphere := by
      refine Integrable.of_bound ?_ ((1 + t * R) ^ n) ?_
      · exact (((continuous_const.add (continuous_const.mul
          ((continuous_supp (K := K) hKne hR).comp continuous_subtype_val))).pow n)).aestronglyMeasurable
      · filter_upwards with θ
        rw [Real.norm_eq_abs]
        have h0 : 0 ≤ 1 + t * supp K (θ : E) := by
          have := hsuppKnn θ; nlinarith [ht.le]
        rw [abs_of_nonneg (pow_nonneg h0 n)]
        exact pow_le_pow_left₀ h0 (by have h := mul_le_mul_of_nonneg_left (hleK θ) ht.le; linarith) n
    have hupp : volume.real C ≤ (1/(n:ℝ)) *
        ∫ θ : Metric.sphere (0 : E) 1, (1 + t * supp K (θ : E))^n
          ∂(MeasureTheory.volume.toSphere) := by
      have h1 := volume_real_le_integral_support hn hCcpt h0C
      have hmono : ∫ θ : Metric.sphere (0 : E) 1, (supp C (θ : E)) ^ n
            ∂(MeasureTheory.volume.toSphere)
          ≤ ∫ θ : Metric.sphere (0 : E) 1, (1 + t * supp K (θ : E)) ^ n
            ∂(MeasureTheory.volume.toSphere) :=
        integral_mono hint1 hint2 (fun θ => pow_le_pow_left₀ (hsuppCnn θ) (hsupC θ) n)
      calc volume.real C ≤ (1/(n:ℝ)) * ∫ θ : Metric.sphere (0 : E) 1, (supp C (θ : E))^n
              ∂(MeasureTheory.volume.toSphere) := h1
        _ ≤ (1/(n:ℝ)) * ∫ θ : Metric.sphere (0 : E) 1, (1 + t * supp K (θ : E))^n
              ∂(MeasureTheory.volume.toSphere) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
    have hD : (1/(n:ℝ)) * ∫ θ : Metric.sphere (0 : E) 1, (1 + t * supp K (θ : E))^n
          ∂(MeasureTheory.volume.toSphere) ≤ V + t * (1 + t * R)^(n-1) * N := by
      have hsig : (MeasureTheory.volume.toSphere : Measure (Metric.sphere (0:E) 1)).real univ
          = (n:ℝ) * V := by
        rw [Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, hVdef]
      have hpoint : ∀ θ : Metric.sphere (0:E) 1,
          (1 + t * supp K (θ:E))^n ≤ 1 + (n:ℝ) * t * (1 + t*R)^(n-1) * supp K (θ:E) := by
        intro θ
        have hu : 0 ≤ t * supp K (θ:E) := mul_nonneg ht.le (hsuppKnn θ)
        have hpow := pow_one_add_sub_one_le hu n
        have hle : (1 + t * supp K (θ:E))^(n-1) ≤ (1 + t*R)^(n-1) := by
          apply pow_le_pow_left₀ _ _ (n-1)
          · positivity
          · have := hleK θ; nlinarith [ht.le]
        calc (1 + t*supp K (θ:E))^n
            = ((1 + t*supp K (θ:E))^n - 1) + 1 := by ring
          _ ≤ (n:ℝ) * (t*supp K (θ:E)) * (1 + t*supp K (θ:E))^(n-1) + 1 := by linarith [hpow]
          _ ≤ (n:ℝ) * (t*supp K (θ:E)) * (1 + t*R)^(n-1) + 1 := by
              have hc : (0:ℝ) ≤ (n:ℝ) * (t*supp K (θ:E)) := by
                have := hsuppKnn θ; positivity
              have := mul_le_mul_of_nonneg_left hle hc
              linarith [this]
          _ = 1 + (n:ℝ) * t * (1 + t*R)^(n-1) * supp K (θ:E) := by ring
      have hint3 : Integrable (fun θ : Metric.sphere (0:E) 1 =>
          1 + (n:ℝ) * t * (1 + t*R)^(n-1) * supp K (θ:E)) MeasureTheory.volume.toSphere := by
        refine Integrable.of_bound ?_ (1 + (n:ℝ) * t * (1 + t*R)^(n-1) * R) ?_
        · exact ((continuous_const.add (continuous_const.mul
            ((continuous_supp (K:=K) hKne hR).comp continuous_subtype_val)))).aestronglyMeasurable
        · filter_upwards with θ
          rw [Real.norm_eq_abs]
          have h0 : 0 ≤ supp K (θ:E) := hsuppKnn θ
          have hc : (0:ℝ) ≤ (n:ℝ) * t * (1 + t*R)^(n-1) := by
            have := ht.le; positivity
          rw [abs_of_nonneg (by positivity)]
          nlinarith [hleK θ, h0, hc]
      have hmono2 : ∫ θ : Metric.sphere (0:E) 1, (1 + t * supp K (θ:E))^n
            ∂(MeasureTheory.volume.toSphere)
          ≤ ∫ θ : Metric.sphere (0:E) 1,
              (1 + (n:ℝ) * t * (1 + t*R)^(n-1) * supp K (θ:E))
            ∂(MeasureTheory.volume.toSphere) :=
        integral_mono hint2 hint3 (fun θ => hpoint θ)
      have hc0 : (0:ℝ) ≤ (n:ℝ) * t * (1 + t*R)^(n-1) := by
        have := ht.le; positivity
      have hintc : Integrable (fun θ : Metric.sphere (0:E) 1 =>
          (n:ℝ) * t * (1 + t*R)^(n-1) * supp K (θ:E)) MeasureTheory.volume.toSphere := by
        refine Integrable.of_bound ?_ ((n:ℝ) * t * (1 + t*R)^(n-1) * R) ?_
        · exact (continuous_const.mul ((continuous_supp (K:=K) hKne hR).comp
            continuous_subtype_val)).aestronglyMeasurable
        · filter_upwards with θ
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc0 (hsuppKnn θ))]
          exact mul_le_mul_of_nonneg_left (hleK θ) hc0
      have hsplit : ∫ θ : Metric.sphere (0:E) 1,
            (1 + (n:ℝ) * t * (1 + t*R)^(n-1) * supp K (θ:E))
            ∂(MeasureTheory.volume.toSphere)
          = (n:ℝ) * V + (n:ℝ) * t * (1 + t*R)^(n-1) * N := by
        rw [integral_add (integrable_const (1:ℝ)) hintc, integral_const, hsig,
          integral_const_mul, ← hNdef, smul_eq_mul, mul_one]
      calc (1/(n:ℝ)) * ∫ θ : Metric.sphere (0:E) 1, (1 + t * supp K (θ:E))^n
              ∂(MeasureTheory.volume.toSphere)
          ≤ (1/(n:ℝ)) * ∫ θ : Metric.sphere (0:E) 1,
              (1 + (n:ℝ) * t * (1 + t*R)^(n-1) * supp K (θ:E))
              ∂(MeasureTheory.volume.toSphere) :=
            mul_le_mul_of_nonneg_left hmono2 (by positivity)
        _ = (1/(n:ℝ)) * ((n:ℝ) * V + (n:ℝ) * t * (1 + t*R)^(n-1) * N) := by rw [hsplit]
        _ = V + t * (1 + t*R)^(n-1) * N := by field_simp
    have hlow : V + (n:ℝ) * V^(((n:ℝ)-1)/(n:ℝ)) * t ≤ volume.real C := by
      have hBmeas : MeasurableSet B := by rw [hBdef]; exact isClosed_closedBall.measurableSet
      have hBbd : Bornology.IsBounded B := by rw [hBdef]; exact isBounded_closedBall
      have hBpos : 0 < volume.real B := by rw [hBV]; exact hVpos
      have htKmeas : MeasurableSet (t • K) := (hKcpt.image (continuous_const_smul t)).measurableSet
      have htKbd : Bornology.IsBounded (t • K) := (hKcpt.image (continuous_const_smul t)).isBounded
      have htKpos : 0 < volume.real (t • K) := by
        rw [volume_real_smul t ht.le K, hvol, mul_one]; exact pow_pos ht n
      have hbm := brunn_minkowski_add hn B (t • K) hBmeas htKmeas hBbd htKbd hBpos htKpos
      have htpow : (volume.real (t • K)) ^ ((1:ℝ)/(n:ℝ)) = t := by
        rw [volume_real_smul t ht.le K, hvol, mul_one]
        rw [one_div, ← Real.rpow_natCast t n, ← Real.rpow_mul ht.le, mul_inv_cancel₀ hnne,
          Real.rpow_one]
      rw [hBV, htpow] at hbm
      have hΦ : V ^ ((1:ℝ)/(n:ℝ)) + t ≤ volume.real C ^ ((1:ℝ)/(n:ℝ)) := by
        rw [hCdef]; exact hbm
      have hvolCnn : 0 ≤ volume.real C := measureReal_nonneg
      have h3 : (volume.real C ^ ((1:ℝ)/(n:ℝ)))^n = volume.real C := by
        rw [one_div]; exact Real.rpow_inv_natCast_pow hvolCnn hn.ne'
      have h2 : (V^((1:ℝ)/(n:ℝ)) + t)^n ≤ volume.real C := by
        have h2' := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ V^((1:ℝ)/(n:ℝ)) + t) hΦ n
        rwa [h3] at h2'
      have hts : -2 ≤ t / s := by
        have h0 : (0:ℝ) ≤ t / s := by positivity
        linarith
      have hB_bern : 1 + (n:ℝ) * (t/s) ≤ (1 + t/s)^n := one_add_mul_le_pow hts n
      have hmul := mul_le_mul_of_nonneg_left hB_bern (pow_nonneg hs_pos.le n)
      have hL_alg : s^n * (1 + t/s)^n = (s + t)^n := by
        rw [← mul_pow]; congr 1; field_simp
      have hVs : V / s = V^(((n:ℝ)-1)/(n:ℝ)) := by
        conv_lhs => rw [← hsn]
        rw [hpow_div, hsp]
      have hR_alg : s^n * (1 + (n:ℝ)*(t/s)) = V + (n:ℝ)*V^(((n:ℝ)-1)/(n:ℝ))*t := by
        rw [hsn, mul_add, mul_one]
        have hVs' : V * ((n:ℝ)*(t/s)) = (n:ℝ)*t*(V/s) := by ring
        rw [hVs', hVs]; ring
      rw [hL_alg, hR_alg, hs_def] at hmul
      linarith [hmul, h2]
    have hcomb : V + (n:ℝ) * V^(((n:ℝ)-1)/(n:ℝ)) * t ≤ V + t * (1 + t * R)^(n-1) * N :=
      le_trans hlow (le_trans hupp hD)
    have h1 : (n:ℝ) * V^(((n:ℝ)-1)/(n:ℝ)) * t ≤ t * ((1 + t * R)^(n-1) * N) := by
      linarith [hcomb]
    have h2 : t * ((n:ℝ) * V^(((n:ℝ)-1)/(n:ℝ))) ≤ t * ((1 + t * R)^(n-1) * N) := by
      linarith [h1]
    exact le_of_mul_le_mul_left h2 ht
  have htend : Tendsto (fun t : ℝ => (1 + t * R) ^ (n - 1) * N) (𝓝[>] (0:ℝ)) (𝓝 N) := by
    have hc : Continuous (fun t : ℝ => (1 + t * R) ^ (n - 1)) := by fun_prop
    have h1 : Tendsto (fun t : ℝ => (1 + t * R) ^ (n - 1)) (𝓝[>] (0:ℝ))
        (𝓝 ((1 + 0 * R) ^ (n - 1))) :=
      (hc.continuousAt.tendsto).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    have h2 : Tendsto (fun t : ℝ => (1 + t * R) ^ (n - 1) * N) (𝓝[>] (0:ℝ))
        (𝓝 ((1 + 0 * R) ^ (n - 1) * N)) := h1.mul tendsto_const_nhds
    simpa using h2
  exact ge_of_tendsto htend (by
    filter_upwards [self_mem_nhdsWithin] with t ht' using key t ht')

end Core

end Main

theorem urysohn_inequality {n : ℕ} (hn : 0 < n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hKsymm : (-K : Set (EuclideanSpace ℝ (Fin n))) = K)
    (hvol : MeasureTheory.volume.real K = 1) :
    (MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ^ (-(1 / (n : ℝ)))
      ≤ ∫ x : EuclideanSpace ℝ (Fin n), (sSup ((fun y => inner ℝ y ((‖x‖)⁻¹ • x)) '' K))
          * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  have hVpos : 0 < MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [Measure.real_def]
    exact ENNReal.toReal_pos
      (Metric.measure_ball_pos MeasureTheory.volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
      MeasureTheory.measure_ball_lt_top.ne
  have hKne : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h; rw [h] at hvol; simp at hvol
  obtain ⟨y₀, hy₀, hmax⟩ := hKcpt.exists_isMaxOn hKne continuous_norm.continuousOn
  have hR : ∀ y ∈ K, ‖y‖ ≤ ‖y₀‖ := fun y hy => hmax hy
  have hcore := urysohn_core hn K hKcvx hKcpt hKsymm hvol
  have hint := integral_dir_supp hn hKne hR
  have hgauss := integral_gauss_radial (n := n) hn
  have hEq : (∫ x : EuclideanSpace ℝ (Fin n),
        (sSup ((fun y => inner ℝ y ((‖x‖)⁻¹ • x)) '' K)) * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ((n : ℝ) * MeasureTheory.volume.real
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
        * (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            supp K (θ : EuclideanSpace ℝ (Fin n)) ∂(MeasureTheory.volume.toSphere)) := by
    rw [show (∫ x : EuclideanSpace ℝ (Fin n),
          (sSup ((fun y => inner ℝ y ((‖x‖)⁻¹ • x)) '' K)) * Real.exp (-Real.pi * ‖x‖ ^ 2))
        = ∫ x : EuclideanSpace ℝ (Fin n),
            supp K ((‖x‖)⁻¹ • x) * Real.exp (-Real.pi * ‖x‖ ^ 2) from
          integral_congr_ae (Eventually.of_forall (fun x => rfl))]
    rw [hint, hgauss]
  have hstep : ((n : ℝ) * MeasureTheory.volume.real
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
        * ((n : ℝ) * MeasureTheory.volume.real
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (((n:ℝ)-1)/(n:ℝ)))
      = (MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
          ^ (-(1 / (n : ℝ))) := by
    have hVne : MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
      ne_of_gt hVpos
    have h1 : ((n : ℝ) * MeasureTheory.volume.real
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
          * ((n : ℝ) * MeasureTheory.volume.real
              (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (((n:ℝ)-1)/(n:ℝ)))
        = MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
              ^ (((n:ℝ)-1)/(n:ℝ))
            / MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      field_simp
    rw [h1, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hVpos]
    congr 1
    field_simp
    ring
  calc (MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
          ^ (-(1 / (n : ℝ)))
      = ((n : ℝ) * MeasureTheory.volume.real
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
          * ((n : ℝ) * MeasureTheory.volume.real
              (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (((n:ℝ)-1)/(n:ℝ))) := hstep.symm
    _ ≤ ((n : ℝ) * MeasureTheory.volume.real
            (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹
          * (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              supp K (θ : EuclideanSpace ℝ (Fin n)) ∂(MeasureTheory.volume.toSphere)) := by
        apply mul_le_mul_of_nonneg_left hcore
        exact inv_nonneg.mpr (le_of_lt (mul_pos (by exact_mod_cast hn) hVpos))
    _ = ∫ x : EuclideanSpace ℝ (Fin n),
          (sSup ((fun y => inner ℝ y ((‖x‖)⁻¹ • x)) '' K)) * Real.exp (-Real.pi * ‖x‖ ^ 2) :=
        hEq.symm

end Commons.GeometryOfNumbers