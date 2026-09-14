import Mathlib
import Submission.Commons.GeometryOfNumbers.urysohn_inequality
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm
import Submission.Commons.Measure.Integral.gaussian_second_moment_exp_pi

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Pointwise Real Topology

namespace Commons.GeometryOfNumbers

section Helpers

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The support function is positively homogeneous. -/
lemma supp_smul_of_pos {K : Set E} {r : ℝ} (hr : 0 < r) (u : E) :
    supp K (r • u) = r * supp K u := by
  rw [supp, supp]
  have hset : ((fun y => inner ℝ y (r • u)) '' K) = r • ((fun y => inner ℝ y u) '' K) := by
    ext b
    simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨y, hy, hb⟩
      exact ⟨inner ℝ y u, ⟨y, hy, rfl⟩, by rw [← hb, real_inner_smul_right]⟩
    · rintro ⟨a, ⟨y, hy, hya⟩, hba⟩
      exact ⟨y, hy, by rw [real_inner_smul_right, hya, hba]⟩
  rw [hset, Real.sSup_smul_of_nonneg hr.le, smul_eq_mul]

/-- `‖x‖² exp(-π‖x‖²)` is integrable on `ℝⁿ`. -/
lemma integrable_norm_sq_exp_pi :
    Integrable (fun x : E => ‖x‖^2 * Real.exp (-Real.pi * ‖x‖^2)) volume := by
  have hbase : Integrable (fun x : E => Real.exp (-(Real.pi/2)*‖x‖^2)) volume :=
    Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm (Real.pi/2) (by positivity)
  refine Integrable.mono' (hbase.const_mul (2/Real.pi * Real.exp (-1))) ?_ ?_
  · fun_prop
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hu := Real.mul_exp_neg_le_exp_neg_one ((Real.pi/2)*‖x‖^2)
    have h1 : ‖x‖^2 * Real.exp (-Real.pi * ‖x‖^2)
        = (‖x‖^2 * Real.exp (-(Real.pi/2) * ‖x‖^2)) * Real.exp (-(Real.pi/2) * ‖x‖^2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    rw [h1]
    have hb : ‖x‖^2 * Real.exp (-(Real.pi/2) * ‖x‖^2) ≤ 2/Real.pi * Real.exp (-1) := by
      have h2 : (Real.pi/2)*‖x‖^2 * Real.exp (-((Real.pi/2)*‖x‖^2)) ≤ Real.exp (-1) := hu
      have h2' : (Real.pi/2)*‖x‖^2 * Real.exp (-(Real.pi/2)*‖x‖^2) ≤ Real.exp (-1) := by
        convert h2 using 2; ring_nf
      have hm := mul_le_mul_of_nonneg_left h2' (show (0:ℝ) ≤ 2/Real.pi by positivity)
      have heq : (2/Real.pi) * ((Real.pi/2)*‖x‖^2 * Real.exp (-(Real.pi/2)*‖x‖^2))
          = ‖x‖^2 * Real.exp (-(Real.pi/2)*‖x‖^2) := by
        field_simp
      rw [heq] at hm
      exact hm
    calc ‖x‖^2 * Real.exp (-(Real.pi/2) * ‖x‖^2) * Real.exp (-(Real.pi/2) * ‖x‖^2)
        ≤ (2/Real.pi * Real.exp (-1)) * Real.exp (-(Real.pi/2) * ‖x‖^2) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = 2/Real.pi * Real.exp (-1) * Real.exp (-(Real.pi/2) * ‖x‖^2) := rfl

/-- `(supp K ·)² exp(-π‖·‖²)` is integrable for bounded `K`. -/
lemma integrable_supp_sq_exp {K : Set E} (hne : K.Nonempty) {R : ℝ} (hR : ∀ y ∈ K, ‖y‖ ≤ R) :
    Integrable (fun x : E => (supp K x)^2 * Real.exp (-Real.pi * ‖x‖^2)) volume := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR _ hne.some_mem)
  refine Integrable.mono' (integrable_norm_sq_exp_pi (n:=n) |>.const_mul (R^2)) ?_ ?_
  · have hcont : Continuous (supp K) := continuous_supp hne hR
    exact ((hcont.pow 2).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb : |supp K x| ≤ R * ‖x‖ := abs_supp_le hne hR x
    have h2 : (supp K x)^2 ≤ R^2 * ‖x‖^2 := by
      have h1 : (supp K x)^2 = |supp K x|^2 := (sq_abs _).symm
      rw [h1]
      calc |supp K x|^2 ≤ (R*‖x‖)^2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = R^2 * ‖x‖^2 := by ring
    calc (supp K x)^2 * Real.exp (-Real.pi * ‖x‖^2)
        ≤ R^2 * ‖x‖^2 * Real.exp (-Real.pi*‖x‖^2) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = R^2 * (‖x‖^2 * Real.exp (-Real.pi*‖x‖^2)) := by ring

/-- Polar-coordinate decomposition of `∫ (supp K x)² exp(-π‖x‖²)`. -/
lemma integral_supp_sq_exp_polar (hn : 0 < n) {K : Set E} (hne : K.Nonempty)
    {R : ℝ} (hR : ∀ y ∈ K, ‖y‖ ≤ R) :
    (∫ x : E, (supp K x)^2 * Real.exp (-Real.pi * ‖x‖^2))
      = (∫ r : Set.Ioi (0:ℝ), (r:ℝ)^2 * Real.exp (-Real.pi*(r:ℝ)^2)
            ∂(Measure.volumeIoiPow (n - 1)))
        * (∫ θ : Metric.sphere (0:E) 1, (supp K (θ:E))^2 ∂(MeasureTheory.volume.toSphere)) := by
  haveI : Nontrivial E := by haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩; infer_instance
  have hInt := integrable_supp_sq_exp (n:=n) hne hR
  rw [Commons.Analysis.MeasureTheory.polar_integral E
      (fun x : E => (supp K x)^2 * Real.exp (-Real.pi*‖x‖^2)) hInt]
  simp only [finrank_euclideanSpace_fin]
  rw [show (∫ θ : Metric.sphere (0:E) 1,
        ∫ r : Set.Ioi (0:ℝ),
          (supp K (r.1 • (θ:E)))^2 * Real.exp (-Real.pi*‖r.1 • (θ:E)‖^2)
          ∂(Measure.volumeIoiPow (n - 1)) ∂(MeasureTheory.volume.toSphere))
      = ∫ θ : Metric.sphere (0:E) 1,
          (∫ r : Set.Ioi (0:ℝ), (r:ℝ)^2 * Real.exp (-Real.pi*(r:ℝ)^2)
            ∂(Measure.volumeIoiPow (n - 1))) * (supp K (θ:E))^2
          ∂(MeasureTheory.volume.toSphere) from ?_]
  · rw [integral_const_mul]
  · refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only []
    rw [show (∫ r : Set.Ioi (0:ℝ),
          (supp K (r.1 • (θ:E)))^2 * Real.exp (-Real.pi*‖r.1 • (θ:E)‖^2)
          ∂(Measure.volumeIoiPow (n - 1)))
        = ∫ r : Set.Ioi (0:ℝ),
          ((r:ℝ)^2 * Real.exp (-Real.pi*(r:ℝ)^2)) * (supp K (θ:E))^2
          ∂(Measure.volumeIoiPow (n - 1)) from ?_]
    · rw [integral_mul_const]
    · refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      show supp K ((r:ℝ) • (θ:E)) ^ 2 * Real.exp (-Real.pi * ‖(r:ℝ) • (θ:E)‖ ^ 2)
          = (r:ℝ)^2 * Real.exp (-Real.pi * (r:ℝ)^2) * (supp K (θ:E))^2
      have hθn := norm_coe_sphere (θ := θ)
      have hr : 0 < (r:ℝ) := r.2
      rw [norm_dir hθn hr, supp_smul_of_pos hr]
      ring

/-- Polar-coordinate decomposition of `∫ ‖x‖² exp(-π‖x‖²)`. -/
lemma integral_norm_sq_exp_polar (hn : 0 < n) :
    (∫ x : E, ‖x‖^2 * Real.exp (-Real.pi * ‖x‖^2))
      = (∫ r : Set.Ioi (0:ℝ), (r:ℝ)^2 * Real.exp (-Real.pi*(r:ℝ)^2)
            ∂(Measure.volumeIoiPow (n - 1)))
        * (∫ θ : Metric.sphere (0:E) 1, (1:ℝ) ∂(MeasureTheory.volume.toSphere)) := by
  haveI : Nontrivial E := by haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩; infer_instance
  have hInt := integrable_norm_sq_exp_pi (n:=n)
  rw [Commons.Analysis.MeasureTheory.polar_integral E
      (fun x : E => ‖x‖^2 * Real.exp (-Real.pi*‖x‖^2)) hInt]
  simp only [finrank_euclideanSpace_fin]
  rw [show (∫ θ : Metric.sphere (0:E) 1,
        ∫ r : Set.Ioi (0:ℝ),
          ‖r.1 • (θ:E)‖^2 * Real.exp (-Real.pi*‖r.1 • (θ:E)‖^2)
          ∂(Measure.volumeIoiPow (n - 1)) ∂(MeasureTheory.volume.toSphere))
      = ∫ θ : Metric.sphere (0:E) 1,
          (∫ r : Set.Ioi (0:ℝ), (r:ℝ)^2 * Real.exp (-Real.pi*(r:ℝ)^2)
            ∂(Measure.volumeIoiPow (n - 1))) * (1:ℝ)
          ∂(MeasureTheory.volume.toSphere) from ?_]
  · rw [integral_const_mul]
  · refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only []
    rw [show (∫ r : Set.Ioi (0:ℝ),
          ‖r.1 • (θ:E)‖^2 * Real.exp (-Real.pi*‖r.1 • (θ:E)‖^2)
          ∂(Measure.volumeIoiPow (n - 1)))
        = ∫ r : Set.Ioi (0:ℝ),
          ((r:ℝ)^2 * Real.exp (-Real.pi*(r:ℝ)^2)) * (1:ℝ)
          ∂(Measure.volumeIoiPow (n - 1)) from ?_]
    · rw [integral_mul_const]
    · refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      show ‖(r:ℝ) • (θ:E)‖ ^ 2 * Real.exp (-Real.pi * ‖(r:ℝ) • (θ:E)‖ ^ 2)
          = (r:ℝ)^2 * Real.exp (-Real.pi * (r:ℝ)^2) * 1
      have hθn := norm_coe_sphere (θ := θ)
      have hr : 0 < (r:ℝ) := r.2
      rw [norm_dir hθn hr]
      ring


end Helpers
/-- Cauchy–Schwarz on a finite measure: `(∫ f)² ≤ μ(univ) ∫ f²`. -/
lemma sq_integral_le_measureReal_univ_mul_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hA : μ.real univ ≠ 0) :
    (∫ x, f x ∂μ)^2 ≤ μ.real univ * ∫ x, f x^2 ∂μ := by
  set A : ℝ := μ.real univ with hAdef
  set B : ℝ := ∫ x, f x ∂μ with hBdef
  have hA0 : 0 < A := lt_of_le_of_ne measureReal_nonneg (Ne.symm hA)
  have hf1 : Integrable (fun x => A^2 * (f x)^2 - (2*A*B) * f x) μ :=
    (hf2.const_mul (A^2)).sub (hf.const_mul (2*A*B))
  have hnonneg : 0 ≤ ∫ x, (A * f x - B)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have step1 : ∫ x, (A * f x - B)^2 ∂μ
      = ∫ x, (A^2 * (f x)^2 - (2*A*B) * f x) ∂μ + ∫ x, (B^2 : ℝ) ∂μ := by
    rw [← integral_add hf1 (integrable_const (B^2))]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have step2 : ∫ x, (A^2 * (f x)^2 - (2*A*B) * f x) ∂μ
      = A^2 * (∫ x, (f x)^2 ∂μ) - (2*A*B) * (∫ x, f x ∂μ) := by
    rw [integral_sub (hf2.const_mul (A^2)) (hf.const_mul (2*A*B)),
      integral_const_mul, integral_const_mul]
  have step3 : ∫ x, (B^2 : ℝ) ∂μ = A * B^2 := by
    rw [integral_const, hAdef, smul_eq_mul]
  have hexp : ∫ x, (A * f x - B)^2 ∂μ = A^2 * (∫ x, (f x)^2 ∂μ) - A * B^2 := by
    rw [step1, step2, step3, ← hBdef]; ring
  have hkey : B^2 ≤ A * (∫ x, (f x)^2 ∂μ) := by
    nlinarith [hnonneg, hexp, hA0]
  rw [hAdef, hBdef]
  linarith [hkey]

theorem minkowski_polar_lower {n : ℕ} (hn : 0 < n) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hKsymm : (-K : Set (EuclideanSpace ℝ (Fin n))) = K)
    (hvol : MeasureTheory.volume.real K = 1) :
    (MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ^ (-(2 / (n : ℝ)))
      * (n : ℝ) / (2 * Real.pi)
      ≤ ∫ x : EuclideanSpace ℝ (Fin n),
          (sSup ((fun y => inner ℝ y x) '' K)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  have hKne : K.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h; rw [h] at hvol; simp at hvol
  obtain ⟨R, hR0, hR⟩ := exists_norm_bound_of_isCompact hKcpt
  set V : ℝ := MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hVdef
  have hVpos : 0 < V := by
    rw [hVdef, Measure.real_def]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos MeasureTheory.volume (0:EuclideanSpace ℝ (Fin n)) one_pos).ne'
      MeasureTheory.measure_ball_lt_top.ne
  set Sig : ℝ := ∫ θ : Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1, (supp K (θ:EuclideanSpace ℝ (Fin n)))^2 ∂(MeasureTheory.volume.toSphere)
    with hSigdef
  set Lam : ℝ := ∫ θ : Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1, supp K (θ:EuclideanSpace ℝ (Fin n)) ∂(MeasureTheory.volume.toSphere)
    with hLamdef
  set one_ : ℝ := (MeasureTheory.volume.toSphere : Measure (Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1)).real Set.univ
    with honedef
  set ρ : ℝ := ∫ r : Set.Ioi (0:ℝ), (r:ℝ)^2 * Real.exp (-Real.pi*(r:ℝ)^2)
      ∂(Measure.volumeIoiPow (n - 1)) with hrdef
  have hpolarL : (∫ x : EuclideanSpace ℝ (Fin n), (supp K x)^2 * Real.exp (-Real.pi * ‖x‖^2)) = ρ * Sig := by
    rw [integral_supp_sq_exp_polar hn hKne hR, hrdef, hSigdef]
  have hone_int : (∫ θ : Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1, (1:ℝ) ∂(MeasureTheory.volume.toSphere)) = one_ := by
    rw [honedef, integral_const, smul_eq_mul, mul_one]
  have hpolarR : (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖^2 * Real.exp (-Real.pi * ‖x‖^2)) = ρ * one_ := by
    rw [integral_norm_sq_exp_polar hn, hrdef, hone_int]
  have hM : (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖^2 * Real.exp (-Real.pi * ‖x‖^2)) = (n:ℝ)/(2*Real.pi) :=
    Commons.Measure.Integral.gaussian_second_moment_exp_pi hn
  have hS : one_ = (n:ℝ) * V := by
    rw [honedef, Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, hVdef]
  have hone_pos : 0 < one_ := by rw [hS]; positivity
  have hcore : (n:ℝ) * V^(((n:ℝ)-1)/(n:ℝ)) ≤ Lam := by
    have h := urysohn_core hn K hKcvx hKcpt hKsymm hvol
    rw [hLamdef, hVdef]
    exact h
  have hcont : Continuous (fun θ : Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1 => supp K (θ:EuclideanSpace ℝ (Fin n))) :=
    (continuous_supp hKne hR).comp continuous_subtype_val
  have hLam_int : Integrable (fun θ : Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1 => supp K (θ:EuclideanSpace ℝ (Fin n)))
      (MeasureTheory.volume.toSphere) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable R ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs]
    exact le_trans (abs_supp_le hKne hR (θ:EuclideanSpace ℝ (Fin n))) (by rw [norm_coe_sphere, mul_one])
  have hSig_int : Integrable (fun θ : Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1 => (supp K (θ:EuclideanSpace ℝ (Fin n)))^2)
      (MeasureTheory.volume.toSphere) := by
    refine Integrable.of_bound (hcont.pow 2).aestronglyMeasurable (R^2) ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb : |supp K (θ:EuclideanSpace ℝ (Fin n))| ≤ R :=
      le_trans (abs_supp_le hKne hR (θ:EuclideanSpace ℝ (Fin n))) (by rw [norm_coe_sphere, mul_one])
    calc (supp K (θ:EuclideanSpace ℝ (Fin n)))^2 = |supp K (θ:EuclideanSpace ℝ (Fin n))|^2 := (sq_abs _).symm
      _ ≤ R^2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hA : (MeasureTheory.volume.toSphere : Measure (Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1)).real Set.univ ≠ 0 := by
    rw [← honedef]; exact ne_of_gt hone_pos
  have hCS : Lam^2 ≤ one_ * Sig := by
    have h := sq_integral_le_measureReal_univ_mul_integral_sq
      (μ := MeasureTheory.volume.toSphere) hLam_int hSig_int hA
    rw [← honedef] at h
    exact h
  have hcore2 : ((n:ℝ) * V^(((n:ℝ)-1)/(n:ℝ)))^2 ≤ Lam^2 :=
    pow_le_pow_left₀ (by positivity) hcore 2
  have hSig_lb : (n:ℝ) * V^(1 - 2/(n:ℝ)) ≤ Sig := by
    have h1 : ((n:ℝ) * V^(((n:ℝ)-1)/(n:ℝ)))^2 / one_ ≤ Sig := by
      rw [div_le_iff₀ hone_pos]
      calc ((n:ℝ) * V^(((n:ℝ)-1)/(n:ℝ)))^2 ≤ one_ * Sig := le_trans hcore2 hCS
        _ = Sig * one_ := by ring
    have h2 : ((n:ℝ) * V^(((n:ℝ)-1)/(n:ℝ)))^2 / one_ = (n:ℝ) * V^(1 - 2/(n:ℝ)) := by
      rw [hS]
      rw [div_eq_iff (by positivity : (n:ℝ) * V ≠ 0)]
      rw [mul_pow, ← Real.rpow_natCast (V^(((n:ℝ)-1)/(n:ℝ))) 2, ← Real.rpow_mul hVpos.le]
      rw [show (((n:ℝ)-1)/(n:ℝ)) * ((2:ℕ):ℝ) = 1 - 2/(n:ℝ) + 1 by
        push_cast; field_simp; ring]
      rw [Real.rpow_add hVpos, Real.rpow_one]
      ring
    linarith [h1, h2]
  have hFin : (n:ℝ)/(2*Real.pi) * V^(-(2/(n:ℝ))) ≤ ∫ x : EuclideanSpace ℝ (Fin n),
      (sSup ((fun y => inner ℝ y x) '' K)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    rw [show (∫ x : EuclideanSpace ℝ (Fin n), (sSup ((fun y => inner ℝ y x) '' K))^2 * Real.exp (-Real.pi*‖x‖^2))
        = ∫ x : EuclideanSpace ℝ (Fin n), (supp K x)^2 * Real.exp (-Real.pi*‖x‖^2) from rfl, hpolarL]
    have hrM : ρ = ((n:ℝ)/(2*Real.pi)) / one_ := by
      rw [eq_div_iff (ne_of_gt hone_pos), ← hpolarR, hM]
    rw [hrM]
    have hstep : ((n:ℝ)/(2*Real.pi)) / one_ * ((n:ℝ) * V^(1 - 2/(n:ℝ)))
        = (n:ℝ)/(2*Real.pi) * V^(-(2/(n:ℝ))) := by
      rw [show one_ = (n:ℝ) * V from hS]
      have hVn : V^(1 - 2/(n:ℝ)) = V * V^(-(2/(n:ℝ))) := by
        rw [show 1 - 2/(n:ℝ) = 1 + (-(2/(n:ℝ))) by ring, Real.rpow_add hVpos, Real.rpow_one]
      rw [hVn]
      field_simp
    calc (n:ℝ)/(2*Real.pi) * V^(-(2/(n:ℝ)))
        = ((n:ℝ)/(2*Real.pi)) / one_ * ((n:ℝ) * V^(1 - 2/(n:ℝ))) := hstep.symm
      _ ≤ ((n:ℝ)/(2*Real.pi)) / one_ * Sig := by
          refine mul_le_mul_of_nonneg_left hSig_lb ?_
          positivity
  rw [show (n:ℝ) / (2 * Real.pi) = (n:ℝ)/(2*Real.pi) from rfl,
      show (-(2 / (n : ℝ))) = -(2/(n:ℝ)) from rfl] at hFin
  calc (MeasureTheory.volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ^ (-(2 / (n : ℝ))) * (n : ℝ) / (2 * Real.pi)
      = (n:ℝ)/(2*Real.pi) * V^(-(2/(n:ℝ))) := by rw [hVdef]; ring
    _ ≤ _ := hFin

end Commons.GeometryOfNumbers
