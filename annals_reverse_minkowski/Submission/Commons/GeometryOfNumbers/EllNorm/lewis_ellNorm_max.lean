import Mathlib
import Submission.Commons.GeometryOfNumbers.EllNorm.continuousOn_integral_gauge_sq_gaussian
import Submission.Commons.GeometryOfNumbers.EllNorm.integral_norm_sq_toLpLin_gaussian
import Submission.Commons.GeometryOfNumbers.minkowski_polar_lower

set_option linter.unusedVariables false

/-!
# The Lewis ellipsoid: existence of a determinant-maximising matrix

This file proves the analytic core of the "Lewis ellipsoid" / reverse-Minkowski input.

For a compact convex `K ⊆ ℝᵐ` with `0` in its interior, the Gaussian-weighted squared gauge

  `ellSqGauss K B = ∫ x, (gauge K (B x))² exp(-π ‖x‖²) dx`

is a continuous, coercive, convex function of the matrix `B`, so its sublevel set
`{B | ellSqGauss K B ≤ τ}` is a compact convex body.  The determinant attains its maximum
there, and the first-order optimality condition (Jacobi's formula) for a determinant
maximiser `C` gives `trace (C⁻¹ * B) ≤ m` for every `B` with `ellSqGauss K B ≤ τ`.

Finally the target theorem, stated with the Gaussian `exp(-‖x‖²/2)` and the unit threshold,
follows by the change of variables `x ↦ √(2π) x`.
-/

namespace Commons.GeometryOfNumbers.EllNorm

open MeasureTheory Matrix Set Filter
open scoped Real BigOperators Topology ENNReal

noncomputable section

variable {m : ℕ}

/-! ## Jacobi's formula for the derivative of the determinant -/

/-- **Jacobi's formula** at `t = 0` for `det (1 + t • N)`: the derivative is `trace N`. -/
theorem hasDerivAt_det_one_add_smul (N : Matrix (Fin m) (Fin m) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • N).det) N.trace 0 := by
  have hprod : ∀ (σ : Equiv.Perm (Fin m)) (i : Fin m),
      (∏ j ∈ Finset.univ.erase i, (if σ j = j then (1:ℝ) else 0))
        = (if σ = 1 then (1:ℝ) else 0) := by
    intro σ i
    by_cases hσ : σ = 1
    · subst hσ
      rw [if_pos rfl]
      exact Finset.prod_eq_one (fun j _ => by simp)
    · rw [if_neg hσ]
      obtain ⟨j, hj⟩ : ∃ j, σ j ≠ j := by
        by_contra h
        push Not at h
        exact hσ (Equiv.Perm.ext (fun x => by simpa using h x))
      obtain ⟨k, hki, hk⟩ : ∃ k, k ≠ i ∧ σ k ≠ k := by
        rcases eq_or_ne j i with hji | hji
        · refine ⟨σ i, ?_, fun hcon => ?_⟩
          · rwa [hji] at hj
          · rw [hji] at hj; exact hj (σ.injective hcon)
        · exact ⟨j, hji, hj⟩
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩) (if_neg hk)
  have key : ∀ σ : Equiv.Perm (Fin m),
      (∑ i, (∏ j ∈ Finset.univ.erase i, (if σ j = j then (1:ℝ) else 0)) * N (σ i) i)
        = (if σ = 1 then (1:ℝ) else 0) * N.trace := by
    intro σ
    rw [Finset.sum_congr rfl (fun i _ => by rw [hprod σ i])]
    by_cases hσ : σ = 1
    · subst hσ; rw [if_pos rfl, one_mul]; simp [Matrix.trace]
    · rw [if_neg hσ]; simp
  have hfun : (fun t : ℝ => (1 + t • N).det)
      = (∑ σ : Equiv.Perm (Fin m), fun t : ℝ => ((Equiv.Perm.sign σ : ℤˣ) : ℝ) *
          ∏ i, ((if σ i = i then (1:ℝ) else 0) + t * N (σ i) i)) := by
    funext t
    rw [Finset.sum_apply, Matrix.det_apply']
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
  rw [hfun]
  have h1 : ∀ (σ : Equiv.Perm (Fin m)) (i : Fin m),
      HasDerivAt (fun t : ℝ => (if σ i = i then (1:ℝ) else 0) + t * N (σ i) i) (N (σ i) i) 0 := by
    intro σ i
    have hl : HasDerivAt (fun t : ℝ => t * N (σ i) i) (N (σ i) i) 0 := by
      have h := (hasDerivAt_id (0:ℝ)).mul_const (N (σ i) i)
      simpa using h
    exact hl.const_add _
  have hderiv : ∀ σ : Equiv.Perm (Fin m), HasDerivAt (fun t : ℝ => ((Equiv.Perm.sign σ : ℤˣ) : ℝ) *
          ∏ i, ((if σ i = i then (1:ℝ) else 0) + t * N (σ i) i))
      (((Equiv.Perm.sign σ : ℤˣ) : ℝ) *
        (∑ i, (∏ j ∈ Finset.univ.erase i, (if σ j = j then (1:ℝ) else 0)) * N (σ i) i)) 0 := by
    intro σ
    have hσd0 : HasDerivAt (∏ i : Fin m, fun t : ℝ => ((if σ i = i then (1:ℝ) else 0) + t * N (σ i) i))
        (∑ i, (∏ j ∈ Finset.univ.erase i, (if σ j = j then (1:ℝ) else 0)) * N (σ i) i) 0 := by
      have := HasDerivAt.finsetProd (u := (Finset.univ : Finset (Fin m)))
        (f := fun i t => (if σ i = i then (1:ℝ) else 0) + t * N (σ i) i)
        (f' := fun i => N (σ i) i) (fun i _ => h1 σ i)
      simpa using this
    have hσd : HasDerivAt (fun t : ℝ => ∏ i : Fin m, ((if σ i = i then (1:ℝ) else 0) + t * N (σ i) i))
        (∑ i, (∏ j ∈ Finset.univ.erase i, (if σ j = j then (1:ℝ) else 0)) * N (σ i) i) 0 :=
      hσd0.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun t => by rw [Finset.prod_apply]))
    exact hσd.const_mul _
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun σ _ => hderiv σ)
  have hgoal : (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤˣ) : ℝ) *
        (∑ i, (∏ j ∈ Finset.univ.erase i, (if σ j = j then (1:ℝ) else 0)) * N (σ i) i)) = N.trace := by
    rw [Finset.sum_congr rfl (fun σ _ => by rw [key σ])]
    rw [show (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤˣ) : ℝ) *
          ((if σ = 1 then (1:ℝ) else 0) * N.trace)) = N.trace from by
      rw [Finset.sum_eq_single 1]
      · simp [Equiv.Perm.sign_one]
      · intro σ _ hσ; rw [if_neg hσ]; ring
      · intro h; exact absurd (Finset.mem_univ 1) h]
  rw [hgoal] at hsum
  exact hsum

/-- **Jacobi's formula** at `t = 0` in general: `d/dt det (A + t • C) = det A * trace (A⁻¹ * C)`. -/
theorem hasDerivAt_det_add_smul (A C : Matrix (Fin m) (Fin m) ℝ) (hA : A.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (A + t • C).det) (A.det * (A⁻¹ * C).trace) 0 := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have heq : ∀ t : ℝ, (A + t • C).det = A.det * (1 + t • (A⁻¹ * C)).det := by
    intro t
    have h1 : A + t • C = A * (1 + t • (A⁻¹ * C)) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv A hunit, one_mul]
    rw [h1, Matrix.det_mul]
  have hcore := hasDerivAt_det_one_add_smul (A⁻¹ * C)
  have hcm := hcore.const_mul A.det
  exact hcm.congr_of_eventuallyEq (Filter.Eventually.of_forall heq)

/-- A determinant maximiser over a convex set satisfies the first-order optimality (trace)
condition. -/
theorem trace_le_of_isMaxOn_det {s : Set (Matrix (Fin m) (Fin m) ℝ)} (hs : Convex ℝ s)
    (A : Matrix (Fin m) (Fin m) ℝ) (hAs : A ∈ s) (hdA : 0 < A.det)
    (hmax : ∀ B ∈ s, B.det ≤ A.det) :
    ∀ B ∈ s, (A⁻¹ * B).trace ≤ (m : ℝ) := by
  intro B hB
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hdA)
  have hderiv : HasDerivAt (fun t : ℝ => (A + t • (B - A)).det)
      (A.det * (A⁻¹ * (B - A)).trace) 0 := hasDerivAt_det_add_smul A (B - A) (ne_of_gt hdA)
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ • ((A + t • (B - A)).det - A.det) ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have hconv : (1 - t) • A + t • B ∈ s := by
      exact hs hAs hB (show (0:ℝ) ≤ 1 - t by linarith) (show (0:ℝ) ≤ t by linarith)
        (show (1 - t) + t = 1 by ring)
    have hsm : (1 - t) • A + t • B = A + t • (B - A) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [hsm] at hconv
    have hle : (A + t • (B - A)).det ≤ A.det := hmax _ hconv
    have hsub : (A + t • (B - A)).det - A.det ≤ 0 := sub_nonpos.mpr hle
    have hinv : 0 < t⁻¹ := inv_pos.mpr ht0
    simpa using mul_nonpos_of_nonneg_of_nonpos hinv.le hsub
  have htend : Filter.Tendsto (fun t : ℝ => t⁻¹ • ((A + t • (B - A)).det - A.det))
      (𝓝[>] (0:ℝ)) (𝓝 (A.det * (A⁻¹ * (B - A)).trace)) := by
    simpa using hderiv.tendsto_slope_zero_right
  have hL : A.det * (A⁻¹ * (B - A)).trace ≤ 0 := le_of_tendsto htend hev
  have htrace : (A⁻¹ * (B - A)).trace ≤ 0 := by
    by_contra h
    push Not at h
    exact absurd hL (not_le.mpr (mul_pos hdA h))
  have hkey : (A⁻¹ * B).trace = (A⁻¹ * (B - A)).trace + (m : ℝ) := by
    have h1 : A⁻¹ * B = A⁻¹ * (B - A) + A⁻¹ * A := by
      rw [Matrix.mul_sub]; abel
    rw [h1, Matrix.trace_add, Matrix.nonsing_inv_mul A hunit, Matrix.trace_one, Fintype.card_fin]
  rw [hkey]
  linarith

/-! ## Elementary bounds for the gauge -/

/-- Two-sided comparison of the gauge of a compact `K` with `0` in its interior with the
Euclidean norm. -/
private lemma ellSq_gauge_bounds (K : Set (EuclideanSpace ℝ (Fin m))) (hKcpt : IsCompact K)
    (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K) :
    ∃ cu R : ℝ, 0 < cu ∧ 0 < R ∧ (∀ y, gauge K y ≤ cu * ‖y‖) ∧ (∀ y, ‖y‖ ≤ R * gauge K y) := by
  obtain ⟨r, hrpos, hrsub⟩ : ∃ r > 0, Metric.ball (0 : EuclideanSpace ℝ (Fin m)) r ⊆ K :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hK0)
  obtain ⟨R₀, _, hR₀⟩ := Commons.GeometryOfNumbers.exists_norm_bound_of_isCompact hKcpt
  refine ⟨r⁻¹, max R₀ 1, inv_pos.mpr hrpos, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_, ?_⟩
  · intro y
    have h := mul_gauge_le_norm (s := K) (r := r) (x := y) hrsub
    have h' : gauge K y * r ≤ ‖y‖ := by rwa [mul_comm] at h
    have h1 : gauge K y ≤ ‖y‖ / r := (le_div_iff₀ hrpos).mpr h'
    rwa [div_eq_inv_mul] at h1
  · intro y
    have hRpos : 0 < max R₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hsub : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (max R₀ 1) := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_trans (hR₀ z hz) (le_max_left _ _)
    have habs : Absorbent ℝ K := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp hK0)
    have hmono : gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (max R₀ 1)) y
        ≤ gauge K y := gauge_mono habs hsub y
    rw [gauge_closedBall hRpos.le y, div_le_iff₀ hRpos] at hmono
    calc ‖y‖ ≤ gauge K y * max R₀ 1 := hmono
      _ = max R₀ 1 * gauge K y := by ring

private lemma ellSq_norm_sq_toLpLin (B : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖Matrix.toLpLin 2 2 B x‖ ^ 2 = ∑ i : Fin m, (∑ j : Fin m, B i j * x.ofLp j) ^ 2 := by
  rw [Matrix.toLpLin_apply, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [WithLp.ofLp_toLp]
  simp only [Matrix.mulVec, dotProduct]
  rw [Real.norm_eq_abs, sq_abs]

private lemma ellSq_norm_sq_toLpLin_le (B : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖Matrix.toLpLin 2 2 B x‖ ^ 2 ≤ (∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2) * ‖x‖ ^ 2 := by
  rw [ellSq_norm_sq_toLpLin]
  have hx : ∑ j : Fin m, x.ofLp j ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl (fun j _ => by rw [Real.norm_eq_abs, sq_abs])
  calc ∑ i : Fin m, (∑ j : Fin m, B i j * x.ofLp j) ^ 2
      ≤ ∑ i : Fin m, (∑ j : Fin m, (B i j) ^ 2) * (∑ j : Fin m, x.ofLp j ^ 2) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
          (fun j => B i j) (fun j => x.ofLp j)
        simpa using this
    _ = ∑ i : Fin m, (∑ j : Fin m, (B i j) ^ 2) * ‖x‖ ^ 2 := by rw [hx]
    _ = (∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2) * ‖x‖ ^ 2 := by rw [Finset.sum_mul]

private lemma ellSq_continuous_toLpLin_fst (B : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin m) => Matrix.toLpLin 2 2 B x) :=
  LinearMap.continuous_of_finiteDimensional (Matrix.toLpLin 2 2 B)

/-! ## The Gaussian-weighted squared gauge -/

/-- The Gaussian-weighted squared gauge `∫ x, gauge K (B x)² exp(-π‖x‖²) dx`. -/
def ellSqGauss (K : Set (EuclideanSpace ℝ (Fin m))) (B : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin m),
    (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)

private lemma ellSq_integrable (K : Set (EuclideanSpace ℝ (Fin m)))
    (hKcvx : Convex ℝ K) (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K)
    (cu : ℝ) (hup : ∀ y, gauge K y ≤ cu * ‖y‖) (B : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin m) =>
      (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
  have hgc : Continuous (gauge K) :=
    continuous_gauge hKcvx (mem_interior_iff_mem_nhds.mp hK0)
  refine Integrable.mono'
    ((Commons.GeometryOfNumbers.integrable_norm_sq_exp_pi (n := m)).const_mul
      (cu ^ 2 * (∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2))) ?_ ?_
  · exact (((hgc.comp (ellSq_continuous_toLpLin_fst B)).pow 2).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := ellSq_norm_sq_toLpLin_le B x
    have h1 : gauge K (Matrix.toLpLin 2 2 B x) ^ 2
        ≤ cu ^ 2 * (∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2) * ‖x‖ ^ 2 := by
      have h2 : gauge K (Matrix.toLpLin 2 2 B x) ≤ cu * ‖Matrix.toLpLin 2 2 B x‖ := hup _
      have h3 : 0 ≤ gauge K (Matrix.toLpLin 2 2 B x) := gauge_nonneg _
      calc gauge K (Matrix.toLpLin 2 2 B x) ^ 2 ≤ (cu * ‖Matrix.toLpLin 2 2 B x‖) ^ 2 :=
            pow_le_pow_left₀ h3 h2 2
        _ = cu ^ 2 * ‖Matrix.toLpLin 2 2 B x‖ ^ 2 := by ring
        _ ≤ cu ^ 2 * ((∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2) * ‖x‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hb (sq_nonneg cu)
        _ = cu ^ 2 * (∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2) * ‖x‖ ^ 2 := by ring
    calc gauge K (Matrix.toLpLin 2 2 B x) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
        ≤ (cu ^ 2 * (∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2) * ‖x‖ ^ 2)
            * Real.exp (-Real.pi * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = cu ^ 2 * (∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2)
            * (‖x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by ring

/-- Coercivity of `ellSqGauss`. -/
private lemma ellSq_coercivity (K : Set (EuclideanSpace ℝ (Fin m))) (hKcpt : IsCompact K)
    (hKcvx : Convex ℝ K) (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K) :
    ∃ c : ℝ, 0 < c ∧ ∀ B : Matrix (Fin m) (Fin m) ℝ,
      c * (∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2) ≤ ellSqGauss K B := by
  obtain ⟨cu, R, hcu, hR, hup, hlow⟩ := ellSq_gauge_bounds K hKcpt hK0
  refine ⟨1 / (2 * Real.pi * R ^ 2), by positivity, fun B => ?_⟩
  have hpt : ∀ x : EuclideanSpace ℝ (Fin m),
      (‖Matrix.toLpLin 2 2 B x‖ / R) ^ 2
        ≤ (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 := by
    intro x
    have h1 : ‖Matrix.toLpLin 2 2 B x‖ / R ≤ gauge K (Matrix.toLpLin 2 2 B x) :=
      (div_le_iff₀ hR).mpr (by simpa [mul_comm] using hlow (Matrix.toLpLin 2 2 B x))
    exact pow_le_pow_left₀ (by positivity) h1 2
  calc 1 / (2 * Real.pi * R ^ 2) * ∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2
      = 1 / R ^ 2 * ((1 / (2 * Real.pi)) * ∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2) := by
          ring
    _ = 1 / R ^ 2 * ∫ x : EuclideanSpace ℝ (Fin m),
          ‖Matrix.toLpLin 2 2 B x‖ ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
          rw [integral_norm_sq_toLpLin_gaussian]
    _ = ∫ x : EuclideanSpace ℝ (Fin m),
          (‖Matrix.toLpLin 2 2 B x‖ / R) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          ring
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin m),
          (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
          exact integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun x => by positivity))
            (ellSq_integrable K hKcvx hK0 cu hup B)
            (Filter.Eventually.of_forall (fun x =>
              mul_le_mul_of_nonneg_right (hpt x) (Real.exp_pos _).le))
    _ = ellSqGauss K B := rfl

/-- The Gaussian-weighted squared gauge is continuous. -/
lemma continuous_ellSqGauss (K : Set (EuclideanSpace ℝ (Fin m))) (hKcvx : Convex ℝ K)
    (hKcpt : IsCompact K) (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K) :
    Continuous (ellSqGauss K) := by
  rw [continuous_iff_continuousAt]
  intro B₀
  set ρ : ℝ := (∑ i : Fin m, ∑ j : Fin m, |B₀ i j|) + 1 with hρdef
  have hB0le : ∀ i j, |B₀ i j| < ρ := by
    intro i j
    have h1a : |B₀ i j| ≤ ∑ j' : Fin m, |B₀ i j'| :=
      Finset.single_le_sum (f := fun j' => |B₀ i j'|) (fun j' _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h1b : (∑ j' : Fin m, |B₀ i j'|) ≤ ∑ i' : Fin m, ∑ j' : Fin m, |B₀ i' j'| :=
      Finset.single_le_sum (f := fun i' => ∑ j' : Fin m, |B₀ i' j'|)
        (fun i' _ => Finset.sum_nonneg (fun j' _ => abs_nonneg _)) (Finset.mem_univ i)
    rw [hρdef]; linarith
  have hbox_nhds : {B : Matrix (Fin m) (Fin m) ℝ | ∀ i j, |B i j| ≤ ρ} ∈ 𝓝 B₀ := by
    have hopen : IsOpen {B : Matrix (Fin m) (Fin m) ℝ | ∀ i j, |B i j| < ρ} := by
      have heq : {B : Matrix (Fin m) (Fin m) ℝ | ∀ i j, |B i j| < ρ}
          = ⋂ i : Fin m, ⋂ j : Fin m, {B : Matrix (Fin m) (Fin m) ℝ | |B i j| < ρ} := by
        ext B; simp
      rw [heq]
      refine isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j => ?_))
      have hcontij : Continuous (fun B : Matrix (Fin m) (Fin m) ℝ => |B i j|) := by fun_prop
      exact isOpen_Iio.preimage hcontij
    exact Filter.mem_of_superset (hopen.mem_nhds hB0le) (fun B hB i j => le_of_lt (hB i j))
  have hcont := continuousOn_integral_gauge_sq_gaussian K hKcpt hKcvx hK0 ρ
  have hfun : ellSqGauss K = fun B : Matrix (Fin m) (Fin m) ℝ =>
      ∫ x : EuclideanSpace ℝ (Fin m),
        (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) := rfl
  rw [hfun]
  exact hcont.continuousAt hbox_nhds

/-- Pointwise subadditivity-type convexity inequality for the gauge. -/
private lemma ellSq_gauge_convex_le (K : Set (EuclideanSpace ℝ (Fin m))) (hKcvx : Convex ℝ K)
    (hKabs : Absorbent ℝ K) (A B : Matrix (Fin m) (Fin m) ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x : EuclideanSpace ℝ (Fin m)) :
    gauge K (Matrix.toLpLin 2 2 (a • A + b • B) x)
      ≤ a * gauge K (Matrix.toLpLin 2 2 A x) + b * gauge K (Matrix.toLpLin 2 2 B x) := by
  have hx : Matrix.toLpLin 2 2 (a • A + b • B) x
      = a • (Matrix.toLpLin 2 2 A x) + b • (Matrix.toLpLin 2 2 B x) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [hx]
  calc gauge K (a • (Matrix.toLpLin 2 2 A x) + b • (Matrix.toLpLin 2 2 B x))
      ≤ gauge K (a • (Matrix.toLpLin 2 2 A x)) + gauge K (b • (Matrix.toLpLin 2 2 B x)) :=
        gauge_add_le hKcvx hKabs _ _
    _ = a * gauge K (Matrix.toLpLin 2 2 A x) + b * gauge K (Matrix.toLpLin 2 2 B x) := by
        rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb, smul_eq_mul, smul_eq_mul]

/-- Convexity of `ellSqGauss`. -/
lemma ellSqGauss_convex_aux (K : Set (EuclideanSpace ℝ (Fin m))) (hKcvx : Convex ℝ K)
    (hKcpt : IsCompact K) (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K)
    (A B : Matrix (Fin m) (Fin m) ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ellSqGauss K (a • A + b • B) ≤ a * ellSqGauss K A + b * ellSqGauss K B := by
  obtain ⟨cu, R, hcu, hR, hup, hlow⟩ := ellSq_gauge_bounds K hKcpt hK0
  have hKabs : Absorbent ℝ K := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp hK0)
  have hIA : Integrable (fun x : EuclideanSpace ℝ (Fin m) =>
      (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) :=
    ellSq_integrable K hKcvx hK0 cu hup A
  have hIB : Integrable (fun x : EuclideanSpace ℝ (Fin m) =>
      (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) :=
    ellSq_integrable K hKcvx hK0 cu hup B
  have hI2 : Integrable (fun x : EuclideanSpace ℝ (Fin m) =>
      a * ((gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
        + b * ((gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))) :=
    (hIA.const_mul a).add (hIB.const_mul b)
  have hpt : ∀ x : EuclideanSpace ℝ (Fin m),
      (gauge K (Matrix.toLpLin 2 2 (a • A + b • B) x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
        ≤ a * ((gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
          + b * ((gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
    intro x
    set p : ℝ := gauge K (Matrix.toLpLin 2 2 A x) with hp
    set q : ℝ := gauge K (Matrix.toLpLin 2 2 B x) with hq
    have hp0 : 0 ≤ p := gauge_nonneg _
    have hq0 : 0 ≤ q := gauge_nonneg _
    have hsub := ellSq_gauge_convex_le K hKcvx hKabs A B a b ha hb x
    rw [← hp, ← hq] at hsub
    have hsq : (gauge K (Matrix.toLpLin 2 2 (a • A + b • B) x)) ^ 2 ≤ (a * p + b * q) ^ 2 :=
      pow_le_pow_left₀ (gauge_nonneg _) hsub 2
    have hsq2 : (a * p + b * q) ^ 2 ≤ a * p ^ 2 + b * q ^ 2 := by
      nlinarith [sq_nonneg (p - q), sq_nonneg p, sq_nonneg q, ha, hb, hab,
        mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p - q))]
    have hexp : 0 < Real.exp (-Real.pi * ‖x‖ ^ 2) := Real.exp_pos _
    calc (gauge K (Matrix.toLpLin 2 2 (a • A + b • B) x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
        ≤ (a * p + b * q) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hsq hexp.le
      _ ≤ (a * p ^ 2 + b * q ^ 2) * Real.exp (-Real.pi * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hsq2 hexp.le
      _ = a * (p ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
            + b * (q ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by ring
      _ = a * ((gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
            + b * ((gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
          rw [hp, hq]
  calc ellSqGauss K (a • A + b • B)
      = ∫ x : EuclideanSpace ℝ (Fin m),
          (gauge K (Matrix.toLpLin 2 2 (a • A + b • B) x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) :=
        rfl
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin m),
          (a * ((gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
            + b * ((gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => by positivity)) hI2
          (Filter.Eventually.of_forall hpt)
    _ = a * (∫ x : EuclideanSpace ℝ (Fin m),
            (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
          + b * (∫ x : EuclideanSpace ℝ (Fin m),
            (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
        rw [integral_add (hIA.const_mul a) (hIB.const_mul b), integral_const_mul, integral_const_mul]
    _ = a * ellSqGauss K A + b * ellSqGauss K B := rfl

/-- Homogeneity of `ellSqGauss` in the matrix argument. -/
lemma ellSqGauss_smul (K : Set (EuclideanSpace ℝ (Fin m))) (c : ℝ) (hc : 0 ≤ c)
    (B : Matrix (Fin m) (Fin m) ℝ) :
    ellSqGauss K (c • B) = c ^ 2 * ellSqGauss K B := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin m),
      gauge K (Matrix.toLpLin 2 2 (c • B) x) = c * gauge K (Matrix.toLpLin 2 2 B x) := by
    intro x
    rw [show Matrix.toLpLin 2 2 (c • B) x = c • (Matrix.toLpLin 2 2 B x) by
      simp only [map_smul, LinearMap.smul_apply]]
    rw [gauge_smul_of_nonneg hc, smul_eq_mul]
  rw [ellSqGauss]
  rw [show (∫ x : EuclideanSpace ℝ (Fin m),
        (gauge K (Matrix.toLpLin 2 2 (c • B) x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ∫ x : EuclideanSpace ℝ (Fin m),
        c ^ 2 * ((gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) from by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show gauge K (Matrix.toLpLin 2 2 (c • B) x) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
      = c ^ 2 * (gauge K (Matrix.toLpLin 2 2 B x) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
    rw [hpt x]; ring]
  rw [integral_const_mul, ellSqGauss]

/-- The closed box of matrices with entries bounded by `ρ`. -/
private def ellSqBox (ρ : ℝ) : Set (Matrix (Fin m) (Fin m) ℝ) := {B | ∀ i j, |B i j| ≤ ρ}

private lemma isCompact_ellSqBox (ρ : ℝ) : IsCompact (ellSqBox (m := m) ρ) := by
  have h : ellSqBox (m := m) ρ
      = Set.pi Set.univ (fun _ : Fin m => Set.pi Set.univ (fun _ : Fin m => Set.Icc (-ρ) ρ)) := by
    ext B; constructor
    · intro hB i _ j _; exact abs_le.mp (hB i j)
    · intro hB i j; exact abs_le.mpr (hB i (trivial) j (trivial))
  rw [h]
  exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))

/-- **The determinant maximiser.** For every `τ > 0` there is a matrix `C` of positive determinant
with `ellSqGauss K C ≤ τ` maximising the determinant on the sublevel set, and satisfying the
first-order (trace) optimality condition. -/
theorem exists_ellSq_max (K : Set (EuclideanSpace ℝ (Fin m))) (hKcvx : Convex ℝ K)
    (hKcpt : IsCompact K) (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : Matrix (Fin m) (Fin m) ℝ, C.det > 0 ∧ ellSqGauss K C ≤ τ ∧
      (∀ B, ellSqGauss K B ≤ τ → B.det ≤ C.det) ∧
      (∀ B, ellSqGauss K B ≤ τ → (C⁻¹ * B).trace ≤ (m : ℝ)) := by
  obtain ⟨c, hcpos, hcoerc⟩ := ellSq_coercivity K hKcpt hKcvx hK0
  have hcont : Continuous (ellSqGauss K) := continuous_ellSqGauss K hKcvx hKcpt hK0
  have hclosed : IsClosed {B : Matrix (Fin m) (Fin m) ℝ | ellSqGauss K B ≤ τ} :=
    isClosed_le hcont continuous_const
  have hzero : ellSqGauss K 0 = 0 := by
    rw [ellSqGauss]
    have h : (fun x : EuclideanSpace ℝ (Fin m) =>
        (gauge K (Matrix.toLpLin 2 2 (0 : Matrix (Fin m) (Fin m) ℝ) x)) ^ 2
          * Real.exp (-Real.pi * ‖x‖ ^ 2)) = fun _ => 0 := by
      funext x
      simp [gauge_zero]
    rw [h, integral_zero]
  have hsub : {B : Matrix (Fin m) (Fin m) ℝ | ellSqGauss K B ≤ τ}
      ⊆ ellSqBox (m := m) (Real.sqrt (τ / c)) := by
    intro B hB i j
    have h1 : (B i j) ^ 2 ≤ ∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2 := by
      refine le_trans (Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ j)) ?_
      exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
        (Finset.mem_univ i)
    have h2 : ∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2 ≤ τ / c := by
      have h := hcoerc B
      rw [le_div_iff₀ hcpos]
      calc (∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2) * c
          = c * (∑ i : Fin m, ∑ j : Fin m, (B i j) ^ 2) := by ring
        _ ≤ ellSqGauss K B := h
        _ ≤ τ := hB
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (le_trans h1 h2)
  have hcpt : IsCompact {B : Matrix (Fin m) (Fin m) ℝ | ellSqGauss K B ≤ τ} :=
    (isCompact_ellSqBox (m := m) (Real.sqrt (τ / c))).of_isClosed_subset hclosed hsub
  have hne : {B : Matrix (Fin m) (Fin m) ℝ | ellSqGauss K B ≤ τ}.Nonempty :=
    ⟨0, by change ellSqGauss K 0 ≤ τ; rw [hzero]; exact hτ.le⟩
  have hdetcont : ContinuousOn (fun B : Matrix (Fin m) (Fin m) ℝ => B.det)
      {B : Matrix (Fin m) (Fin m) ℝ | ellSqGauss K B ≤ τ} :=
    (continuous_id.matrix_det : Continuous (fun B : Matrix (Fin m) (Fin m) ℝ => B.det)).continuousOn
  obtain ⟨C, hCmem, hCmax⟩ := hcpt.exists_isMaxOn hne hdetcont
  have hconv : Convex ℝ {B : Matrix (Fin m) (Fin m) ℝ | ellSqGauss K B ≤ τ} := by
    intro A hA B hB a b ha hb hab
    change ellSqGauss K (a • A + b • B) ≤ τ
    have hA' : ellSqGauss K A ≤ τ := hA
    have hB' : ellSqGauss K B ≤ τ := hB
    have h1 := ellSqGauss_convex_aux K hKcvx hKcpt hK0 A B a b ha hb hab
    have h2 : a * ellSqGauss K A + b * ellSqGauss K B ≤ τ := by
      have h3 := add_le_add (mul_le_mul_of_nonneg_left hA' ha) (mul_le_mul_of_nonneg_left hB' hb)
      rwa [← add_mul, hab, one_mul] at h3
    exact le_trans h1 h2
  have hCdetpos : 0 < C.det := by
    set J1 : ℝ := ellSqGauss K 1 with hJ1
    have hJ1nn : 0 ≤ J1 := by
      rw [hJ1, ellSqGauss]
      exact integral_nonneg (fun x => by positivity)
    set ε : ℝ := Real.sqrt (τ / (J1 + 1)) with hε
    have hεpos : 0 < ε := Real.sqrt_pos.mpr (by positivity)
    have hε2 : ε ^ 2 = τ / (J1 + 1) := Real.sq_sqrt (by positivity)
    have hmemε : ellSqGauss K (ε • 1) ≤ τ := by
      rw [ellSqGauss_smul K ε hεpos.le, hε2, hJ1]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < J1 + 1)]
      nlinarith [hτ]
    have hdetε : 0 < (ε • (1 : Matrix (Fin m) (Fin m) ℝ)).det := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
      exact pow_pos hεpos m
    exact lt_of_lt_of_le hdetε (hCmax hmemε)
  exact ⟨C, hCdetpos, hCmem, fun B hB => hCmax hB,
    fun B hB => trace_le_of_isMaxOn_det hconv C hCmem hCdetpos (fun D hD => hCmax hD) B hB⟩

/-! ## Change of variables: relating the two Gaussian normalisations -/

/-- The change of variables `x ↦ √(2π) x` relating the Gaussian `exp(-‖x‖²/2)` to the
normalised Gaussian `exp(-π‖x‖²)`. -/
lemma ellSq_transfer (K : Set (EuclideanSpace ℝ (Fin m))) (A : Matrix (Fin m) (Fin m) ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin m),
        (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2))
      = (Real.sqrt (2 * Real.pi)) ^ m * ellSqGauss K (Real.sqrt (2 * Real.pi) • A) := by
  set R : ℝ := Real.sqrt (2 * Real.pi) with hR
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hRsq : R ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  set f : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun x => (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) with hf
  have hcomp := MeasureTheory.Measure.integral_comp_smul
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin m)))) f R
  rw [finrank_euclideanSpace, Fintype.card_fin] at hcomp
  rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hRpos.le m)), smul_eq_mul] at hcomp
  -- hcomp : ∫ x, f (R • x) = (R ^ m)⁻¹ * ∫ x, f x
  have key : (∫ x : EuclideanSpace ℝ (Fin m), f (R • x)) = ellSqGauss K (R • A) := by
    rw [ellSqGauss]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hsm : Matrix.toLpLin 2 2 A (R • x) = Matrix.toLpLin 2 2 (R • A) x := by
      simp only [map_smul, LinearMap.smul_apply]
    have hnorm : ‖R • x‖ ^ 2 = 2 * Real.pi * ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos, mul_pow, hRsq]
    show (gauge K (Matrix.toLpLin 2 2 A (R • x))) ^ 2 * Real.exp (-‖R • x‖ ^ 2 / 2)
      = (gauge K (Matrix.toLpLin 2 2 (R • A) x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
    rw [hsm, hnorm, show -(2 * Real.pi * ‖x‖ ^ 2) / 2 = -Real.pi * ‖x‖ ^ 2 by ring]
  rw [key] at hcomp
  rw [hcomp]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero m (ne_of_gt hRpos)), one_mul]

/-! ## The Lewis ellipsoid theorem -/

/-- **Lewis's ellipsoid, existence form.** For a compact convex `K ⊆ ℝᵐ` with `0` in its
interior there is a matrix `A` of positive determinant such that `A` maximises the determinant
among all matrices `B` with `∫ gauge K (B x)² exp(-‖x‖²/2) ≤ 1`, and such that the first-order
optimality condition `trace (A⁻¹ B) ≤ m` holds for every such `B`. -/
theorem lewis_ellNorm_max {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hKcvx : Convex ℝ K)
    (hKsymm : (-K : Set (EuclideanSpace ℝ (Fin m))) = K) (hKcpt : IsCompact K)
    (hK0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K) :
    ∃ A : Matrix (Fin m) (Fin m) ℝ, A.det > 0 ∧
      (∫ x : EuclideanSpace ℝ (Fin m),
        (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) ≤ 1 ∧
      (∀ B : Matrix (Fin m) (Fin m) ℝ,
        (∫ x : EuclideanSpace ℝ (Fin m),
          (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) ≤ 1 →
        B.det ≤ A.det) ∧
      (∀ B : Matrix (Fin m) (Fin m) ℝ,
        (∫ x : EuclideanSpace ℝ (Fin m),
          (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) ≤ 1 →
        Matrix.trace (A⁻¹ * B) ≤ (m : ℝ)) ∧
      Matrix.trace (A⁻¹ * A) = (m : ℝ) := by
  classical
  set R : ℝ := Real.sqrt (2 * Real.pi) with hR
  have hRpos : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have hτpos : 0 < (R ^ m)⁻¹ := inv_pos.mpr (pow_pos hRpos m)
  obtain ⟨C, hCdet, hCJ, hCmax, hCtr⟩ := exists_ellSq_max K hKcvx hKcpt hK0 (R ^ m)⁻¹ hτpos
  have hdetA : 0 < (R⁻¹ • C).det := by
    rw [Matrix.det_smul, Fintype.card_fin]
    exact mul_pos (pow_pos (inv_pos.mpr hRpos) m) hCdet
  have hred : ∀ B : Matrix (Fin m) (Fin m) ℝ,
      (∫ x : EuclideanSpace ℝ (Fin m),
        (gauge K (Matrix.toLpLin 2 2 B x)) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2)) ≤ 1 →
      ellSqGauss K (R • B) ≤ (R ^ m)⁻¹ := by
    intro B hB
    rw [ellSq_transfer] at hB
    rw [inv_eq_one_div]
    refine (le_div_iff₀ (pow_pos hRpos m)).mpr ?_
    rwa [mul_comm] at hB
  refine ⟨R⁻¹ • C, hdetA, ?_, ?_, ?_, ?_⟩
  · rw [ellSq_transfer, smul_smul, mul_inv_cancel₀ hRne, one_smul]
    have h : R ^ m * ellSqGauss K C ≤ R ^ m * (R ^ m)⁻¹ :=
      mul_le_mul_of_nonneg_left hCJ (pow_nonneg hRpos.le m)
    rwa [mul_inv_cancel₀ (pow_ne_zero m hRne)] at h
  · intro B hB
    have hCB := hCmax (R • B) (hred B hB)
    have h1 : R ^ m * B.det ≤ C.det := by
      rwa [Matrix.det_smul, Fintype.card_fin] at hCB
    rw [Matrix.det_smul, Fintype.card_fin]
    calc B.det = (R ^ m)⁻¹ * (R ^ m * B.det) := by
          rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hRne), one_mul]
      _ ≤ (R ^ m)⁻¹ * C.det :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (pow_nonneg hRpos.le m))
      _ = (R⁻¹) ^ m * C.det := by rw [← inv_pow]
  · intro B hB
    have hCB := hCtr (R • B) (hred B hB)
    have hAinv : (R⁻¹ • C)⁻¹ = R • C⁻¹ := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul,
          Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.mpr (ne_of_gt hCdet)), smul_smul,
          inv_mul_cancel₀ hRne, one_smul]
    have heq : (R⁻¹ • C)⁻¹ * B = C⁻¹ * (R • B) := by
      rw [hAinv, Matrix.smul_mul, Matrix.mul_smul]
    rwa [heq]
  · rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt hdetA)), Matrix.trace_one,
        Fintype.card_fin]

end

end Commons.GeometryOfNumbers.EllNorm
