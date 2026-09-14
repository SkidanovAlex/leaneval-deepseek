import Submission.NBody.MarchalModelTwoSided

/-!
# The good direction

For the symmetric bump to be a legal competitor, the displacement `δ` must not be *parallel* to a
pair separation `s̄ i₀ - s̄ j` of the limit shape: otherwise the bumped parabolic profile meets a
collision (and the pair potential gain ceases to be integrable).  The directions parallel to a fixed
non-zero vector `u` form a **null** set of angles (the solutions of `α cos θ + β sin θ = ±‖u‖`), so
the circle-average negativity of `exists_model_dir_negative_two_sided_avoid` can be combined with the
avoidance of these sets.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **Bessel for an orthonormal pair**: `⟪u,e⟫² + ⟪u,f⟫² ≤ ‖u‖²`. -/
lemma bessel_pair {u e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0) :
    (inner ℝ u e)^2 + (inner ℝ u f)^2 ≤ ‖u‖^2 := by
  have hef' : inner ℝ f e = 0 := by rw [real_inner_comm]; exact hef
  set A : ℝ := inner ℝ u e with hAy
  set B : ℝ := inner ℝ u f with hBy
  have hnsq : ‖A • e + B • f‖^2 = A^2 + B^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, he, hf, hef, hef', mul_one,
      mul_zero, add_zero]
    rw [sq_abs, sq_abs]; ring
  have horth : inner ℝ (u - (A • e + B • f)) (A • e + B • f) = 0 := by
    rw [inner_sub_left]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, he, hf, hef, hef', mul_one,
      mul_zero, add_zero]
    rw [sq_abs, sq_abs]
    simp only [hAy, hBy]
    ring
  have h := norm_add_sq_real (u - (A • e + B • f)) (A • e + B • f)
  rw [sub_add_cancel, horth, hnsq] at h
  nlinarith [sq_nonneg ‖u - (A • e + B • f)‖]

/-- **The bad directions are null.**  The set of angles `θ` for which the unit direction in the
plane `(e,f)` is parallel to a fixed non-zero vector `u` has measure zero. -/
theorem volume_badSet_eq_zero {u : E} (hu : u ≠ 0) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) :
    volume {θ : ℝ | (inner ℝ u (circleDir e f θ))^2 = ‖u‖^2} = 0 := by
  set A : ℝ := inner ℝ u e with hAy
  set B : ℝ := inner ℝ u f with hBy
  by_cases hz : A = 0 ∧ B = 0
  · have hemp : {θ : ℝ | (inner ℝ u (circleDir e f θ))^2 = ‖u‖^2} = ∅ := by
      ext θ
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro h
      have hval : inner ℝ u (circleDir e f θ) = 0 := by
        rw [circleDir, inner_add_right, real_inner_smul_right, real_inner_smul_right]
        rw [show inner ℝ u e = 0 from hz.1, show inner ℝ u f = 0 from hz.2]
        ring
      rw [hval] at h
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
      exact hu (norm_eq_zero.mp (sq_eq_zero_iff.mp h.symm))
    rw [hemp]; exact measure_empty
  · have hAorB : A ≠ 0 ∨ B ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hz ⟨hcon.1, hcon.2⟩
    have hrpos : 0 < Real.sqrt (A^2 + B^2) :=
      Real.sqrt_pos.mpr (by rcases hAorB with h | h <;> positivity)
    obtain ⟨φ, hφc, hφs⟩ := exists_cos_sin_polar A B
    have hkey : ∀ θ : ℝ, inner ℝ u (circleDir e f θ)
        = Real.sqrt (A^2 + B^2) * Real.cos (θ - φ) := by
      intro θ
      have hrs : Real.sqrt (A^2 + B^2) * Real.cos (θ - φ)
          = Real.sqrt (A^2 + B^2) * Real.cos φ * Real.cos θ
            + Real.sqrt (A^2 + B^2) * Real.sin φ * Real.sin θ := by
        rw [Real.cos_sub]; ring
      rw [circleDir, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        show inner ℝ u e = A from hAy.symm, show inner ℝ u f = B from hBy.symm, hrs,
        ← hφc, ← hφs]
      ring
    have hsub : {θ : ℝ | (inner ℝ u (circleDir e f θ))^2 = ‖u‖^2} ⊆
        {θ : ℝ | Real.cos (θ - φ) = 1} ∪ {θ : ℝ | Real.cos (θ - φ) = -1} := by
      intro θ hθ
      have h1 : (Real.sqrt (A^2 + B^2) * Real.cos (θ - φ))^2 = ‖u‖^2 := by
        rw [← hkey θ]; exact hθ
      have hbess : A^2 + B^2 ≤ ‖u‖^2 := bessel_pair he hf hef
      have hr2 : Real.sqrt (A^2 + B^2)^2 = A^2 + B^2 := Real.sq_sqrt (by positivity)
      have hcos2 : Real.cos (θ - φ)^2 = 1 := by
        have hun : (Real.sqrt (A^2 + B^2))^2 * Real.cos (θ - φ)^2 = ‖u‖^2 := by
          rw [← mul_pow]; exact h1
        have hr2pos : (0:ℝ) < Real.sqrt (A^2 + B^2)^2 := by
          rw [hr2]; rcases hAorB with h | h <;> positivity
        have hge : 1 ≤ Real.cos (θ - φ)^2 := by
          nlinarith [hun, hbess, hr2, hr2pos]
        have hle : Real.cos (θ - φ)^2 ≤ 1 := by
          nlinarith [Real.sin_sq_add_cos_sq (θ - φ), sq_nonneg (Real.sin (θ - φ))]
        linarith
      rcases sq_eq_one_iff.mp hcos2 with h | h
      · left; exact h
      · right; exact h
    refine measure_mono_null hsub ?_
    rw [measure_union_null_iff]
    constructor
    · have hr : {θ : ℝ | Real.cos (θ - φ) = 1}
          = Set.range (fun k : ℤ => φ + k * (2 * Real.pi)) := by
        ext θ
        simp only [mem_setOf_eq, Set.mem_range]
        rw [Real.cos_eq_one_iff]
        constructor
        · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩
        · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩
      rw [hr]; exact (Set.countable_range _).measure_zero volume
    · have hr : {θ : ℝ | Real.cos (θ - φ) = -1}
          = Set.range (fun k : ℤ => φ + Real.pi + k * (2 * Real.pi)) := by
        ext θ
        simp only [mem_setOf_eq, Set.mem_range]
        rw [Real.cos_eq_neg_one_iff]
        constructor
        · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩
        · rintro ⟨n, hn⟩; exact ⟨n, by linarith⟩
      rw [hr]; exact (Set.countable_range _).measure_zero volume

/-- **The Cauchy--Schwarz bound along the circle.** -/
theorem inner_circleDir_sq_le {u e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) (θ : ℝ) :
    (inner ℝ u (circleDir e f θ))^2 ≤ ‖u‖^2 := by
  have hval : inner ℝ u (circleDir e f θ)
      = Real.cos θ * inner ℝ u e + Real.sin θ * inner ℝ u f := by
    rw [circleDir, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [hval]
  have h1 : (Real.cos θ * inner ℝ u e + Real.sin θ * inner ℝ u f)^2
      ≤ (inner ℝ u e)^2 + (inner ℝ u f)^2 := by
    nlinarith [sq_nonneg (Real.sin θ * inner ℝ u e - Real.cos θ * inner ℝ u f),
      Real.sin_sq_add_cos_sq θ]
  linarith [bessel_pair (u := u) he hf hef]

/-- **The good direction condition.**  If `θ` is not a bad direction for `u` then
`δ = ρ • circleDir e f θ` is not parallel to `u`. -/
theorem goodDir_of_notMem_badSet {u : E} (hu : u ≠ 0) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = 0) {ρ : ℝ} (hρ : 0 < ρ) {θ : ℝ}
    (hθ : θ ∉ {θ : ℝ | (inner ℝ u (circleDir e f θ))^2 = ‖u‖^2}) :
    (inner ℝ u (ρ • circleDir e f θ))^2 < ‖u‖^2 * ‖ρ • circleDir e f θ‖^2 := by
  have hnorm : ‖circleDir e f θ‖ = 1 := norm_circleDir he hf hef θ
  have hne : (inner ℝ u (circleDir e f θ))^2 ≠ ‖u‖^2 := hθ
  have hlt : (inner ℝ u (circleDir e f θ))^2 < ‖u‖^2 :=
    lt_of_le_of_ne (inner_circleDir_sq_le he hf hef θ) hne
  have h1 : inner ℝ u (ρ • circleDir e f θ) = ρ * inner ℝ u (circleDir e f θ) :=
    real_inner_smul_right _ _ _
  have h2 : ‖ρ • circleDir e f θ‖ = ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hnorm, mul_one]
  rw [h1, mul_pow, h2, mul_comm (‖u‖^2) (ρ^2)]
  exact mul_lt_mul_of_pos_left hlt (pow_pos hρ 2)

/-- The subset relation version: bad directions are exactly the non-good ones for `u ≠ 0`. -/
theorem badSet_subset_of_not_good {u : E} {e f : E} {ρ : ℝ} (hρ : 0 < ρ) {θ : ℝ}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0)
    (hbad : (inner ℝ u (ρ • circleDir e f θ))^2 = ‖u‖^2 * ‖ρ • circleDir e f θ‖^2) :
    θ ∈ {θ : ℝ | (inner ℝ u (circleDir e f θ))^2 = ‖u‖^2} := by
  have hnorm : ‖circleDir e f θ‖ = 1 := norm_circleDir he hf hef θ
  have h1 : inner ℝ u (ρ • circleDir e f θ) = ρ * inner ℝ u (circleDir e f θ) :=
    real_inner_smul_right _ _ _
  have h2 : ‖ρ • circleDir e f θ‖ = ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hnorm, mul_one]
  rw [h1, mul_pow, h2, mul_comm (‖u‖^2) (ρ^2)] at hbad
  exact mul_left_cancel₀ (ne_of_gt (pow_pos hρ 2)) hbad

end Submission.NBody
