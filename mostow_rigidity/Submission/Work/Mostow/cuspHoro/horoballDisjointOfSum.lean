import Mathlib
import Submission.Work.Mostow.cuspHoroDefs

namespace Work.Mostow.cuspHoro

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-!
# Disjointness of horoballs from the sum of their levels

For two distinct boundary points `ξ ≠ η` of `ℍⁿ` and levels `s t : ℝ`, the open horoballs
`horoball ξ s` and `horoball η t` are disjoint as soon as

`s + t ≤ log ((1 - ⟪ξ,η⟫)/2)`.

The mathematical content is the sharp lower bound for the sum of the two Busemann functions: for
*every* point `u` of the chart model,

`(tpart u - ⟪u,ξ⟫) * (tpart u - ⟪u,η⟫) ≥ (1 - ⟪ξ,η⟫)/2`,

i.e. `β_ξ u + β_η u ≥ log ((1 - ⟪ξ,η⟫)/2)`.  This is proved by pure linear algebra of the inner
product: from Cauchy–Schwarz applied to the pair `(u - ⟪u,η⟫·η, ξ - ⟪ξ,η⟫·η)` one gets

`‖u‖²(1 - c²) - a² - b² + 2abc ≥ 0`  (`a = ⟪u,ξ⟫`, `b = ⟪u,η⟫`, `c = ⟪ξ,η⟫`),

and a short expansion turns this into the claimed bound.  The case `c = -1` (i.e. `η = -ξ`,
geodesic through the base point) is treated separately.
-/

/-- Core horoball inequality: for unit vectors `ξ, η` with `⟪ξ,η⟫ > -1` and every `u`,
`(√(1+‖u‖²) - ⟪u,ξ⟫) (√(1+‖u‖²) - ⟪u,η⟫) ≥ (1 - ⟪ξ,η⟫)/2`. -/
private lemma core_lt {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (ξ η u : V) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hc : -1 < inner ℝ ξ η) :
    (1 - inner ℝ ξ η)/2 ≤
      (Real.sqrt (1 + ‖u‖^2) - inner ℝ u ξ) * (Real.sqrt (1 + ‖u‖^2) - inner ℝ u η) := by
  set a := inner ℝ u ξ with ha
  set b := inner ℝ u η with hb
  set c := inner ℝ ξ η with hcc
  set N := ‖u‖^2 with hN
  set T := Real.sqrt (1 + N) with hT
  have hT2 : T^2 = 1 + N := by rw [hT, hN]; exact Real.sq_sqrt (by positivity)
  -- Cauchy–Schwarz on `(u - b·η, ξ - c·η)`.
  have hvw : inner ℝ (u - b • η) (ξ - c • η) = a - c * b := by
    have A : inner ℝ u (ξ - c • η) = inner ℝ u ξ - c * inner ℝ u η := by
      rw [inner_sub_right, real_inner_smul_right]
    have hηw : inner ℝ η (ξ - c • η) = 0 := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hη]
      rw [← real_inner_comm η ξ, hcc]
      ring
    have B : inner ℝ (b • η) (ξ - c • η) = 0 := by
      rw [real_inner_smul_left, hηw, mul_zero]
    rw [inner_sub_left, A, B, sub_zero, ha, hb]
  have hv : inner ℝ (u - b • η) (u - b • η) = N - b^2 := by
    rw [real_inner_self_eq_norm_sq, norm_sub_sq_real, norm_smul, hη, mul_one,
        real_inner_smul_right, Real.norm_eq_abs, sq_abs]
    rw [hN, hb]
    ring
  have hw : inner ℝ (ξ - c • η) (ξ - c • η) = 1 - c^2 := by
    rw [real_inner_self_eq_norm_sq, norm_sub_sq_real, norm_smul, hη, mul_one,
        real_inner_smul_right, Real.norm_eq_abs, sq_abs, hξ, hcc]
    ring
  have hcs := real_inner_mul_inner_self_le (u - b • η) (ξ - c • η)
  rw [hvw, hv, hw] at hcs
  have hD : 0 ≤ N * (1 - c^2) - a^2 - b^2 + 2 * a * b * c := by nlinarith [hcs]
  -- The key algebraic identity, reducing the claim to `hD ≥ 0` and a square.
  have hkey : (1 + c) * (2 * (T - a) * (T - b) - (1 - c))
      = (a + b - (1 + c) * T)^2 + (N * (1 - c^2) - a^2 - b^2 + 2 * a * b * c) := by
    nlinarith [hT2]
  have hpos : 0 < 1 + c := by linarith
  have hmain : 0 ≤ 2 * (T - a) * (T - b) - (1 - c) := by
    have : 0 ≤ (1 + c) * (2 * (T - a) * (T - b) - (1 - c)) := by
      rw [hkey]; nlinarith [sq_nonneg (a + b - (1 + c) * T), hD]
    exact (mul_nonneg_iff_of_pos_left hpos).mp this
  rw [hT, ha, hb, hcc]
  linarith

/-- Core horoball inequality in the antipodal case `⟪ξ,η⟫ = -1` (so `η = -ξ`). -/
private lemma core_anti {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (ξ η u : V) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (hc : inner ℝ ξ η = -1) :
    (1 - inner ℝ ξ η)/2 ≤
      (Real.sqrt (1 + ‖u‖^2) - inner ℝ u ξ) * (Real.sqrt (1 + ‖u‖^2) - inner ℝ u η) := by
  have heta : η = -ξ := by
    have h0 : ‖ξ + η‖^2 = 0 := by rw [norm_add_sq_real, hξ, hη, hc]; norm_num
    have h1 : ‖ξ + η‖ = 0 := by nlinarith [h0, norm_nonneg (ξ + η)]
    have h2 : ξ + η = 0 := by simpa using (norm_eq_zero.mp h1)
    exact eq_neg_of_add_eq_zero_right h2
  subst heta
  have hξneg : inner ℝ ξ (-ξ) = -1 := by
    rw [inner_neg_right, real_inner_self_eq_norm_sq, hξ]; ring
  have hune : inner ℝ u (-ξ) = - inner ℝ u ξ := inner_neg_right u ξ
  rw [hξneg, hune]
  have hT2 : Real.sqrt (1 + ‖u‖^2)^2 = 1 + ‖u‖^2 := Real.sq_sqrt (by positivity)
  have ha : (inner ℝ u ξ)^2 ≤ ‖u‖^2 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) u ξ
    rw [hξ, mul_one, Real.norm_eq_abs] at h
    nlinarith [h, abs_nonneg (inner ℝ u ξ), sq_abs (inner ℝ u ξ)]
  nlinarith [hT2, ha]

theorem horoballDisjointOfSum (n : ℕ) (hI : HypIsometryProp n) (ξ η : E n)
    (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hξη : ξ ≠ η) (s t : ℝ)
    (h : s + t ≤ Real.log ((1 - inner ℝ ξ η) / 2)) :
    Disjoint (horoball ξ s) (horoball η t) := by
  have hξn : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have hηn : ‖η‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hη
  rw [Set.disjoint_left]
  intro u hu1 hu2
  simp only [horoball, Set.mem_ofPred_eq, busemann, tpart] at hu1 hu2
  -- Cauchy–Schwarz gives `-1 ≤ ⟪ξ,η⟫ ≤ 1`.
  have hcabs : |inner ℝ ξ η| ≤ 1 := by
    have hh := norm_inner_le_norm (𝕜 := ℝ) ξ η
    rw [hξn, hηn, mul_one, Real.norm_eq_abs] at hh
    exact hh
  obtain ⟨hcge, hcle⟩ := abs_le.mp hcabs
  -- The sharp bound on the product of the two levels.
  have hcore : (1 - inner ℝ ξ η)/2 ≤
      (Real.sqrt (1 + ‖u‖^2) - inner ℝ u ξ) * (Real.sqrt (1 + ‖u‖^2) - inner ℝ u η) := by
    rcases lt_or_eq_of_le hcge with hlt | heq
    · exact core_lt ξ η u hξn hηn hlt
    · exact core_anti ξ η u hξn hηn heq.symm
  have hT2 : (Real.sqrt (1 + ‖u‖^2))^2 = 1 + ‖u‖^2 := Real.sq_sqrt (by positivity)
  have hTpos : 0 < Real.sqrt (1 + ‖u‖^2) := Real.sqrt_pos.mpr (by positivity)
  -- Positivity of the two levels `√(1+‖u‖²) - ⟪u,ξ⟫` and `√(1+‖u‖²) - ⟪u,η⟫`.
  have hab : |inner ℝ u ξ| ≤ ‖u‖ := by
    have hh := norm_inner_le_norm (𝕜 := ℝ) u ξ
    rw [hξn, mul_one, Real.norm_eq_abs] at hh
    exact hh
  have hTa : 0 < Real.sqrt (1 + ‖u‖^2) - inner ℝ u ξ := by
    have hlt : (inner ℝ u ξ)^2 < (Real.sqrt (1 + ‖u‖^2))^2 := by
      have h2 : (inner ℝ u ξ)^2 ≤ ‖u‖^2 :=
        sq_le_sq.mpr (by rw [abs_of_nonneg (norm_nonneg u)]; exact hab)
      rw [hT2]; linarith
    have h2 : |inner ℝ u ξ| < |Real.sqrt (1 + ‖u‖^2)| := sq_lt_sq.mp hlt
    rw [abs_of_pos hTpos] at h2
    have := le_abs_self (inner ℝ u ξ)
    linarith
  have hbb : |inner ℝ u η| ≤ ‖u‖ := by
    have hh := norm_inner_le_norm (𝕜 := ℝ) u η
    rw [hηn, mul_one, Real.norm_eq_abs] at hh
    exact hh
  have hTb : 0 < Real.sqrt (1 + ‖u‖^2) - inner ℝ u η := by
    have hlt : (inner ℝ u η)^2 < (Real.sqrt (1 + ‖u‖^2))^2 := by
      have h2 : (inner ℝ u η)^2 ≤ ‖u‖^2 :=
        sq_le_sq.mpr (by rw [abs_of_nonneg (norm_nonneg u)]; exact hbb)
      rw [hT2]; linarith
    have h2 : |inner ℝ u η| < |Real.sqrt (1 + ‖u‖^2)| := sq_lt_sq.mp hlt
    rw [abs_of_pos hTpos] at h2
    have := le_abs_self (inner ℝ u η)
    linarith
  -- `⟪ξ,η⟫ < 1` because `ξ ≠ η` are unit vectors.
  have hclt1 : inner ℝ ξ η < 1 := by
    rcases lt_or_eq_of_le hcle with hh | hh
    · exact hh
    · exfalso
      have hz : ‖ξ - η‖^2 = 0 := by rw [norm_sub_sq_real, hξn, hηn, hh]; ring
      have hnn : ‖ξ - η‖ = 0 := by nlinarith [hz, norm_nonneg (ξ - η)]
      have hz' : ξ - η = 0 := by simpa using (norm_eq_zero.mp hnn)
      exact hξη (sub_eq_zero.mp hz')
  have hpos2 : 0 < (1 - inner ℝ ξ η)/2 := by linarith
  have hprodpos :
      0 < (Real.sqrt (1+‖u‖^2) - inner ℝ u ξ)*(Real.sqrt (1+‖u‖^2) - inner ℝ u η) :=
    lt_of_lt_of_le hpos2 hcore
  -- Compare the logarithms of the two levels with `s` and `t`.
  have hlog : Real.log ((Real.sqrt (1+‖u‖^2) - inner ℝ u ξ)*(Real.sqrt (1+‖u‖^2) - inner ℝ u η))
      = Real.log (Real.sqrt (1+‖u‖^2) - inner ℝ u ξ)
        + Real.log (Real.sqrt (1+‖u‖^2) - inner ℝ u η) :=
    Real.log_mul (ne_of_gt hTa) (ne_of_gt hTb)
  have hstrict : Real.log ((Real.sqrt (1+‖u‖^2) - inner ℝ u ξ)*(Real.sqrt (1+‖u‖^2) - inner ℝ u η))
      < Real.log ((1 - inner ℝ ξ η)/2) := by
    rw [hlog]
    exact lt_of_lt_of_le (add_lt_add hu1 hu2) h
  have := (Real.log_lt_log_iff hprodpos hpos2).mp hstrict
  linarith

end Work.Mostow.cuspHoro
