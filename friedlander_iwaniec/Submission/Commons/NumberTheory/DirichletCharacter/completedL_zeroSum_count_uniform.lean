import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_window_cover
import Submission.Commons.NumberTheory.DirichletCharacter.diskZeroCount_two_half

noncomputable section
open Complex DirichletCharacter Metric
open scoped Real Topology BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.DirichletCharacter

/-- On a set where `f` is analytic, the divisor of `f` coincides with the vanishing order of `f`
at every point of the set. -/
private lemma divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hu : u ∈ U) :
    MeromorphicOn.divisor f U u = (analyticOrderNatAt f u : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu, (hf u hu).meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt f u) ⊤ with h | h
  · rw [h]; simp [analyticOrderNatAt, h]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    have h2 : analyticOrderNatAt f u = n := by
      rw [analyticOrderNatAt, ← hn]
      simp
    rw [h2, ← hn]
    simp

/-- The divisor coefficients of an analytic function are nonnegative. -/
private lemma divisor_nonneg_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) :
    (0 : ℤ) ≤ MeromorphicOn.divisor f U z := by
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz]
    have hAn : AnalyticAt ℂ f z := hf z hz
    have hNF := hAn.meromorphicNFAt
    have hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z :=
      (MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hNF).2 hAn
    exact (WithTop.untop₀_nonneg (α := ℤ) (a := meromorphicOrderAt f z)).mpr hord
  · rw [MeromorphicOn.divisor_def]
    rw [if_neg]
    intro h
    exact hz h.2

/-- `log 4 ≤ 2`. -/
private lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]; linarith

/-- **Uniform zero count of the completed Dirichlet L-function in a disk centred at `2`.**

For a primitive non-trivial character `χ mod N` and every `R ≥ 2`, the (signed) divisor sum of
`Λ(χ,·)` in the closed disk of radius `R` about the point `2` is at most
`4·R·(3/2·(log N + log(R+2) + 4) + 6)`, with a constant independent of `χ` and `N`.

This is obtained by covering the disk `B(2,R)` with the `⌈2R+2⌉+1 ≤ 4R` unit windows of radius
`5/2` (`completedL_window_cover`) and applying the *explicit, χ-free* small-disk bound
`diskZeroCount_two_half` to each of them. -/
private theorem completedL_disk_uniform {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {R : ℝ} (hR : 2 ≤ R) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (2 : ℂ) R)) u : ℤ) : ℝ)) ≤
      4 * R * (3 / 2 * (Real.log (N : ℝ) + Real.log (R + 2) + 4) + 6) := by
  classical
  set nR : ℕ := Nat.ceil (2 * R + 2) + 1 with hnR
  set E : ℝ := 3 / 2 * (Real.log (N : ℝ) + Real.log (R + 2) + 4) + 6 with hE
  have hA0 : 0 ≤ Real.log (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
    exact Real.log_nonneg hN1
  have hB0 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := by rw [hE]; nlinarith
  -- the covering inequality
  have hcenter : Metric.closedBall ((2 : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) R =
      Metric.closedBall (2 : ℂ) R := by
    rw [show ((2 : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) = 2 by simp]
  have hcover := completedL_window_cover χ hχ hχprim (R := R) (t := 0) hR
  -- per-window bound
  have hterm : ∀ j ∈ Finset.range nR,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (((0 : ℝ) - (R + 1) + (j : ℝ)) : ℂ))
          2.5)) u : ℤ) : ℝ)) ≤ E := by
    intro j hj
    have hjlt : (j : ℝ) < 2 * R + 3 := by
      have h1 : j < Nat.ceil (2 * R + 2) + 1 := by
        rw [← hnR]; exact Finset.mem_range.mp hj
      have h2 : (j : ℝ) ≤ (Nat.ceil (2 * R + 2) : ℝ) := by
        exact_mod_cast (Nat.lt_succ_iff.mp h1)
      have h3 : (Nat.ceil (2 * R + 2) : ℝ) < 2 * R + 3 := by
        have := Nat.ceil_lt_add_one (a := 2 * R + 2) (by positivity : (0 : ℝ) ≤ 2 * R + 2)
        linarith
      linarith
    have hbase := diskZeroCount_two_half χ hχ hχprim ((0 : ℝ) - (R + 1) + (j : ℝ))
    have hconv : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (((0 : ℝ) - (R + 1) + (j : ℝ)) : ℂ))
          2.5)) u : ℤ) : ℝ))
        = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) +
          Complex.I * Complex.ofReal ((0 : ℝ) - (R + 1) + (j : ℝ))) (5 / 2))) u : ℤ) : ℝ)) := by
      apply finsum_congr
      intro u
      have hc : ((2 : ℂ) + Complex.I * (((0 : ℝ) - (R + 1) + (j : ℝ)) : ℂ))
          = ((2 : ℂ) + Complex.I * Complex.ofReal ((0 : ℝ) - (R + 1) + (j : ℝ))) := by
        simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_zero,
          Complex.ofReal_natCast]
      have hr : (2.5 : ℝ) = 5 / 2 := by norm_num
      rw [hc, hr]
    rw [hconv]
    refine le_trans hbase ?_
    have hlog : Real.log (2 + |(0 : ℝ) - (R + 1) + (j : ℝ)| + 2) ≤ Real.log (R + 2) + 2 := by
      have harg : (0 : ℝ) < 2 + |(0 : ℝ) - (R + 1) + (j : ℝ)| + 2 := by positivity
      have hle : 2 + |(0 : ℝ) - (R + 1) + (j : ℝ)| + 2 ≤ 4 * (R + 2) := by
        have h1 : |(0 : ℝ) - (R + 1) + (j : ℝ)| ≤ 3 * R + 4 := by
          have h2 : |(0 : ℝ) - (R + 1) + (j : ℝ)| ≤ |(0 : ℝ) - (R + 1)| + |(j : ℝ)| :=
            abs_add_le _ _
          have h3 : |(0 : ℝ) - (R + 1)| = R + 1 := by
            rw [zero_sub, abs_neg, abs_of_nonneg (by linarith)]
          have h4 : |((j : ℕ) : ℝ)| = (j : ℝ) := abs_of_nonneg (by positivity)
          rw [h3, h4] at h2
          linarith
        linarith
      calc Real.log (2 + |(0 : ℝ) - (R + 1) + (j : ℝ)| + 2)
          ≤ Real.log (4 * (R + 2)) := Real.log_le_log harg hle
        _ = Real.log 4 + Real.log (R + 2) :=
            Real.log_mul (by norm_num) (by linarith)
        _ ≤ Real.log (R + 2) + 2 := by linarith [log_four_le_two]
    rw [hE]
    have h1 : Real.log (N : ℝ) +
        Real.log (2 + |(0 : ℝ) - (R + 1) + (j : ℝ)| + 2) + 2
        ≤ Real.log (N : ℝ) + Real.log (R + 2) + 4 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    linarith
  have hcard : ((Finset.range nR).card : ℝ) ≤ 4 * R := by
    rw [Finset.card_range, hnR]
    have h3 : (Nat.ceil (2 * R + 2) : ℝ) < 2 * R + 3 := by
      have := Nat.ceil_lt_add_one (a := 2 * R + 2) (by positivity : (0 : ℝ) ≤ 2 * R + 2)
      linarith
    have h2 : ((Nat.ceil (2 * R + 2) + 1 : ℕ) : ℝ) = (Nat.ceil (2 * R + 2) : ℝ) + 1 := by
      push_cast; ring
    rw [h2]; linarith
  calc (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (2 : ℂ) R)) u : ℤ) : ℝ))
      = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) R)) u : ℤ) : ℝ)) := by
          rw [hcenter]
    _ ≤ ∑ j ∈ Finset.range nR, (∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall ((2 : ℂ) + Complex.I * (((0 : ℝ) - (R + 1) + (j : ℝ)) : ℂ))
              2.5)) u : ℤ) : ℝ)) := by
          simpa [nR] using hcover
    _ ≤ ∑ j ∈ Finset.range nR, E := Finset.sum_le_sum hterm
    _ = ((Finset.range nR).card : ℝ) * E := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (4 * R) * E := mul_le_mul_of_nonneg_right hcard hE0
    _ = 4 * R * (3 / 2 * (Real.log (N : ℝ) + Real.log (R + 2) + 4) + 6) := by rw [hE]

theorem completedL_zeroSum_count_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Complex.reProdIm (Set.Ioo 0 1) (Set.Icc (-T) T))) u : ℤ) : ℝ))
        ≤ c * (T + 2) * (Real.log ((N : ℝ) * (T + 2)) + 2) := by
  refine ⟨40, by norm_num, ?_⟩
  intro N _ χ hχ hχprim T hT
  set R : ℝ := T + 2 with hRdef
  have hR : 2 ≤ R := by rw [hRdef]; linarith
  have hRpos : 0 < R := by linarith
  -- the strip sum is bounded by the disk sum
  have hstrip_le_disk :
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Complex.reProdIm (Set.Ioo 0 1) (Set.Icc (-T) T))) u : ℤ) : ℝ)) ≤
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (2 : ℂ) R)) u : ℤ) : ℝ)) := by
    set Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hΛdef
    set reg : Set ℂ := Complex.reProdIm (Set.Ioo (0 : ℝ) 1) (Set.Icc (-T) T) with hregdef
    set B : Set ℂ := Metric.closedBall (2 : ℂ) R with hBdef
    have hΛan (U : Set ℂ) : AnalyticOnNhd ℂ Λ U := fun z _ =>
      (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
    have hdivEq : ∀ u : ℂ, u ∈ reg →
        MeromorphicOn.divisor Λ reg u = MeromorphicOn.divisor Λ B u := by
      intro u hu
      rw [hregdef] at hu
      obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hu
      have huB : u ∈ B := by
        rw [hBdef, Metric.mem_closedBall, dist_eq_norm]
        calc ‖u - 2‖ ≤ |(u - 2).re| + |(u - 2).im| := Complex.norm_le_abs_re_add_abs_im _
          _ = |u.re - 2| + |u.im| := by simp
          _ ≤ 2 + T := by
              have h1 : |u.re - 2| ≤ 2 := by
                rw [abs_le]; constructor <;> linarith [hre.1, hre.2]
              have h2 : |u.im| ≤ T := abs_le.mpr him
              linarith
          _ ≤ R := by rw [hRdef]; linarith
      rw [divisor_eq_analyticOrderNatAt (hΛan reg) hu,
        divisor_eq_analyticOrderNatAt (hΛan B) huB]
    have hpoint : ∀ u : ℂ,
        ((MeromorphicOn.divisor Λ reg u : ℤ) : ℝ) ≤ ((MeromorphicOn.divisor Λ B u : ℤ) : ℝ) := by
      intro u
      by_cases hu : u ∈ reg
      · rw [hdivEq u hu]
      · have h0 : MeromorphicOn.divisor Λ reg u = 0 :=
          (MeromorphicOn.divisor Λ reg).apply_eq_zero_of_notMem hu
        rw [h0, Int.cast_zero]
        exact_mod_cast divisor_nonneg_of_analyticOnNhd (hΛan B)
    have hfinB : Function.HasFiniteSupport (fun u : ℂ =>
        ((MeromorphicOn.divisor Λ B u : ℤ) : ℝ)) := by
      have h1 : Function.HasFiniteSupport (fun u : ℂ => (MeromorphicOn.divisor Λ B u : ℤ)) := by
        simpa [Function.HasFiniteSupport] using
          ((MeromorphicOn.divisor Λ B).finiteSupport (by
            rw [hBdef]; exact isCompact_closedBall (2 : ℂ) R))
      exact h1.subset (by
        intro u hu
        rw [Function.mem_support] at hu ⊢
        intro h
        exact hu (by exact_mod_cast h))
    have hfinL : Function.HasFiniteSupport (fun u : ℂ =>
        ((MeromorphicOn.divisor Λ reg u : ℤ) : ℝ)) :=
      hfinB.subset (by
        intro u hu
        rw [Function.mem_support] at hu ⊢
        intro hB
        apply hu
        by_cases hureg : u ∈ reg
        · rw [hdivEq u hureg]; exact hB
        · rw [(MeromorphicOn.divisor Λ reg).apply_eq_zero_of_notMem hureg]; norm_num)
    exact finsum_le_finsum' hfinL hfinB hpoint
  have hdisk := completedL_disk_uniform χ hχ hχprim hR
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hA0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hC0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hB_le : Real.log (R + 2) ≤ Real.log R + 1 := by
    have h1 : Real.log (R + 2) ≤ Real.log (2 * R) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (2 * R) = Real.log 2 + Real.log R :=
      Real.log_mul (by norm_num) (ne_of_gt hRpos)
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith [h1, h2, h3]
  have hNR : Real.log ((N : ℝ) * R) = Real.log (N : ℝ) + Real.log R :=
    Real.log_mul (by positivity) (ne_of_gt hRpos)
  have hfin : 4 * R * (3 / 2 * (Real.log (N : ℝ) + Real.log (R + 2) + 4) + 6) ≤
      40 * R * (Real.log ((N : ℝ) * R) + 2) := by
    rw [hNR]
    nlinarith [hA0, hC0, hB_le, hR, hRpos]
  calc (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Complex.reProdIm (Set.Ioo 0 1) (Set.Icc (-T) T))) u : ℤ) : ℝ))
      ≤ (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (2 : ℂ) R)) u : ℤ) : ℝ)) := hstrip_le_disk
    _ ≤ 4 * R * (3 / 2 * (Real.log (N : ℝ) + Real.log (R + 2) + 4) + 6) := hdisk
    _ ≤ 40 * R * (Real.log ((N : ℝ) * R) + 2) := hfin

end Commons.NumberTheory.DirichletCharacter
