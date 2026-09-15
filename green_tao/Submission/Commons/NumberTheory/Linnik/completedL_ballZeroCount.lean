import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.Linnik.completedL_local_zeroCount

open Complex DirichletCharacter Metric
open scoped Real

noncomputable section

namespace Commons.NumberTheory.Linnik

/-!
# `completedL_ballZeroCount` — zeros of the completed Dirichlet L-function in an
arbitrary disk

The count (with multiplicity) of zeros of `Λ(s, χ) := completedLFunction χ s` inside
`closedBall a ρ` (`ρ ≥ 1`) is bounded by `c·(ρ+1)·(log(‖a‖+ρ+2) + log N + 2)`.

**Reduction.**  By `zerosInStrip`, every zero of `Λ` has `0 < Re < 1`, so any zero in
`closedBall a ρ` lies inside the (larger) disk centred at `2 + I·(Im a)` of radius
`ρ + 2` (its real part is within `2` of the centre, its imaginary part within `ρ`).
Divisor sums are monotone under this enlargement, and the *local* count
`completedL_local_zeroCount` (disks centred on the line `Re = 2`, radius `R ≥ 2`)
provides the bound `c₀·(ρ+2)·(log(4 + |Im a| + ρ) + log N + 2)`, which absorbs into
the required right hand side.
-/

/-- Divisor coefficients of an analytic function are nonnegative. -/
lemma divisor_nonneg_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U) :
    (0 : ℤ) ≤ MeromorphicOn.divisor f U z := by
  rw [MeromorphicOn.divisor_def]
  by_cases h : MeromorphicOn f U ∧ z ∈ U
  · rw [if_pos h]
    have hAn : AnalyticAt ℂ f z := hf z h.2
    have hNF := hAn.meromorphicNFAt
    have hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z :=
      (MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hNF).2 hAn
    exact (WithTop.untop₀_nonneg (α := ℤ) (a := meromorphicOrderAt f z)).mpr hord
  · rw [if_neg h]

/-- Cast to the reals, divisor coefficients of an analytic function are nonnegative. -/
lemma divisor_real_nonneg_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor f U z : ℤ) : ℝ) := by
  exact_mod_cast divisor_nonneg_of_analyticOnNhd hf hz

/-- The completed L-function of a non-trivial character is analytic everywhere. -/
lemma completedLFunction_analyticOnNhd {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (U : Set ℂ) :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) U := by
  intro z hz
  exact (differentiable_completedLFunction hχ).analyticAt z

/-- An analytic function with a nonzero value has zero divisor coefficient. -/
lemma divisor_zero_of_analytic_ne_zero {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hAnU : AnalyticOnNhd ℂ f U) (hz : z ∈ U) (hfz : f z ≠ 0) :
    MeromorphicOn.divisor f U z = 0 := by
  rw [MeromorphicOn.divisor_apply hAnU.meromorphicOn hz]
  have hAn : AnalyticAt ℂ f z := hAnU z hz
  have hord : meromorphicOrderAt f z = 0 := by
    rw [hAn.meromorphicOrderAt_eq]
    have h0 : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hfz)
    simp [h0]
  simp [hord]

/-- zeros-in-strip for a zero of the completed L-function. -/
lemma completedL_zero_strip_ball {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {u : ℂ}
    (hu : DirichletCharacter.completedLFunction χ u = 0) :
    0 < u.re ∧ u.re < 1 :=
  Commons.NumberTheory.DirichletCharacter.zerosInStrip χ hχ hχprim u hu

/-- Containment: a zero of `Λ` inside `closedBall a ρ` lies inside
`closedBall (2 + I·Im a) (ρ + 2)`. -/
lemma zero_in_ball_left_le_zero_in_ball_right {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {a : ℂ} {ρ : ℝ} {u : ℂ} (huB : u ∈ Metric.closedBall a ρ)
    (hu0 : DirichletCharacter.completedLFunction χ u = 0) :
    u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (ρ + 2) := by
  have hstrip := completedL_zero_strip_ball χ hχ hχprim hu0
  have hre : |u.re - 2| ≤ 2 := by
    have h1 : u.re - 2 < 0 := by linarith [hstrip.2]
    have h2 : -2 ≤ u.re - 2 := by linarith [hstrip.1]
    rw [abs_of_neg h1]
    linarith
  have hdist : ‖u - a‖ ≤ ρ := by simpa [dist_eq_norm] using huB
  have him2 : |u.im - a.im| ≤ ρ := by
    have h := Complex.abs_im_le_norm (u - a)
    simpa using (le_trans h hdist)
  rw [Metric.mem_closedBall, dist_eq_norm]
  have htri := Complex.norm_le_abs_re_add_abs_im (u - ((2 : ℂ) + Complex.I * (a.im : ℂ)))
  have hre' : (u - ((2 : ℂ) + Complex.I * (a.im : ℂ))).re = u.re - 2 := by simp
  have him' : (u - ((2 : ℂ) + Complex.I * (a.im : ℂ))).im = u.im - a.im := by simp
  calc
    ‖u - ((2 : ℂ) + Complex.I * (a.im : ℂ))‖
        ≤ |(u - ((2 : ℂ) + Complex.I * (a.im : ℂ))).re|
            + |(u - ((2 : ℂ) + Complex.I * (a.im : ℂ))).im| := htri
    _ = |u.re - 2| + |u.im - a.im| := by rw [hre', him']
    _ ≤ 2 + ρ := add_le_add hre him2
    _ = ρ + 2 := by ring

/-- Pointwise comparison of the small-ball divisor and the large-ball divisor. -/
lemma small_divisor_le_big_divisor {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    (a : ℂ) (ρ : ℝ) (u : ℂ) :
    (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ) ≤
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (ρ + 2))) u : ℤ) : ℝ) := by
  let c0 : ℂ := (2 : ℂ) + Complex.I * (a.im : ℂ)
  have hfA : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall a ρ) := completedLFunction_analyticOnNhd χ hχ _
  have hfB : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall c0 (ρ + 2)) := completedLFunction_analyticOnNhd χ hχ _
  by_cases huB : u ∈ Metric.closedBall c0 (ρ + 2)
  · by_cases huA : u ∈ Metric.closedBall a ρ
    · -- u in both balls: the divisor coefficients agree
      rw [MeromorphicOn.divisor_apply hfA.meromorphicOn huA,
        MeromorphicOn.divisor_apply hfB.meromorphicOn huB]
    · -- u in B ∖ A : the small coefficient is 0, the big one nonnegative
      have hzeroA : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ) u = 0 := by
        rw [MeromorphicOn.divisor_def]
        rw [if_neg]
        intro h
        exact huA h.2
      rw [hzeroA]
      simpa [c0] using (divisor_real_nonneg_of_analyticOnNhd hfB huB)
  · -- u ∉ B : both coefficients vanish
    have hzeroB : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall c0 (ρ + 2)) u = 0 := by
      rw [MeromorphicOn.divisor_def]
      rw [if_neg]
      intro h
      exact huB h.2
    have hzeroA : MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall a ρ) u = 0 := by
      by_cases huA : u ∈ Metric.closedBall a ρ
      · by_contra hne
        -- a non-zero coefficient at an analytic point forces a zero of Λ
        have hfzero : DirichletCharacter.completedLFunction χ u = 0 := by
          by_contra hfz
          exact hne (divisor_zero_of_analytic_ne_zero hfA huA hfz)
        have hc := zero_in_ball_left_le_zero_in_ball_right χ hχ hχprim huA hfzero
        exact huB (by simpa [c0] using hc)
      · rw [MeromorphicOn.divisor_def]
        rw [if_neg]
        intro h
        exact huA h.2
    rw [hzeroA, hzeroB]

/-- Finite support of the integer-valued divisor functions. -/
lemma divisor_finiteSupport {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (a : ℂ) (ρ : ℝ) :
    Function.HasFiniteSupport
      (fun u : ℂ => ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ)) := by
  simpa [Function.HasFiniteSupport] using
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall a ρ)).finiteSupport (isCompact_closedBall a ρ))

/-- Finite support of the real-valued divisor functions. -/
lemma divisor_real_finiteSupport {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (a : ℂ) (ρ : ℝ) :
    Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ)) := by
  have hfinZ : (Function.support
      (fun u : ℂ => ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ))).Finite := by
    simpa [Function.HasFiniteSupport] using (divisor_finiteSupport χ hχ a ρ)
  have hsub : Function.support
      (fun u : ℂ => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ⊆
      Function.support
      (fun u : ℂ => ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ)) := by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    exact fun hz => hu (by exact_mod_cast hz)
  exact hfinZ.subset hsub

/-- Monotonicity of the divisor sum under the enlargement of the ball. -/
lemma divisor_sum_le_divisor_sum_big {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    (a : ℂ) (ρ : ℝ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (ρ + 2))) u : ℤ) : ℝ)) := by
  have hf : Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ)) :=
    divisor_real_finiteSupport χ hχ a ρ
  have hg : Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (ρ + 2))) u : ℤ) : ℝ)) :=
    divisor_real_finiteSupport χ hχ ((2 : ℂ) + Complex.I * (a.im : ℂ)) (ρ + 2)
  exact finsum_le_finsum' hf hg (fun u => small_divisor_le_big_divisor χ hχ hχprim a ρ u)

/-- `log N ≥ 0` for `N : ℕ`, `NeZero N`. -/
lemma log_N_nonneg {N : ℕ} [NeZero N] : (0 : ℝ) ≤ Real.log (N : ℝ) := by
  exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))))

/-- **Zero count of the completed Dirichlet L-function in an arbitrary disk.** -/
theorem completedL_ballZeroCount {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, ∀ a : ℂ, ∀ ρ : ℝ, 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤
        c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  rcases completedL_local_zeroCount χ hχ hχprim with ⟨c0, hc0⟩
  let c : ℝ := 4 * max c0 0 + 4
  refine ⟨c, ?_⟩
  intro a ρ hρ
  have hnorm : 0 ≤ ‖a‖ := norm_nonneg a
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ1 : 1 ≤ ρ := hρ
  have hX : 2 ≤ ‖a‖ + ρ + 2 := by nlinarith
  have hXpos : 0 < ‖a‖ + ρ + 2 := by nlinarith
  have hlogN0 : (0 : ℝ) ≤ Real.log (N : ℝ) := log_N_nonneg
  have hXge : 1 ≤ ‖a‖ + ρ + 2 := by nlinarith
  have hXlog : 0 ≤ Real.log (‖a‖ + ρ + 2) := by
    exact Real.log_nonneg hXge
  -- step 1 + 2: enlarge the disk to centre `2 + I·Im a`, radius `ρ + 2`, then use
  -- the local count bound
  have h2 := hc0 (ρ + 2) (by linarith : 2 ≤ ρ + 2) a.im
  have h2log : (2 + |a.im| + (ρ + 2)) = (4 + |a.im| + ρ) := by ring
  have h2' : (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor Λ (Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ))
            (ρ + 2))) u : ℤ) : ℝ)) ≤
      c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by
    simpa [Λ, h2log] using h2
  have h12 : (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor Λ (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤
      c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by
    calc
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall a ρ)) u : ℤ) : ℝ))
          = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall a ρ)) u : ℤ) : ℝ) := by simp [Λ]
      _ ≤ ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall ((2 : ℂ) + Complex.I * (a.im : ℂ)) (ρ + 2))) u : ℤ) : ℝ) :=
              divisor_sum_le_divisor_sum_big χ hχ hχprim a ρ
      _ ≤ c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by
              simpa [Λ] using h2'
  -- log absorption: log(4 + |a.im| + ρ) ≤ 2·log(‖a‖+ρ+2)
  have hIm : |a.im| ≤ ‖a‖ := Complex.abs_im_le_norm a
  have hposLog : 0 < 4 + |a.im| + ρ := by nlinarith [abs_nonneg a.im]
  have hleSq : 4 + ‖a‖ + ρ ≤ (‖a‖ + ρ + 2) ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ + ρ), hnorm]
  have hlog1 : Real.log (4 + |a.im| + ρ) ≤ 2 * Real.log (‖a‖ + ρ + 2) := by
    have hmono : Real.log (4 + |a.im| + ρ) ≤ Real.log (4 + ‖a‖ + ρ) := by
      exact Real.log_le_log hposLog (by nlinarith)
    have hpos2 : 0 < 4 + ‖a‖ + ρ := by nlinarith
    have hlog2 : Real.log (4 + ‖a‖ + ρ) ≤ Real.log ((‖a‖ + ρ + 2) ^ 2) :=
      Real.log_le_log hpos2 hleSq
    have hsq : Real.log ((‖a‖ + ρ + 2) ^ 2) = 2 * Real.log (‖a‖ + ρ + 2) := by
      rw [Real.log_pow]
      ring
    calc
      Real.log (4 + |a.im| + ρ) ≤ Real.log (4 + ‖a‖ + ρ) := hmono
      _ ≤ Real.log ((‖a‖ + ρ + 2) ^ 2) := hlog2
      _ = 2 * Real.log (‖a‖ + ρ + 2) := hsq
  have hsmall : 2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 ≤
      2 * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    nlinarith [hlogN0, hXlog]
  have hposT : 0 ≤ Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 := by linarith
  have hposC : 0 ≤ max c0 0 := le_max_right c0 0
  have hRhoFact : (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) ≤
      4 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    have hρ2 : ρ + 2 ≤ 2 * (ρ + 1) := by nlinarith
    have hleft : 0 ≤ 2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 := by linarith
    calc
      (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)
          ≤ (2 * (ρ + 1)) * (2 * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) := by
              exact mul_le_mul hρ2 hsmall hleft (by linarith)
      _ = 4 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by ring
  have hposArg : 0 ≤ Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2 := by
    have h1pos : 0 ≤ Real.log (4 + |a.im| + ρ) := by
      refine Real.log_nonneg ?_
      have h_abs : 0 ≤ |a.im| := abs_nonneg a.im
      linarith
    linarith
  have hstepA : c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) ≤
      (max c0 0) * (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    have hle0 : c0 ≤ max c0 0 := le_max_left c0 0
    have hprod1 : c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) ≤
        (max c0 0) * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by
      have hfact : 0 ≤ (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by positivity
      calc
        c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2)
            = c0 * ((ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2)) := by ring
        _ ≤ (max c0 0) * ((ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2)) := by
            exact mul_le_mul_of_nonneg_right hle0 hfact
        _ = (max c0 0) * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := by ring
    have hArg : Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2 ≤
        2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2 := by linarith [hlog1]
    have hpos2 : 0 ≤ (max c0 0) * (ρ + 2) := by positivity
    exact le_trans hprod1 (mul_le_mul_of_nonneg_left hArg hpos2)
  have hstepB : (max c0 0) * (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) ≤
      (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    calc
      (max c0 0) * (ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)
          = (max c0 0) * ((ρ + 2) * (2 * Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) := by ring
      _ ≤ (max c0 0) * (4 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) := by
          exact mul_le_mul_of_nonneg_left hRhoFact hposC
      _ = (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by ring
  have hfinal : (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) ≤
      (4 * max c0 0 + 4) * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    have hleC : 4 * max c0 0 ≤ 4 * max c0 0 + 4 := by linarith
    have hposR : 0 ≤ (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by positivity
    calc
      (max c0 0) * (4 * (ρ + 1)) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)
          = (4 * max c0 0) * ((ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) := by ring
      _ ≤ (4 * max c0 0 + 4) * ((ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2)) := by
          exact mul_le_mul_of_nonneg_right hleC hposR
      _ = (4 * max c0 0 + 4) * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by ring
  have hchain : c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) ≤
      (4 * max c0 0 + 4) * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    exact le_trans (le_trans hstepA hstepB) hfinal
  have hgoal : (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor Λ (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ≤
      c * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := by
    dsimp [c]
    calc
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall a ρ)) u : ℤ) : ℝ))
          ≤ c0 * (ρ + 2) * (Real.log (4 + |a.im| + ρ) + Real.log (N : ℝ) + 2) := h12
      _ ≤ (4 * max c0 0 + 4) * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N : ℝ) + 2) := hchain
  exact hgoal

end Commons.NumberTheory.Linnik
