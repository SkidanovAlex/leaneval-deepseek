/-
# `Submission.Work.FIArea6Hecke.R.heckeZFRrealAxisClean`

**Lemma 16.1 of *FI* (Landau–Siegel), as the proposition `ZFRrealAxis ε`**: this is the fleet's file
`R/heckeZFRrealAxis` with

* all its top-level auxiliary declarations renamed with the prefix `zc_` (so that this module can
  coexist with the original in one import closure), and
* its single remaining placeholder `hdb0` — the sharp derivative bound (16.19) on `1/2 ≤ re s ≤ 1`
  for a *real* strict character — discharged by the proved `Work.FIArea6Hecke.R.LvalDerivBoundClean`,
  whose statement is literally identical to the placeholder.  (The placeholder could not be
  discharged by `Lval_deriv_bound_sharp`, which rests on the refuted `completion_FE_strict`; the
  clean file rebuilds the bound from the three value bounds by Cauchy's estimate.)

This gives an independent, `sorry`-free route to `ZFRrealAxis ε` for the target
`R/logDerivReLower`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing
import Submission.Work.FIArea6Hecke.R.rootOfUnityRatIsFourth
import Submission.Work.FIArea6Hecke.R.m_eq_zero_of_psiReal
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_eq_sum_chi4
import Submission.Commons.NumberTheory.DirichletCharacter.estermann_positivity
import Submission.Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
import Submission.Work.FIArea6Hecke.R.heckeLSeries_one_eq_zeta_mul_chi4
import Submission.Work.FIArea6Hecke.R.real_zeros_bounded_above
import Submission.Work.FIArea6Hecke.R.same_real_zeros_of_agree_on_primary_units
import Submission.Work.FIArea6Hecke.R.Lval_one_norm_le_of_real_zero_segment
import Submission.Work.FIArea6Hecke.R.heckeLval_strip_bound_uniform_clean
import Submission.Work.FIArea6Hecke.R.Lval_ball_bound_uniform
import Submission.Work.FIArea6Hecke.R.exists_completion_strict
import Submission.Work.FIArea6Hecke.R.estermann_defs
import Submission.Work.FIArea6Hecke.R.estermannBall
import Submission.Work.FIArea6Hecke.R.logRpowAbsorb
import Submission.Work.FIArea6Hecke.R.siegelFinalArith
import Submission.Work.FIArea6Hecke.R.LamOneNeZeroRealV
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.LvalHalfPlaneClean
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.LvalDerivBoundClean


set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## 0. Elementary algebra of the predicates -/

/-- **A unit modulo `4d₁` and a unit modulo `4d₂` are a unit modulo `4d₁d₂`**: if `z·a ≡ 1` mod
`4d₁` and `z·c ≡ 1` mod `4d₂`, then `z·(a + c - z·a·c) - 1 = -(z·a - 1)(z·c - 1)` is divisible by
`4d₁d₂`. -/
lemma zc_isUnitMod4d_mul_moduli {d₁ d₂ : ℕ} {z : GaussianInt}
    (h₁ : Work.FIArea5.S16Hecke.IsUnitMod4d d₁ z)
    (h₂ : Work.FIArea5.S16Hecke.IsUnitMod4d d₂ z) :
    Work.FIArea5.S16Hecke.IsUnitMod4d (d₁ * d₂) z := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨c, hc⟩ := h₂
  refine ⟨a + c - z * a * c, ?_⟩
  have key : z * (a + c - z * a * c) - 1 = -((z * a - 1) * (z * c - 1)) := by ring
  rw [key]
  have hmul : (((4 * (d₁ * d₂) : ℕ) : ℤ) : GaussianInt)
      ∣ (4 * d₁ : ℕ) * (4 * d₂ : ℕ) := by
    refine ⟨(4 : GaussianInt), ?_⟩
    push_cast
    ring
  have hprod : (((4 * d₁ : ℕ) : ℤ) : GaussianInt) * (((4 * d₂ : ℕ) : ℤ) : GaussianInt)
      ∣ (z * a - 1) * (z * c - 1) :=
    mul_dvd_mul ha hc
  exact dvd_neg.mpr (dvd_trans hmul hprod)

/-- **The pointwise product of two strict characters is a strict character.**  A Gaussian integer
is a unit modulo `4d₁d₂` iff it is a unit modulo `4d₁` and modulo `4d₂`, so the product vanishes
exactly off the units modulo `4d₁d₂`. -/
theorem zc_isCharMod4dStrict_mul {d₁ d₂ : ℕ} (_h₁ : 1 ≤ d₁) (_h₂ : 1 ≤ d₂)
    {chi₁ chi₂ : GaussianInt → ℂ}
    (hchi₁ : Work.FIArea5.S16Hecke.IsCharMod4dStrict d₁ chi₁)
    (hchi₂ : Work.FIArea5.S16Hecke.IsCharMod4dStrict d₂ chi₂) :
    Work.FIArea5.S16Hecke.IsCharMod4dStrict (d₁ * d₂) (fun z => chi₁ z * chi₂ z) := by
  obtain ⟨⟨h1₁, hmul₁, hbd₁, hper₁, hv₁⟩, hstr₁⟩ := hchi₁
  obtain ⟨⟨h1₂, hmul₂, hbd₂, hper₂, hv₂⟩, hstr₂⟩ := hchi₂
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show chi₁ 1 * chi₂ 1 = 1
    rw [h1₁, h1₂, one_mul]
  · intro z w
    show chi₁ (z * w) * chi₂ (z * w) = (chi₁ z * chi₂ z) * (chi₁ w * chi₂ w)
    rw [hmul₁, hmul₂]
    ring
  · intro z
    rw [norm_mul]
    exact mul_le_one₀ (hbd₁ z) (norm_nonneg _) (hbd₂ z)
  · intro z w hzw
    have hdvd₁ : (((4 * d₁ : ℕ) : ℤ) : GaussianInt)
        ∣ (((4 * (d₁ * d₂) : ℕ) : ℤ) : GaussianInt) := by
      refine ⟨((d₂ : ℤ) : GaussianInt), ?_⟩
      push_cast
      ring
    have hdvd₂ : (((4 * d₂ : ℕ) : ℤ) : GaussianInt)
        ∣ (((4 * (d₁ * d₂) : ℕ) : ℤ) : GaussianInt) := by
      refine ⟨((d₁ : ℤ) : GaussianInt), ?_⟩
      push_cast
      ring
    show chi₁ z * chi₂ z = chi₁ w * chi₂ w
    rw [hper₁ z w (dvd_trans hdvd₁ hzw), hper₂ z w (dvd_trans hdvd₂ hzw)]
  · intro z hz
    have hdvd₁ : (((4 * d₁ : ℕ) : ℤ) : GaussianInt)
        ∣ (((4 * (d₁ * d₂) : ℕ) : ℤ) : GaussianInt) := by
      refine ⟨((d₂ : ℤ) : GaussianInt), ?_⟩
      push_cast
      ring
    show chi₁ z * chi₂ z = 0
    rw [hv₁ z (dvd_trans hdvd₁ hz), zero_mul]
  · intro z hz
    by_cases hu₁ : Work.FIArea5.S16Hecke.IsUnitMod4d d₁ z
    · by_cases hu₂ : Work.FIArea5.S16Hecke.IsUnitMod4d d₂ z
      · exact absurd (zc_isUnitMod4d_mul_moduli hu₁ hu₂) hz
      · show chi₁ z * chi₂ z = 0
        rw [hstr₂ z hu₂, mul_zero]
    · show chi₁ z * chi₂ z = 0
      rw [hstr₁ z hu₁, zero_mul]

/-! ## 1. Bounds of the fixed auxiliary functions on the ball `|s-2| ≤ 3/2` -/

/-- On the ball `|s-2| ≤ 3/2` one has `‖s‖ ≤ 7/2` and `re s ≥ 1/2`. -/
lemma zc_ball_re_ge {s : ℂ} (hs : s ∈ Metric.closedBall (2 : ℂ) (3 / 2)) :
    (1 / 2 : ℝ) ≤ s.re ∧ ‖s‖ ≤ 7 / 2 := by
  have hnorm : ‖s - 2‖ ≤ 3 / 2 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hs
  have h := Complex.abs_re_le_norm (s - 2)
  have hre : (s - 2).re = s.re - 2 := by simp
  rw [hre] at h
  have habs : |s.re - 2| ≤ 3 / 2 := le_trans h hnorm
  refine ⟨by linarith [(abs_le.mp habs).1], ?_⟩
  have h2 : ‖((2 : ℂ))‖ = 2 := by norm_num
  calc ‖s‖ = ‖(s - 2) + 2‖ := by ring_nf
    _ ≤ ‖s - 2‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
    _ ≤ 3 / 2 + 2 := by rw [h2]; linarith
    _ = 7 / 2 := by norm_num

/-- The Dirichlet `L`-function of `χ₄` is bounded by `56` on the ball `|s-2| ≤ 3/2`, since
`‖L(χ₄,s)‖ ≤ 2·4·‖s‖/re s` for `re s > 0` and there `‖s‖ ≤ 7/2`, `re s ≥ 1/2`. -/
lemma zc_chi4C_ball_bound {s : ℂ} (hs : s ∈ Metric.closedBall (2 : ℂ) (3 / 2)) :
    ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s‖ ≤ 56 := by
  obtain ⟨hsre, hnorm⟩ := zc_ball_re_ge hs
  have hsre0 : 0 < s.re := by linarith
  have h := Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
    Work.FIArea6Hecke.R.chi4C Work.FIArea6Hecke.R.chi4C_ne_one hsre0
  have hb : 2 * (4 : ℝ) * ‖s‖ / s.re ≤ 56 := by
    rw [div_le_iff₀ hsre0]
    nlinarith [hnorm, hsre, hsre0]
  simpa using h.trans hb

/-- `‖1 - 2^{-s}‖ ≤ 2` on the ball `|s-2| ≤ 3/2`. -/
lemma zc_two_cpow_ball_bound {s : ℂ} (hs : s ∈ Metric.closedBall (2 : ℂ) (3 / 2)) :
    ‖1 - (2 : ℂ) ^ (-s)‖ ≤ 2 := by
  obtain ⟨hsre, -⟩ := zc_ball_re_ge hs
  have hbase : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have h2 : ‖((2 : ℝ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hre : (-s).re = -s.re := by simp
    rw [hre]
    calc (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 := Real.rpow_zero 2
  rw [hbase] at h2
  calc ‖1 - (2 : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by rw [norm_one]; linarith
    _ = 2 := by norm_num

/-! ## 2. Agreement from a principal product -/

/-- If two strict characters multiply to the principal strict character on the primary units, then
they agree there: `χ₁ z · χ₂ z = 1` with both values of modulus `≤ 1` forces both to have modulus
`1`, and then `χ₂ z = (χ₁ z)⁻¹ = star (χ₁ z) = χ₁ z` by reality of `χ₁`. -/
lemma zc_eq_of_mul_eq_one_on_primary_units {d₁ d₂ : ℕ} {chi₁ chi₂ : GaussianInt → ℂ}
    (hχ₁ : Work.FIArea5.S16Hecke.IsCharMod4dStrict d₁ chi₁)
    (hχ₂ : Work.FIArea5.S16Hecke.IsCharMod4dStrict d₂ chi₂)
    (hre₁ : ∀ z : GaussianInt, chi₁ z = star (chi₁ z))
    (hprin : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      chi₁ z * chi₂ z = Work.FIArea6Hecke.principalStrict (d₁ * d₂) z) :
    ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → Work.FIArea5.S16Hecke.IsUnitMod4d d₁ z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d₂ z → chi₁ z = chi₂ z := by
  intro z hz hz₁ hz₂
  have hu : Work.FIArea5.S16Hecke.IsUnitMod4d (d₁ * d₂) z := zc_isUnitMod4d_mul_moduli hz₁ hz₂
  have hprod : chi₁ z * chi₂ z = 1 := by
    rw [hprin z hz]
    simp [Work.FIArea6Hecke.principalStrict, hu]
  have hb₁ : ‖chi₁ z‖ ≤ 1 := hχ₁.1.2.2.1 z
  have hb₂ : ‖chi₂ z‖ ≤ 1 := hχ₂.1.2.2.1 z
  have hnorm : ‖chi₁ z‖ * ‖chi₂ z‖ = 1 := by rw [← norm_mul, hprod, norm_one]
  have hn₁ : ‖chi₁ z‖ = 1 := by
    nlinarith [hnorm, hb₁, hb₂, norm_nonneg (chi₁ z), norm_nonneg (chi₂ z)]
  have h2 : chi₂ z = (chi₁ z)⁻¹ := eq_inv_of_mul_eq_one_right hprod
  rw [h2]
  rw [Complex.inv_eq_conj hn₁]
  exact hre₁ z

/-! ## 3. The target -/

theorem heckeZFRrealAxisClean (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        Work.FIArea6Hecke.R.PsiReal chi m →
        ∀ s : ℂ, s.im = 0 →
          1 - c / (d : ℝ) ^ ε < s.re → s.re ≤ 2 →
          Work.FIArea6Hecke.Lval d m Lam s ≠ 0 := by
  -- ## the analytic inputs (the `have`s marked PLACEHOLDER are delegated lemmas)
  obtain ⟨Ccrude, hCcrude1, hcrude⟩ :=
    Work.FIArea6Hecke.R.heckeLval_strip_bound_uniform_clean
  obtain ⟨Cb, hCbpos, hballU⟩ := Work.FIArea6Hecke.R.Lval_ball_bound_uniform
  have hdb0 : ∃ C K k : ℝ, 0 < C ∧ 0 ≤ K ∧ 0 ≤ k ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∀ z : GaussianInt, chi z = star (chi z)) →
        (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
        ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 →
          ‖deriv (fun z : ℂ => Work.FIArea6Hecke.Lval d 0 Lam z) s‖
            ≤ C * ((d : ℝ) * (2 + |s.im|)) ^ (K * (1 - s.re))
                * (Real.log (4 * (d : ℝ) * (2 + |s.im|))) ^ k := by
    exact LvalDerivBoundClean
  obtain ⟨Cd, Kd, kd, hCdpos, hKdnn, hkdnn, hderivbd⟩ := hdb0
  obtain ⟨Clog, klog, hClogpos, hklognn, hlogBd⟩ := Work.FIArea6Hecke.R.LvalHalfPlaneClean
  -- ## the threshold of the case analysis
  set ε₁ : ℝ := min (ε / (4000 * (Kd + 90))) (1 / 20) with hε₁def
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]
    exact lt_min (div_pos hε (by positivity)) (by norm_num)
  have hε₁le20 : ε₁ ≤ 1 / 20 := by rw [hε₁def]; exact min_le_right _ _
  have h4000 : 4000 * (Kd + 90) * ε₁ ≤ ε := by
    have h1 : ε₁ ≤ ε / (4000 * (Kd + 90)) := by rw [hε₁def]; exact min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hε₁leε : ε₁ ≤ ε := by
    have h2 : (1 : ℝ) ≤ 4000 * (Kd + 90) := by nlinarith [hKdnn]
    nlinarith [h4000, hε₁pos, h2]
  have hKdε₁ : 4000 * Kd * ε₁ ≤ ε := by nlinarith [h4000, hε₁pos, hKdnn]
  have h90ε₁ : 4000 * 90 * ε₁ ≤ ε := by nlinarith [h4000, hε₁pos]
  -- ## the main claim, at the threshold
  have hmain : ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∀ z : GaussianInt, chi z = star (chi z)) →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ s : ℂ, s.im = 0 →
          1 - c / (d : ℝ) ^ ε < s.re → s.re ≤ 2 →
          Work.FIArea6Hecke.Lval d 0 Lam s ≠ 0 := by
    by_cases hex : ∃ (d₁ : ℕ) (chi₁ : GaussianInt → ℂ) (Lam₁ : ℂ → ℂ) (β₁ : ℝ),
        1 ≤ d₁ ∧ Work.FIArea5.S16Hecke.IsCharMod4dStrict d₁ chi₁ ∧
        (∀ z : GaussianInt, chi₁ z = star (chi₁ z)) ∧
        AnalyticOn ℂ Lam₁ Set.univ ∧
        (∀ s : ℂ, 1 < s.re →
          Lam₁ s = Work.FITop4.Bridge.heckeArch d₁ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s) ∧
        1 - ε₁ < β₁ ∧ β₁ < 1 ∧
        Work.FIArea6Hecke.Lval d₁ 0 Lam₁ (β₁ : ℂ) = 0
    · -- **Case 2**: an exceptional real zero exists; fix one.
      obtain ⟨d₁, chi₁, Lam₁, β₁, hd₁, hχ₁, hre₁, hAn₁, hagr₁, hβ₁lo, hβ₁hi, hzero₁⟩ := hex
      have hβ₁pos : 0 < β₁ := by linarith [hβ₁lo, hε₁le20]
      have hne₁ : ∃ s : ℂ, 0 < s.re ∧ Lam₁ s ≠ 0 := by
        refine ⟨2, by norm_num, ?_⟩
        rw [hagr₁ 2 (by norm_num)]
        exact mul_ne_zero
          (Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd₁ 0 (by norm_num))
          (Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi₁ 0
            hχ₁.1.1 hχ₁.1.2.1 hχ₁.1.2.2.1 (by norm_num))
      obtain ⟨βs, hβs_lt, hβs_max⟩ := Work.FIArea6Hecke.R.real_zeros_bounded_above hAn₁ hne₁
      have hβ₁leβs : β₁ ≤ βs := by
        refine hβs_max β₁ hβ₁pos hβ₁hi ?_
        have hz := hzero₁
        rw [Work.FIArea6Hecke.Lval] at hz
        exact (div_eq_zero_iff.mp hz).resolve_right
          (Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd₁ 0 hβ₁pos)
      -- ### the constants
      set Cch : ℝ := max Ccrude Work.FIArea5.S16Hecke.heckeLMajorant with hCchdef
      have hCch1 : 1 ≤ Cch := le_trans hCcrude1 (le_max_left _ _)
      have hCchLM : Work.FIArea5.S16Hecke.heckeLMajorant ≤ Cch := le_max_right _ _
      set Cc : ℝ := max 1 (max 56 (max 2 (Cb * Cch))) with hCcdef
      have hCc1 : 1 ≤ Cc := le_max_left _ _
      have hCc56 : 56 ≤ Cc := le_trans (le_max_left _ _) (le_max_right _ _)
      have hCc2 : 2 ≤ Cc :=
        le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
      have hCcCb : Cb * Cch ≤ Cc :=
        le_trans (le_max_right (2 : ℝ) (Cb * Cch))
          (le_trans (le_max_right (56 : ℝ) (max 2 (Cb * Cch)))
            (le_max_right (1 : ℝ) (max 56 (max 2 (Cb * Cch)))))
      -- ### the ball bound for an arbitrary datum
      have hballAt : ∀ (d' : ℕ), 1 ≤ d' → ∀ (chi' : GaussianInt → ℂ),
          Work.FIArea5.S16Hecke.IsCharMod4dStrict d' chi' →
          (∀ z : GaussianInt, chi' z = star (chi' z)) →
          (∀ z : GaussianInt, ‖chi' z‖ ≤ 1) →
          ∀ (Lam' : ℂ → ℂ), AnalyticOn ℂ Lam' Set.univ →
          (∀ s : ℂ, 1 < s.re →
            Lam' s = Work.FITop4.Bridge.heckeArch d' 0 s *
              Work.FIArea5.S16Hecke.heckeLSeries chi' 0 s) →
          ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
            ‖Work.FIArea6Hecke.Lval d' 0 Lam' s‖ ≤ Cc * (d' : ℝ) ^ (10 : ℕ) := by
        intro d' hd' chi' hχ' hre' hb' Lam' hAn' hagr'
        have hstrip : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 →
            ‖Work.FIArea6Hecke.Lval d' 0 Lam' s‖
              ≤ Cch * (d' : ℝ) ^ (10 : ℕ) * (1 + |s.im|) ^ (10 : ℕ) := by
          intro s hs1 hs2
          refine le_trans (hcrude d' hd' chi' hχ' hre' hb' Lam' hAn' hagr' s hs1 hs2) ?_
          have h2 : Ccrude ≤ Cch := le_max_left _ _
          have h3 : (0 : ℝ) ≤ (d' : ℝ) ^ (10 : ℕ) := by positivity
          have h4 : (0 : ℝ) ≤ (1 + |s.im|) ^ (10 : ℕ) := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 h3) h4
        have hline : ∀ s : ℂ, 3 / 2 ≤ s.re →
            ‖Work.FIArea6Hecke.Lval d' 0 Lam' s‖ ≤ Cch := by
          intro s hs
          have hs1 : 1 < s.re := by linarith
          have hs0 : 0 < s.re := by linarith
          have hne : Work.FITop4.Bridge.heckeArch d' 0 s ≠ 0 :=
            Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd' 0 hs0
          have hval : Work.FIArea6Hecke.Lval d' 0 Lam' s
              = Work.FIArea5.S16Hecke.heckeLSeries chi' 0 s := by
            rw [Work.FIArea6Hecke.Lval, hagr' s hs1]
            exact mul_div_cancel_left₀ _ hne
          rw [hval]
          exact le_trans
            (Work.FIArea5.S16Hecke.heckeLSeries_norm_le_re_ge_three_halves chi' 0 hb'
              (by linarith)) hCchLM
        have hbd := (hballU d' hd' chi' hχ' hb' Lam' hAn' hagr' Cch hCch1 hstrip hline).1
        intro s hs
        refine le_trans (hbd s hs) ?_
        exact mul_le_mul_of_nonneg_right hCcCb (by positivity)
      -- ### the Estermann constant (fixed datum `(d₁, χ₁, Lam₁, β₁)`)
      have hζK : ∀ s : ℂ, 1 < s.re →
          Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1 : ℂ)) 0 s
            = riemannZeta s * DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s
                * (1 - (2 : ℂ) ^ (-s)) :=
        fun s hs => by
          rw [Work.FIArea6Hecke.R.heckeLSeries_one_eq_zeta_mul_chi4 hs,
            Work.FIArea6Hecke.R.LSeries_axisChi4_eq_LFunction hs]
      have hβ₁lo' : 19 / 20 ≤ β₁ := by linarith [hβ₁lo, hε₁le20]
      have hLam1zero : Lam₁ ((β₁ : ℝ) : ℂ) = 0 := by
        have hz := hzero₁
        rw [Work.FIArea6Hecke.Lval] at hz
        exact (div_eq_zero_iff.mp hz).resolve_right
          (Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd₁ 0 hβ₁pos)
      have hball₁ := hballAt d₁ hd₁ chi₁ hχ₁ hre₁ hχ₁.1.2.2.1 Lam₁ hAn₁ hagr₁
      have hL4 : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
          ‖DirichletCharacter.LFunction Work.FIArea6Hecke.R.chi4C s‖ ≤ Cc :=
        fun s hs => le_trans (Work.FIArea6Hecke.R.zc_chi4C_ball_bound hs) hCc56
      have h2s : ∀ s : ℂ, s ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
          ‖1 - (2 : ℂ) ^ (-s)‖ ≤ Cc :=
        fun s hs => le_trans (Work.FIArea6Hecke.R.zc_two_cpow_ball_bound hs) hCc2
      obtain ⟨c₃, hc₃pos, hE₃⟩ := Work.FIArea6Hecke.R.estermannBall (d₁ := d₁) hd₁ hχ₁.1.1 hre₁ hχ₁.1.2.1 hχ₁.1.2.2.1 hAn₁ hagr₁ hζK
        hβ₁lo' hβ₁hi hLam1zero hCc1 hball₁ hL4 h2s
      -- ### the log-absorption constant and the final constants
      obtain ⟨A, hA1, hAb⟩ := Work.FIArea6Hecke.R.logRpowAbsorb ε hε klog kd hklognn hkdnn Clog Cd
        hClogpos hCdpos d₁ hd₁
      set B₀ : ℝ := (d₁ : ℝ) ^ (-(200 * (1 - β₁))) with hB₀def
      have hB₀pos : 0 < B₀ := by
        rw [hB₀def]
        exact Real.rpow_pos_of_pos (by exact_mod_cast (show (0 : ℕ) < d₁ by omega)) _
      set c₂ : ℝ := min ε₁ (min (1 - βs) (min 1 (c₃ * (1 - β₁) * B₀ / (A * A ^ (200 : ℕ)))))
        with hc₂def
      have hc₂val : 0 < c₃ * (1 - β₁) * B₀ / (A * A ^ (200 : ℕ)) := by
        have h1 : 0 < 1 - β₁ := by linarith
        have h3 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
        have h4 : 0 < A ^ (200 : ℕ) := pow_pos h3 200
        exact div_pos (mul_pos (mul_pos hc₃pos h1) hB₀pos) (mul_pos h3 h4)
      have hc₂pos : 0 < c₂ := by
        rw [hc₂def]
        exact lt_min hε₁pos (lt_min (by linarith) (lt_min one_pos hc₂val))
      have hc₂leε₁ : c₂ ≤ ε₁ := by rw [hc₂def]; exact min_le_left _ _
      have hc₂leβs : c₂ ≤ 1 - βs := by
        rw [hc₂def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
      have hc₂lec₃ : c₂ ≤ c₃ * (1 - β₁) * B₀ / (A * A ^ (200 : ℕ)) := by
        rw [hc₂def]
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
      refine ⟨c₂, hc₂pos, fun d chi Lam hd hχ hre hAn hagr s him hs1 hs2 => ?_⟩
      intro hLval
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have hdpos : 0 < (d : ℝ) := by linarith
      have h2 : (1 : ℝ) ≤ (d : ℝ) ^ ε := Real.one_le_rpow hd1 hε.le
      have hpowpos : 0 < (d : ℝ) ^ ε := lt_of_lt_of_le one_pos h2
      have hdiv_le_c : c₂ / (d : ℝ) ^ ε ≤ c₂ := by
        rw [div_le_iff₀ hpowpos]
        calc c₂ = c₂ * 1 := by ring
          _ ≤ c₂ * (d : ℝ) ^ ε := mul_le_mul_of_nonneg_left h2 hc₂pos.le
      have hdiv_le_ε₁ : c₂ / (d : ℝ) ^ ε ≤ ε₁ := le_trans hdiv_le_c hc₂leε₁
      have hsre1 : 1 - ε₁ < s.re := by linarith
      have hsre : 0 < s.re := by linarith
      by_cases hgt : 1 < s.re
      · -- `re s > 1`: the Euler product
        have hLam : Lam s ≠ 0 := by
          rw [hagr s hgt]
          exact mul_ne_zero (Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd 0 hsre)
            (Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi 0
              hχ.1.1 hχ.1.2.1 hχ.1.2.2.1 hgt)
        exact (Work.FIArea6Hecke.Lval_ne_zero_iff hd 0 hsre).mpr hLam hLval
      · push Not at hgt
        have hs_lt1 : s.re < 1 := by
          refine lt_of_le_of_ne hgt ?_
          intro h1
          have hs_eq : s = ((s.re : ℝ) : ℂ) := by
            apply Complex.ext
            · simp
            · simpa using him
          have hs1' : s = 1 := by rw [hs_eq, h1]; norm_num
          have hLam1 : Lam 1 ≠ 0 :=
            Work.FIArea6Hecke.R.LamOneNeZeroRealV hd hχ hre hAn hagr
          rw [hs1'] at hLval
          rw [Work.FIArea6Hecke.Lval] at hLval
          exact hLam1 ((div_eq_zero_iff.mp hLval).resolve_right
            (Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd 0 (by norm_num)))
        by_cases hprin : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
            chi₁ z * chi z = Work.FIArea6Hecke.principalStrict (d₁ * d) z
        · -- **sub-case (a)**
          have hagree := Work.FIArea6Hecke.R.zc_eq_of_mul_eq_one_on_primary_units hχ₁ hχ hre₁ hprin
          have hs_eq : s = ((s.re : ℝ) : ℂ) := by
            apply Complex.ext
            · simp
            · simpa using him
          have hzero : Work.FIArea6Hecke.Lval d 0 Lam (s.re : ℂ) = 0 := by
            rw [← hs_eq]; exact hLval
          have hzero₁' : Work.FIArea6Hecke.Lval d₁ 0 Lam₁ (s.re : ℂ) = 0 :=
            Work.FIArea6Hecke.R.same_real_zeros_of_agree_on_primary_units hd₁ hd hχ₁ hχ hagree
              hAn₁ hagr₁ hAn hagr hsre hs_lt1 hzero
          have hLam_zero : Lam₁ (s.re : ℂ) = 0 := by
            rw [Work.FIArea6Hecke.Lval] at hzero₁'
            exact (div_eq_zero_iff.mp hzero₁').resolve_right
              (Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd₁ 0 hsre)
          have hle : s.re ≤ βs := hβs_max s.re hsre hs_lt1 hLam_zero
          linarith
        · -- **sub-case (b)**: the product character is nontrivial on a primary unit
          push Not at hprin
          obtain ⟨z₀, hz₀prim, hz₀ne⟩ := hprin
          have hprod : Work.FIArea5.S16Hecke.IsCharMod4dStrict (d₁ * d)
              (fun z => chi₁ z * chi z) :=
            Work.FIArea6Hecke.R.zc_isCharMod4dStrict_mul hd₁ hd hχ₁ hχ
          have hz₀u : Work.FIArea5.S16Hecke.IsUnitMod4d (d₁ * d) z₀ := by
            by_contra hzu
            have h1 : chi₁ z₀ * chi z₀ = 0 := hprod.2 z₀ hzu
            have h2 : Work.FIArea6Hecke.principalStrict (d₁ * d) z₀ = 0 :=
              Work.FIArea6Hecke.principalStrict_of_not_unit hzu
            rw [h1, h2] at hz₀ne
            exact hz₀ne rfl
          have hz₀1 : chi₁ z₀ * chi z₀ ≠ 1 := by
            intro h1
            refine hz₀ne ?_
            rw [h1, Work.FIArea6Hecke.principalStrict_of_unit hz₀u]
          have hdre : ∀ z : GaussianInt,
              (fun z => chi₁ z * chi z) z = star ((fun z => chi₁ z * chi z) z) := by
            intro z
            show chi₁ z * chi z = star (chi₁ z * chi z)
            rw [star_mul, ← hre z, ← hre₁ z]
            ring
          have hbnd : ∀ z : GaussianInt, ‖(fun z => chi₁ z * chi z) z‖ ≤ 1 := by
            intro z
            rw [norm_mul]
            exact mul_le_one₀ (hχ₁.1.2.2.1 z) (norm_nonneg _) (hχ.1.2.2.1 z)
          have hd₁d : 1 ≤ d₁ * d :=
            Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
          obtain ⟨Lam12, hAn12, hagr12⟩ :=
            Work.FIArea6Hecke.R.exists_completion_strict hd₁d hprod ⟨z₀, hz₀prim, hz₀u, hz₀1⟩
          set F : ℂ → ℂ := fun z => Work.FIArea6Hecke.Lval (d₁ * d) 0 Lam12 z with hFdef
          have hFball : AnalyticOnNhd ℂ F (Metric.closedBall (2 : ℂ) (3 / 2)) :=
            fun z hz => Work.FIArea6Hecke.R.analyticAt_Lval_of_mem_ball hd₁d hAn12 hz
          have hFagr : ∀ s : ℂ, 1 < s.re →
              F s = Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi z) 0 s := by
            intro s hs
            have hs0 : 0 < s.re := by linarith
            have hne : Work.FITop4.Bridge.heckeArch (d₁ * d) 0 s ≠ 0 :=
              Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd₁d 0 hs0
            have hFs : F s = Lam12 s / Work.FITop4.Bridge.heckeArch (d₁ * d) 0 s := rfl
            rw [hFs, hagr12 s hs]
            exact mul_div_cancel_left₀ _ hne
          -- the constant `K`
          set K : ℝ := max 1 (Clog * (Real.log (8 * (d₁ : ℝ) * (d : ℝ))) ^ klog) with hKdef
          have hK1 : 1 ≤ K := le_max_left _ _
          have hF1 : ‖F 1‖ ≤ K := by
            have hgen := hlogBd (d₁ * d) hd₁d (fun z => chi₁ z * chi z) hprod
              ⟨z₀, hz₀prim, hz₀u, hz₀1⟩ Lam12 hAn12 hagr12 1 (by norm_num)
            have hlogeq : Real.log (4 * ((d₁ * d : ℕ) : ℝ) * (2 + |((1 : ℂ)).im|))
                = Real.log (8 * (d₁ : ℝ) * (d : ℝ)) := by
              congr 1
              simp
              push_cast
              ring
            rw [hlogeq] at hgen
            have hFs : F 1 = Work.FIArea6Hecke.Lval (d₁ * d) 0 Lam12 1 := rfl
            rw [hFs]
            exact le_trans hgen (le_max_right _ _)
          have hKbound : K ≤ A * (d : ℝ) ^ (ε / 400) := by
            have h1 : Clog * (Real.log (8 * (d₁ : ℝ) * (d : ℝ))) ^ klog
                ≤ A * (d : ℝ) ^ (ε / 400) := (hAb d hd).1
            have hdle : (1 : ℝ) ≤ (d : ℝ) ^ (ε / 400) := Real.one_le_rpow hd1 (by positivity)
            have hA1' : (1 : ℝ) ≤ A * (d : ℝ) ^ (ε / 400) := by nlinarith [hA1, hdle]
            rw [hKdef]
            exact max_le hA1' h1
          -- the constant `D`
          set D : ℝ := Cd * (2 * (d : ℝ)) ^ (ε / 4) * (Real.log (8 * (d : ℝ))) ^ kd with hDdef
          have hDpos : 0 < D := by
            rw [hDdef]
            have h2d : (0 : ℝ) < 2 * (d : ℝ) := by positivity
            have hl : 0 < Real.log (8 * (d : ℝ)) := by
              refine Real.log_pos ?_
              nlinarith
            exact mul_pos (mul_pos hCdpos (Real.rpow_pos_of_pos h2d _))
              (Real.rpow_pos_of_pos hl _)
          have hDbound : D ≤ A * (d : ℝ) ^ (3 * ε / 8) := (hAb d hd).2
          -- the mean-value step
          have hderiv : ∀ t : ℝ, s.re ≤ t → t ≤ 1 →
              ‖deriv (fun z : ℂ => Work.FIArea6Hecke.Lval d 0 Lam z) ((t : ℝ) : ℂ)‖ ≤ D := by
            intro t ht0 ht1
            have ht512 : 1 / 2 ≤ ((t : ℂ)).re := by
              rw [Complex.ofReal_re]
              linarith [hsre1, hε₁le20, ht0]
            have ht1' : ((t : ℂ)).re ≤ 1 := by rw [Complex.ofReal_re]; exact ht1
            have hdb := hderivbd d hd chi hχ hre hχ.1.2.2.1 Lam hAn hagr (t : ℂ) ht512 ht1'
            have hexp : Kd * (1 - t) ≤ ε / 4 := by
              have h1t : 1 - t ≤ ε₁ := by linarith
              nlinarith [hKdnn, hKdε₁, hε₁pos, h1t]
            simp only [Complex.ofReal_im, Complex.ofReal_re, abs_zero, add_zero] at hdb
            have harg1 : 4 * (d : ℝ) * 2 = 8 * (d : ℝ) := by ring
            rw [harg1] at hdb
            have harg2 : (d : ℝ) * 2 = 2 * (d : ℝ) := by ring
            rw [harg2] at hdb
            refine le_trans hdb ?_
            rw [hDdef]
            have hbase1 : (1 : ℝ) ≤ 2 * (d : ℝ) := by linarith
            have hpowmono : (2 * (d : ℝ)) ^ (Kd * (1 - t)) ≤ (2 * (d : ℝ)) ^ (ε / 4) :=
              Real.rpow_le_rpow_of_exponent_le hbase1 hexp
            have hlogpos : (0 : ℝ) ≤ (Real.log (8 * (d : ℝ))) ^ kd :=
              Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
            have hkey := mul_le_mul_of_nonneg_right hpowmono hlogpos
            calc Cd * (2 * (d : ℝ)) ^ (Kd * (1 - t)) * (Real.log (8 * (d : ℝ))) ^ kd
                = Cd * ((2 * (d : ℝ)) ^ (Kd * (1 - t)) * (Real.log (8 * (d : ℝ))) ^ kd) := by
                  ring
              _ ≤ Cd * ((2 * (d : ℝ)) ^ (ε / 4) * (Real.log (8 * (d : ℝ))) ^ kd) :=
                  mul_le_mul_of_nonneg_left hkey hCdpos.le
              _ = Cd * (2 * (d : ℝ)) ^ (ε / 4) * (Real.log (8 * (d : ℝ))) ^ kd := by ring
          have hMT : ‖Work.FIArea6Hecke.Lval d 0 Lam 1‖ ≤ (1 - s.re) * D := by
            have hs_eq : s = ((s.re : ℝ) : ℂ) := by
              apply Complex.ext
              · simp
              · simpa using him
            have hzero : Work.FIArea6Hecke.Lval d 0 Lam (s.re : ℂ) = 0 := by
              rw [← hs_eq]; exact hLval
            refine Work.FIArea6Hecke.R.Lval_one_norm_le_of_real_zero_segment hd hχ hre hAn hagr
              hsre hs_lt1 ?_ hzero hDpos.le hderiv
            linarith [hε₁le20, hsre1]
          -- the Estermann input for this datum
          have hLamB : ∀ s' : ℂ, s' ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
              ‖Work.FIArea6Hecke.Lval d 0 Lam s'‖ ≤ Cc * (d : ℝ) ^ (10 : ℕ) :=
            hballAt d hd chi hχ hre hχ.1.2.2.1 Lam hAn hagr
          have hFb : ∀ s' : ℂ, s' ∈ Metric.closedBall (2 : ℂ) (3 / 2) →
              ‖F s'‖ ≤ Cc * ((d₁ * d : ℕ) : ℝ) ^ (10 : ℕ) := by
            intro s' hs'
            have h := hballAt (d₁ * d) hd₁d (fun z => chi₁ z * chi z) hprod hdre hbnd
              Lam12 hAn12 hagr12 s' hs'
            have hFs : F s' = Work.FIArea6Hecke.Lval (d₁ * d) 0 Lam12 s' := rfl
            rw [hFs]
            exact h
          have hE3 := hE₃ d hd chi hχ.1.1 hre hχ.1.2.1 hχ.1.2.2.1 Lam hAn hagr F hFball hFagr
            K hK1 hF1 hLamB hFb
          have hcomb : c₃ * (1 - β₁) * K ^ (-(200 : ℝ)) *
                (max (d₁ : ℝ) (d : ℝ)) ^ (-(200 * (1 - β₁))) ≤ (1 - s.re) * D :=
            le_trans hE3 hMT
          -- the two hypotheses of the arithmetic lemma
          have h200 : 200 * (1 - β₁) ≤ ε / 8 := by
            nlinarith [hβ₁lo, h90ε₁, hε₁pos, hε]
          have hBhyp : B₀ * (d : ℝ) ^ (-(ε / 8)) ≤
              (max (d₁ : ℝ) (d : ℝ)) ^ (-(200 * (1 - β₁))) := by
            have hd₁1 : (1 : ℝ) ≤ (d₁ : ℝ) := by exact_mod_cast hd₁
            have hmax_le : max (d₁ : ℝ) (d : ℝ) ≤ (d₁ : ℝ) * (d : ℝ) := by
              refine max_le ?_ ?_
              · nlinarith [hd1]
              · nlinarith [hd1, hd₁1]
            have hstep : ((d₁ : ℝ) * (d : ℝ)) ^ (-(200 * (1 - β₁)))
                ≤ (max (d₁ : ℝ) (d : ℝ)) ^ (-(200 * (1 - β₁))) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hmax_le (by nlinarith [hβ₁hi])
            have hmul : ((d₁ : ℝ) * (d : ℝ)) ^ (-(200 * (1 - β₁)))
                = B₀ * (d : ℝ) ^ (-(200 * (1 - β₁))) := by
              rw [hB₀def, Real.mul_rpow (by exact_mod_cast (show (0 : ℕ) ≤ d₁ by omega)) hdpos.le]
            have hdmono : (d : ℝ) ^ (-(ε / 8)) ≤ (d : ℝ) ^ (-(200 * (1 - β₁))) :=
              Real.rpow_le_rpow_of_exponent_le hd1 (by linarith [h200])
            rw [hmul] at hstep
            calc B₀ * (d : ℝ) ^ (-(ε / 8))
                ≤ B₀ * (d : ℝ) ^ (-(200 * (1 - β₁))) :=
                  mul_le_mul_of_nonneg_left hdmono hB₀pos.le
              _ ≤ (max (d₁ : ℝ) (d : ℝ)) ^ (-(200 * (1 - β₁))) := hstep
          have hfinal := Work.FIArea6Hecke.R.siegelFinalArith ε hε d₁ d c₃ β₁ B₀ K D A (1 - s.re)
            hd₁ hd hc₃pos hβ₁pos hβ₁hi
            hB₀pos hA1 hK1 hDpos h200 hBhyp hKbound hDbound hcomb
          -- contradiction with the hypothesis of the region
          have hle3 : c₂ / (d : ℝ) ^ ε ≤ 1 - s.re :=
            le_trans (div_le_div_of_nonneg_right hc₂lec₃ (Real.rpow_pos_of_pos hdpos ε).le)
              hfinal
          linarith [hs1, hle3]
    · -- **Case 1**: there is no exceptional real zero; the threshold itself works.
      refine ⟨ε₁, hε₁pos, fun d chi Lam hd hχ hre hAn hagr s him hs1 hs2 => ?_⟩
      intro hLval
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have h2 : (1 : ℝ) ≤ (d : ℝ) ^ ε := Real.one_le_rpow hd1 hε.le
      have hpowpos : 0 < (d : ℝ) ^ ε := lt_of_lt_of_le one_pos h2
      have h3 : ε₁ / (d : ℝ) ^ ε ≤ ε₁ := by
        rw [div_le_iff₀ hpowpos]
        calc ε₁ = ε₁ * 1 := by ring
          _ ≤ ε₁ * (d : ℝ) ^ ε := mul_le_mul_of_nonneg_left h2 hε₁pos.le
      have hsre1 : 1 - ε₁ < s.re := by linarith
      have hsre : 0 < s.re := by linarith
      have hs_eq : s = ((s.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simpa using him
      by_cases hgt : 1 < s.re
      · have hLam : Lam s ≠ 0 := by
          rw [hagr s hgt]
          exact mul_ne_zero (Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd 0 hsre)
            (Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi 0
              hχ.1.1 hχ.1.2.1 hχ.1.2.2.1 hgt)
        exact (Work.FIArea6Hecke.Lval_ne_zero_iff hd 0 hsre).mpr hLam hLval
      · push Not at hgt
        have hlt1 : s.re < 1 := by
          refine lt_of_le_of_ne hgt ?_
          intro h1
          have hs1' : s = 1 := by rw [hs_eq, h1]; norm_num
          have hLam1 : Lam 1 ≠ 0 := Work.FIArea6Hecke.R.LamOneNeZeroRealV hd hχ hre hAn hagr
          rw [hs1'] at hLval
          rw [Work.FIArea6Hecke.Lval] at hLval
          exact hLam1 ((div_eq_zero_iff.mp hLval).resolve_right
            (Work.FIArea6Hecke.heckeArch_ne_zero_of_pos_re hd 0 (by norm_num)))
        have hzero' : Work.FIArea6Hecke.Lval d 0 Lam (s.re : ℂ) = 0 := by
          rw [← hs_eq]; exact hLval
        exact absurd ⟨d, chi, Lam, s.re, hd, hχ, hre, hAn, hagr, hsre1, hlt1, hzero'⟩ hex
  -- ## transfer from the threshold back to the given `ε`
  obtain ⟨c, hc, hmain'⟩ := hmain
  refine ⟨c, hc, fun d chi m Lam hd hχ hAn hagr hpsi s him hs1 hs2 => ?_⟩
  have hm : m = 0 := Work.FIArea6Hecke.R.m_eq_zero_of_psiReal hd hχ hpsi
  subst hm
  have hre : ∀ z : GaussianInt, chi z = star (chi z) :=
    fun z => ((Work.FIArea6Hecke.R.psiReal_zero_iff.mp hpsi) z).symm
  have hagr0 : ∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
    intro s hs
    simpa using hagr s (by simpa using hs)
  exact hmain' d chi Lam hd hχ hre hAn hagr0 s him hs1 hs2

end

end Work.FIArea6Hecke.R
