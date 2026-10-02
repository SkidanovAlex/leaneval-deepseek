import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_band_poly
import Submission.Commons.NumberTheory.DirichletCharacter.L_lower_re_two
import Submission.Commons.NumberTheory.Linnik.completedL_growth_circle

open Complex DirichletCharacter Metric
open scoped Real Topology BigOperators
set_option maxHeartbeats 0

noncomputable section

namespace Commons.NumberTheory.DirichletCharacter
private lemma Λ_eq_L_mul_gamma {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {z : ℂ}
    (hz : 0 < z.re) :
    DirichletCharacter.completedLFunction χ z =
      DirichletCharacter.LFunction χ z * χ.gammaFactor z :=
  Commons.NumberTheory.Linnik.completedLFunction_eq_mul_gammaFactor_re_pos χ hz

private lemma Gammaℝ_analyticAt_of_re_pos {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Complex.Gammaℝ z := by
  have hinv : Differentiable ℂ (fun s : ℂ => s.Gammaℝ⁻¹) := Complex.differentiable_Gammaℝ_inv
  have hinvz : (fun s : ℂ => s.Gammaℝ⁻¹) z ≠ 0 := by
    dsimp
    exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz)
  have han0 : AnalyticAt ℂ (fun s : ℂ => (s.Gammaℝ⁻¹)⁻¹) z :=
    (hinv.analyticAt z).inv hinvz
  convert han0 with s
  · rw [inv_inv]

private lemma gammaFactor_analyticAt_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ}
    (hz : 0 < z.re) : AnalyticAt ℂ (χ.gammaFactor) z := by
  rcases χ.even_or_odd with hE | hO
  · have hγ : χ.gammaFactor = Complex.Gammaℝ := by
      funext s
      exact Even.gammaFactor_def hE s
    rw [hγ]
    exact Gammaℝ_analyticAt_of_re_pos hz
  · have hγ : χ.gammaFactor = (fun s : ℂ => Complex.Gammaℝ (s + 1)) := by
      funext s
      exact Odd.gammaFactor_def hO s
    rw [hγ]
    change AnalyticAt ℂ (fun s : ℂ => Complex.Gammaℝ (s + 1)) z
    refine AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun s : ℂ => s + 1) (x := z) ?_ ?_
    · have hz1 : 0 < (z + 1).re := by simp; linarith only [hz]
      exact Gammaℝ_analyticAt_of_re_pos hz1
    · fun_prop

private lemma gammaFactor_ne_zero_of_re_pos {N : ℕ} (χ : DirichletCharacter ℂ N) {z : ℂ}
    (hz : 0 < z.re) : χ.gammaFactor z ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [Even.gammaFactor_def hE]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hz
  · rw [Odd.gammaFactor_def hO]
    have hz1 : 0 < (z + 1).re := by simp; linarith only [hz]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hz1

private lemma divisor_completedL_le_divisor_L {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (U : Set ℂ) {u : ℂ} (huU : u ∈ U) (hre : 0 < u.re) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) U u ≤
      MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U u := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let L : ℂ → ℂ := DirichletCharacter.LFunction χ
  have hΛan : AnalyticOnNhd ℂ Λ U := by
    intro z hz
    exact (differentiable_completedLFunction hχ).analyticAt z
  have hLan : AnalyticOnNhd ℂ L U := by
    intro z hz
    exact (differentiable_LFunction hχ).analyticAt z
  by_cases h0 : Λ u = 0
  · have hγan : AnalyticAt ℂ (χ.gammaFactor) u := gammaFactor_analyticAt_of_re_pos χ hre
    have hγ0 : χ.gammaFactor u ≠ 0 := gammaFactor_ne_zero_of_re_pos χ hre
    have hev' : {z : ℂ | 0 < z.re} ∈ 𝓝[≠] u := by
      simpa [nhdsWithin] using
        (Filter.mem_inf_of_left ((isOpen_lt continuous_const continuous_re).mem_nhds hre))
    have hfun : (fun z : ℂ => Λ z) =ᶠ[𝓝[≠] u] fun z : ℂ => χ.gammaFactor z * L z := by
      filter_upwards [hev'] with z hz
      · dsimp [Λ, L]
        rw [Λ_eq_L_mul_gamma χ hz]
        ring
    have hordL : meromorphicOrderAt (fun z : ℂ => χ.gammaFactor z * L z) u =
        meromorphicOrderAt L u :=
      meromorphicOrderAt_mul_of_ne_zero hγan hγ0
    have hord : meromorphicOrderAt Λ u = meromorphicOrderAt L u := by
      dsimp [Λ]
      calc
        meromorphicOrderAt (fun z : ℂ => DirichletCharacter.completedLFunction χ z) u
            = meromorphicOrderAt (fun z : ℂ => χ.gammaFactor z * L z) u := meromorphicOrderAt_congr hfun
        _ = meromorphicOrderAt L u := hordL
    have hdΛ : MeromorphicOn.divisor Λ U u = MeromorphicOn.divisor L U u := by
      rw [MeromorphicOn.divisor_apply hΛan.meromorphicOn huU,
        MeromorphicOn.divisor_apply hLan.meromorphicOn huU]
      exact congrArg (WithTop.untop₀ (α := ℤ)) hord
    rw [hdΛ]
  · have hd : MeromorphicOn.divisor Λ U u = 0 := by
      rw [MeromorphicOn.divisor_apply hΛan.meromorphicOn huU]
      have hAn : AnalyticAt ℂ Λ u := hΛan u huU
      have hord : meromorphicOrderAt Λ u = 0 := by
        rw [hAn.meromorphicOrderAt_eq]
        have h0 : analyticOrderAt Λ u = 0 := analyticOrderAt_eq_zero.mpr (Or.inr h0)
        simp [h0]
      simp [hord]
    have hnn : 0 ≤ MeromorphicOn.divisor L U u := by
      rw [MeromorphicOn.divisor_apply hLan.meromorphicOn huU]
      have hAn : AnalyticAt ℂ L u := hLan u huU
      have hNF := hAn.meromorphicNFAt
      have hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt L u :=
        (MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hNF).2 hAn
      exact (WithTop.untop₀_nonneg (α := ℤ) (a := meromorphicOrderAt L u)).mpr hord
    rw [hd]
    exact hnn


private lemma closedBall_abs_self {c : ℂ} {r : ℝ} (hr : 0 ≤ r) :
    Metric.closedBall c |r| = Metric.closedBall c r := by
  ext z
  simp [abs_of_nonneg hr]

/-- the divisor sum of L over a unit-height window, bounded. -/
theorem L_window_divisor_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ cw : ℝ, 0 ≤ cw ∧ ∀ T : ℝ,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * (T : ℂ)) 2.5)) u : ℤ) : ℝ)) ≤
        cw * (Real.log (2 + |T|) + Real.log (N : ℝ) + 2) := by
  classical
  let L : ℂ → ℂ := DirichletCharacter.LFunction χ
  have hLan (U : Set ℂ) : AnalyticOnNhd ℂ L U := by
    intro z hz
    exact (differentiable_LFunction hχ).analyticAt z
  rcases Commons.NumberTheory.DirichletCharacter.LFunction_band_poly χ hχ hχprim with ⟨C, k, hC, hk, hband⟩
  rcases Commons.NumberTheory.DirichletCharacter.L_lower_re_two χ hχ with ⟨c0, hc0, hlow⟩
  let mc : ℝ := max C 1
  have hC_mc : C ≤ mc := le_max_left C 1
  have hmc1 : 1 ≤ mc := le_max_right C 1
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  let A : ℝ := k * Real.log 2 + |Real.log mc| + |Real.log c0|
  let cw : ℝ := (k + A / 2) / Real.log (6 / 5)
  have hlog65 : 0 < Real.log (6 / 5) := Real.log_pos (by norm_num)
  have hcw : 0 ≤ cw := by
    dsimp [cw]
    positivity
  refine ⟨cw, hcw, ?_⟩
  intro T
  let c : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  let X : ℝ := Real.log (2 + |T|) + Real.log (N : ℝ) + 2
  let M : ℝ := mc * (1 + |T| + 3) ^ k * (N : ℝ) ^ k
  have hM1 : 1 ≤ M := by
    dsimp [M]
    have h1a : 1 ≤ (1 + |T| + 3) ^ k := Real.one_le_rpow (by linarith only [abs_nonneg T]) hk
    have h1b : 1 ≤ (N : ℝ) ^ k := Real.one_le_rpow hN1 hk
    have h2 : 1 ≤ mc * (1 + |T| + 3) ^ k := by
      calc
        1 ≤ mc := hmc1
        _ ≤ mc * (1 + |T| + 3) ^ k := by
          exact le_mul_of_one_le_right (by positivity) h1a
    calc
      1 ≤ mc * (1 + |T| + 3) ^ k := h2
      _ ≤ mc * (1 + |T| + 3) ^ k * (N : ℝ) ^ k := by
        exact le_mul_of_one_le_right (by positivity) h1b
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hfc : L c ≠ 0 := by
    intro hz
    have hz' : ‖L c‖ = 0 := by simp [hz]
    have hlow' : c0 ≤ ‖L c‖ := hlow T
    dsimp [c] at hlow'
    linarith only [hc0, hz', hlow']
  have hfb : ∀ z : ℂ, z ∈ sphere c |3| → ‖L z‖ ≤ M := by
    intro z hz
    have hznorm3 : ‖z - c‖ = 3 := by
      have hzn : ‖z - c‖ = |3| := by simpa [dist_eq_norm, Metric.sphere] using hz
      rwa [abs_of_pos (by norm_num)] at hzn
    have hzre_low : -1 ≤ z.re := by
      have hre : |z.re - 2| ≤ 3 := by
        calc
          |z.re - 2| = |(z - c).re| := by simp [c]
          _ ≤ ‖z - c‖ := Complex.abs_re_le_norm (z - c)
          _ = 3 := hznorm3
      have habs := abs_le.mp hre
      linarith only [habs]
    have hzre_high : z.re ≤ 8 := by
      have hre : |z.re - 2| ≤ 3 := by
        calc
          |z.re - 2| = |(z - c).re| := by simp [c]
          _ ≤ ‖z - c‖ := Complex.abs_re_le_norm (z - c)
          _ = 3 := hznorm3
      have habs := abs_le.mp hre
      linarith only [habs]
    have hb := hband z hzre_low hzre_high
    have hzim : |z.im| ≤ |T| + 3 := by
      have him : |z.im - T| ≤ ‖z - c‖ := by
        calc
          |z.im - T| = |(z - c).im| := by simp [c]
          _ ≤ ‖z - c‖ := Complex.abs_im_le_norm (z - c)
      have hz3 : |z.im - T| ≤ 3 := le_trans him (le_of_eq hznorm3)
      have habs := abs_le.mp hz3
      have hT1 : T ≤ |T| := le_abs_self T
      have hT2 : -|T| ≤ T := by linarith only [neg_le_abs T]
      apply abs_le.mpr
      constructor
      · linarith only [habs.1, hT2, habs]
      · linarith only [habs.2, hT1, habs]
    have hb1 : (1 + |z.im|) ≤ (1 + |T| + 3) := by linarith only [hzim]
    have hb1nn : 0 ≤ 1 + |z.im| := by positivity
    have hpow : (1 + |z.im|) ^ k ≤ (1 + |T| + 3) ^ k :=
      Real.rpow_le_rpow hb1nn hb1 hk
    have hpow0 : 0 ≤ (1 + |z.im|) ^ k := Real.rpow_nonneg hb1nn k
    have hNk0 : 0 ≤ (N : ℝ) ^ k := Real.rpow_nonneg (le_of_lt hNpos) k
    have hmc0 : 0 ≤ mc := by positivity
    calc
      ‖L z‖ ≤ C * (1 + |z.im|) ^ k * (N : ℝ) ^ k := hb
      _ ≤ mc * (1 + |T| + 3) ^ k * (N : ℝ) ^ k := by
        calc
          C * (1 + |z.im|) ^ k * (N : ℝ) ^ k ≤ mc * (1 + |z.im|) ^ k * (N : ℝ) ^ k := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC_mc hpow0) hNk0
          _ ≤ mc * (1 + |T| + 3) ^ k * (N : ℝ) ^ k := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hmc0) hNk0
      _ = M := rfl
  have hjs := AnalyticOnNhd.sum_divisor_le (c := c) (r := 2.5) (R := 3) (M := M) (f := L)
      (r_pos := by norm_num) (r_lt_R := by norm_num) (hM := hM1)
      (h₁f := hLan (Metric.closedBall c |3|)) (h₂f := hfc) (f_bound := hfb)
  have hfinZ : Function.HasFiniteSupport (fun u : ℂ => (MeromorphicOn.divisor L (Metric.closedBall c 2.5)) u) := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor L (Metric.closedBall c 2.5)).finiteSupport
        (isCompact_closedBall c 2.5))
  have hEqSum : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor L (Metric.closedBall c 2.5)) u : ℤ) : ℝ)) =
      ↑(∑ᶠ u : ℂ, ((MeromorphicOn.divisor L (Metric.closedBall c |2.5|)) u : ℤ)) := by
    calc
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor L (Metric.closedBall c 2.5)) u : ℤ) : ℝ))
          = ↑(∑ᶠ u : ℂ, ((MeromorphicOn.divisor L (Metric.closedBall c 2.5)) u : ℤ)) := by
              simpa using ((Int.castRingHom ℝ).map_finsum hfinZ).symm
      _ = ↑(∑ᶠ u : ℂ, ((MeromorphicOn.divisor L (Metric.closedBall c |2.5|)) u : ℤ)) := by
              congr 1
              apply finsum_congr
              intro u
              rw [show Metric.closedBall c 2.5 = Metric.closedBall c |2.5| by
                exact (closedBall_abs_self (r := 2.5) (by norm_num)).symm]
  have hsum : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor L (Metric.closedBall c 2.5)) u : ℤ) : ℝ)) ≤
      Real.log (M / ‖L c‖) / Real.log (3 / 2.5) := by
    rw [hEqSum]
    simpa [M] using hjs
  have hlc0 : 0 < ‖L c‖ := norm_pos_iff.mpr hfc
  have hlogM : Real.log M = Real.log mc + k * Real.log (1 + |T| + 3) + k * Real.log (N : ℝ) := by
    dsimp [M]
    let A : ℝ := (1 + |T| + 3) ^ k
    let B : ℝ := (N : ℝ) ^ k
    have hApos : 0 < A := by dsimp [A]; positivity
    have hBpos : 0 < B := by dsimp [B]; exact Real.rpow_pos_of_pos hNpos k
    have hmcpos : 0 < mc := lt_of_lt_of_le zero_lt_one hmc1
    have hmcB : 0 < mc * A := mul_pos hmcpos hApos
    calc
      Real.log (mc * A * B) = Real.log ((mc * A) * B) := by ring
      _ = Real.log (mc * A) + Real.log B := Real.log_mul (ne_of_gt hmcB) (ne_of_gt hBpos)
      _ = (Real.log mc + Real.log A) + Real.log B := by rw [Real.log_mul (ne_of_gt hmcpos) (ne_of_gt hApos)]
      _ = Real.log mc + Real.log A + Real.log B := by ring
      _ = Real.log mc + k * Real.log (1 + |T| + 3) + k * Real.log (N : ℝ) := by
        dsimp [A, B]
        rw [Real.log_rpow (by positivity : 0 < 1 + |T| + 3) k]
        rw [Real.log_rpow hNpos k]
  have hlogc_lower : Real.log c0 ≤ Real.log ‖L c‖ := by
    exact Real.log_le_log hc0 (hlow T)
  have hlogM1 : Real.log M - Real.log ‖L c‖ ≤ Real.log M + |Real.log c0| := by
    have h3 : -Real.log c0 ≤ |Real.log c0| := neg_le_abs (Real.log c0)
    linarith only [hlogc_lower, h3]
  have hle1 : Real.log (1 + |T| + 3) ≤ Real.log (2 + |T|) + Real.log 2 := by
    have hpos1 : 0 < 1 + |T| + 3 := by positivity
    have hle : 1 + |T| + 3 ≤ (2 + |T|) * 2 := by linarith only [abs_nonneg T]
    have h := Real.log_le_log hpos1 hle
    rw [Real.log_mul (ne_of_gt (by positivity : 0 < 2 + |T|)) (ne_of_gt (by norm_num : 0 < (2 : ℝ)))] at h
    linarith only [h]
  have hlogM2 : Real.log M ≤ k * Real.log (2 + |T|) + k * Real.log (N : ℝ) + (k * Real.log 2 + |Real.log mc|) := by
    have habsc0 : 0 ≤ |Real.log c0| := abs_nonneg _

    have hmcl : Real.log mc ≤ |Real.log mc| := le_abs_self (Real.log mc)
    have hle2 : k * Real.log (1 + |T| + 3) ≤ k * Real.log (2 + |T|) + k * Real.log 2 := by
      calc
        k * Real.log (1 + |T| + 3) ≤ k * (Real.log (2 + |T|) + Real.log 2) := by
          exact mul_le_mul_of_nonneg_left hle1 hk
        _ = k * Real.log (2 + |T|) + k * Real.log 2 := by ring
    calc
      Real.log M = Real.log mc + k * Real.log (1 + |T| + 3) + k * Real.log (N : ℝ) := hlogM
      _ ≤ Real.log mc + (k * Real.log (2 + |T|) + k * Real.log 2) + k * Real.log (N : ℝ) := by
        linarith only [hle2]
      _ = k * Real.log (2 + |T|) + k * Real.log (N : ℝ) + (k * Real.log 2 + Real.log mc) := by
        ring
      _ ≤ k * Real.log (2 + |T|) + k * Real.log (N : ℝ) + (k * Real.log 2 + |Real.log mc|) := by
        linarith only [hmcl]
  have hLogNn0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hLogT0 : 0 ≤ Real.log (2 + |T|) := Real.log_nonneg (by linarith only [abs_nonneg T])
  have hlogM3 : k * Real.log (2 + |T|) + k * Real.log (N : ℝ) + A ≤ (k + A / 2) * X := by
    dsimp [X]
    have hknn : 0 ≤ k := hk
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hhalf : (1 : ℝ) ≤ (1 / 2) * (Real.log (2 + |T|) + Real.log (N : ℝ) + 2) := by
      linarith only [hLogT0, hLogNn0]
    have h1 : k * Real.log (2 + |T|) + k * Real.log (N : ℝ) ≤ k * (Real.log (2 + |T|) + Real.log (N : ℝ) + 2) := by
      linarith only [hk]
    have h2 : A ≤ A * ((1 / 2) * (Real.log (2 + |T|) + Real.log (N : ℝ) + 2)) := by
      nlinarith only [hLogNn0, hA, hLogT0]
    linarith only [hk, h2]
  have hratio : Real.log (M / ‖L c‖) / Real.log (3 / 2.5) ≤ cw * X := by
    have hlg : Real.log (3 / 2.5) = Real.log (6 / 5) := by norm_num
    have hb1 : Real.log (M / ‖L c‖) ≤ (k + A / 2) * X := by
      rw [Real.log_div (ne_of_gt hMpos) (ne_of_gt hlc0)]
      calc
        Real.log M - Real.log ‖L c‖ ≤ Real.log M + |Real.log c0| := hlogM1
        _ ≤ k * Real.log (2 + |T|) + k * Real.log (N : ℝ) + (k * Real.log 2 + |Real.log mc|) + |Real.log c0| := by
          linarith only [hlogM2]
        _ = k * Real.log (2 + |T|) + k * Real.log (N : ℝ) + A := by
          dsimp [A]
          ring
        _ ≤ (k + A / 2) * X := by
          have hA2 : A ≤ (A / 2) * X := by
            dsimp [X]
            have hA0 : 0 ≤ A := by dsimp [A]; positivity
            have hX2 : 2 ≤ Real.log (2 + |T|) + Real.log (N : ℝ) + 2 := by linarith only [hLogT0, hLogNn0]
            have h12 : (1 : ℝ) ≤ (1 / 2) * (Real.log (2 + |T|) + Real.log (N : ℝ) + 2) := by
              linarith only [hLogT0, hLogNn0]
            nlinarith only [hLogNn0, hA0, hLogT0]
          linarith only [hlogM3, hA2]
    calc
      Real.log (M / ‖L c‖) / Real.log (3 / 2.5) ≤ (k + A / 2) * X / Real.log (3 / 2.5) := by
        exact div_le_div_of_nonneg_right hb1 (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2.5)))
      _ ≤ cw * X := by
        have hlg' : (k + A / 2) * X / Real.log (3 / 2.5) = cw * X := by
          dsimp [cw]
          rw [hlg]
          ring_nf
        exact le_of_eq hlg'
  have hfinal : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor L (Metric.closedBall c 2.5)) u : ℤ) : ℝ)) ≤ cw * X := by
    exact le_trans hsum hratio
  have hrew : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (Metric.closedBall ((2 : ℂ) + Complex.I * (T : ℂ)) 2.5)) u : ℤ) : ℝ)) =
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor L (Metric.closedBall c 2.5)) u : ℤ) : ℝ)) := by
    dsimp [L, c]
  rw [hrew]
  exact hfinal

