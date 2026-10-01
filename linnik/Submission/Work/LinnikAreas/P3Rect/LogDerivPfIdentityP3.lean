/-
# `LogDerivPfIdentityP3`: the `logDeriv_pf_identity` content missing from the `rect` file

The module `Commons.NumberTheory.Linnik.logDeriv_pf_identity` declares 28 constants that are
also declared by `Commons.NumberTheory.Linnik.completedL_pf_identity_rect`; the two files
can therefore never be imported into one environment.  26 of the 28 declarations are
*verbatim* the same in the two files, and the two remaining ones (`pf_P0_log_bound`,
`pf_P_ne_zero_circle`) have the same statement up to definitional unfolding.  This module
provides the part of the `logDeriv_pf_identity` surface that the `rect` file does *not*
have (the six declarations `pf_cofactor_logbound`, `pfLD`, `pfSum`, `pf_perterm`,
`pf_defect_bound`, `logDeriv_pf_identity`), on top of the `rect` file; the local copy of
`pf_P0_log_bound` is renamed `pf_P0_log_bound_p3` so that no name is declared twice.
-/
import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.NumberTheory.Linnik.completedL_growth_circle
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Commons.NumberTheory.Linnik.partialFraction_conv
import Submission.Commons.NumberTheory.Linnik.partialFraction_tail
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue_pair
import Submission.Commons.NumberTheory.Linnik.ell_pow_div_self_tendsto_zero
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
open Complex DirichletCharacter Metric Filter Function Set MeromorphicOn Topology
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

namespace Commons.NumberTheory.Linnik

-- local copy of the `logDeriv_pf_identity` version of `pf_P0_log_bound` (see the header)
lemma pf_P0_log_bound_p3 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ T)
    (δ₀ : ℝ) (hδ₀pos : 0 < δ₀) (hδ₀ : ∀ u : ℂ,
      DirichletCharacter.completedLFunction χ u = 0 → δ₀ ≤ ‖u‖) :
    |Real.log ‖pfP N χ T 0‖| ≤
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (closedBall (0 : ℂ) T)) u : ℤ) : ℝ)) * (Real.log T + |Real.log δ₀|) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T) u
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact pf_divisor_nonneg_closedBall χ hχ T u
  have hsupport : (Function.support d).Finite := by
    dsimp [d]
    exact pf_divisor_support_finite χ hχ T
  let S : Finset ℂ := hsupport.toFinset
  have hmemS : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hdist0 : ∀ u : ℂ, u ∈ S → δ₀ ≤ ‖u‖ ∧ ‖u‖ ≤ T := by
    intro u hu
    have hdne : d u ≠ 0 := (hmemS u).mp hu
    have hzu : Λ u = 0 := by
      dsimp [d] at hdne
      exact pf_divisor_ne_zero_is_zero χ hχ hdne
    have huδ : δ₀ ≤ ‖u‖ := hδ₀ u (by simpa [Λ] using hzu)
    have hdne0 : (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)) u ≠ 0 := by
      simpa [d] using hdne
    have huT : ‖u‖ ≤ T := by
      have hmemB : u ∈ closedBall (0 : ℂ) T := by
        by_contra hout
        rw [MeromorphicOn.divisor_def] at hdne0
        simp [hout] at hdne0
      simpa [Metric.mem_closedBall, dist_eq_norm] using hmemB
    exact ⟨huδ, huT⟩
  let B : ℝ := Real.log T + |Real.log δ₀|
  have hlogTpos : 0 ≤ Real.log T := Real.log_nonneg hT
  have hlogB : ∀ u : ℂ, u ∈ S → |Real.log ‖u‖| ≤ B := by
    intro u hu
    have hδle : δ₀ ≤ ‖u‖ := (hdist0 u hu).1
    have hTge : ‖u‖ ≤ T := (hdist0 u hu).2
    have hpos : 0 < ‖u‖ := lt_of_lt_of_le hδ₀pos hδle
    have hle1 : Real.log ‖u‖ ≤ B := by
      have h : Real.log ‖u‖ ≤ Real.log T := Real.log_le_log hpos hTge
      have habs : 0 ≤ |Real.log δ₀| := abs_nonneg _
      dsimp [B]
      linarith
    have hle2 : -B ≤ Real.log ‖u‖ := by
      have h : Real.log δ₀ ≤ Real.log ‖u‖ := Real.log_le_log hδ₀pos hδle
      have hnegabs : -|Real.log δ₀| ≤ Real.log δ₀ := neg_abs_le (Real.log δ₀)
      have h3 : -B ≤ -|Real.log δ₀| := by
        dsimp [B]
        linarith
      exact le_trans (le_trans h3 hnegabs) h
    exact abs_le.mpr ⟨hle2, hle1⟩
  have hnorm_fac : ∀ u : ℂ, u ∈ S → ‖(0 : ℂ) - u‖ = ‖u‖ := by
    intro u hu
    simp
  have hprod_eq : (∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (d u)) = ∏ u ∈ S, ((0 : ℂ) - u) ^ (d u) := by
    refine finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => ((0 : ℂ) - u) ^ (d u)) ?_
    intro u hu
    rw [Function.mem_mulSupport] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      have : ((0 : ℂ) - u) ^ (d u) = 1 := by simp [hd0]
      exact hu this
    exact (hmemS u).mpr hdne
  have hpos_fac : ∀ u : ℂ, u ∈ S → 0 < ‖((0 : ℂ) - u) ^ (d u)‖ := by
    intro u hu
    have hp : 0 < ‖(0 : ℂ) - u‖ := by
      rw [hnorm_fac u hu]
      exact lt_of_lt_of_le hδ₀pos (hdist0 u hu).1
    simpa [pf_norm_zpow_eq] using pf_zpow_pos hp (hd_nonneg u)
  have hlogS : |(∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖)| ≤
      (∑ u ∈ S, ((d u : ℤ) : ℝ)) * B := by
    have h1 : |∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖| ≤
        ∑ u ∈ S, |((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖| := by
      exact Finset.abs_sum_le_sum_abs (fun u => ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖) S
    have h2 : (∑ u ∈ S, |((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖|) ≤
        ∑ u ∈ S, (((d u : ℤ) : ℝ) * B) := by
      refine Finset.sum_le_sum (fun u hu => ?_)
      have hd0 : 0 ≤ (d u : ℝ) := by exact_mod_cast (hd_nonneg u)
      have hb : |Real.log ‖u‖| ≤ B := hlogB u hu
      calc
        |((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖| = (d u : ℝ) * |Real.log ‖(0 : ℂ) - u‖| := by
          rw [abs_mul, abs_of_nonneg hd0]
        _ = (d u : ℝ) * |Real.log ‖u‖| := by rw [hnorm_fac u hu]
        _ ≤ (d u : ℝ) * B := mul_le_mul_of_nonneg_left hb hd0
    have h3 : (∑ u ∈ S, (((d u : ℤ) : ℝ) * B)) = (∑ u ∈ S, ((d u : ℤ) : ℝ)) * B := by
      rw [Finset.sum_mul]
    linarith
  have hfin_eq : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) = ∑ u ∈ S, ((d u : ℤ) : ℝ) := by
    refine finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℝ)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      exact hu (by simp [hd0])
    exact (hmemS u).mpr hdne
  calc
    |Real.log ‖pfP N χ T 0‖|
        = |Real.log ‖∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (d u)‖| := by
            dsimp only [pfP]
    _ = |Real.log ‖∏ u ∈ S, ((0 : ℂ) - u) ^ (d u)‖| := by rw [hprod_eq]
    _ = |Real.log (∏ u ∈ S, ‖((0 : ℂ) - u) ^ (d u)‖)| := by
            rw [pf_norm_finset_prod S (fun u => ((0 : ℂ) - u) ^ (d u))]
    _ = |∑ u ∈ S, Real.log ‖((0 : ℂ) - u) ^ (d u)‖| := by
            rw [Real.log_prod]
            intro u hu
            exact (hpos_fac u hu).ne'
    _ = |∑ u ∈ S, ((d u : ℤ) : ℝ) * Real.log ‖(0 : ℂ) - u‖| := by
            congr 1
            apply Finset.sum_congr rfl
            intro u hu
            have hp0 : 0 < ‖(0 : ℂ) - u‖ := by
              rw [hnorm_fac u hu]
              exact lt_of_lt_of_le hδ₀pos (hdist0 u hu).1
            have hlog : Real.log (‖(0 : ℂ) - u‖ ^ (d u)) = (d u : ℝ) * Real.log ‖(0 : ℂ) - u‖ :=
              pf_log_zpow hp0 (hd_nonneg u)
            rw [pf_norm_zpow_eq ((0 : ℂ) - u) (d u), hlog]
    _ ≤ (∑ u ∈ S, ((d u : ℤ) : ℝ)) * B := hlogS
    _ = (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) * B := by rw [hfin_eq]
    _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (closedBall (0 : ℂ) T)) u : ℤ) : ℝ)) * (Real.log T + |Real.log δ₀|) := by
            dsimp only [B]

/-- Cofactor at a good radius: bounds log‖g‖ on the ball by M0. -/
lemma pf_cofactor_logbound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {A T : ℝ} (hA0 : 0 ≤ A) (hA1 : 1 ≤ A)
    (hTpos : 0 < T) (hT2 : 2 ≤ T) (hT2A : T ≤ 2 * A)
    (hmargin : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 →
      (L_N N A) ^ 2 * |‖u‖ - T| ≥ 1)
    (zc gc : ℝ) (hzc_nonneg : 0 ≤ zc) (hgc_nonneg : 0 ≤ gc)
    (hzc : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℝ)) ≤ zc * R * L_N N R)
    (hgc : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖DirichletCharacter.completedLFunction χ z‖ ≤
        Real.exp (gc * R * L_N N R))
    (δ₀ : ℝ) (hδ₀pos : 0 < δ₀)
    (hLgeD : |Real.log δ₀| ≤ L_N N A)
    (hδ₀ : ∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 → δ₀ ≤ ‖u‖) :
    ∃ (g : ℂ → ℂ) (M0 : ℝ), 0 ≤ M0 ∧
      AnalyticOnNhd ℂ g (ball 0 T) ∧
      (∀ w : ℂ, w ∈ ball 0 T → g w ≠ 0) ∧
      (∀ z : ℂ, z ∈ ball 0 T → DirichletCharacter.completedLFunction χ z =
        pfP N χ T z * g z) ∧
      (∃ ε : ℝ, 0 < ε ∧ AnalyticOnNhd ℂ g (ball 0 (T + ε)) ∧
        (∀ z : ℂ, z ∈ ball 0 (T + ε) → DirichletCharacter.completedLFunction χ z =
          pfP N χ T z * g z)) ∧
      (∀ w : ℂ, w ∈ ball 0 T → Real.log ‖g w‖ ≤ M0) ∧
      |Real.log ‖g 0‖| ≤ M0 ∧
      M0 ≤ (4 * gc + 20 * zc + |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| + 1) *
        (A * (L_N N A) ^ 2 + 1) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛ0 : Λ 0 ≠ 0 := by simpa [Λ] using (completedLFunction_zero_ne_zero χ hχ hχprim)
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using (differentiable_completedLFunction hχ)
  have hcirc : ∀ u : ℂ, ‖u‖ = T → Λ u ≠ 0 := by
    intro u hu hz
    have hmm := hmargin u (by simpa [Λ] using hz)
    have hL : 0 < (L_N N A) ^ 2 := by
      have hLpos : 0 < L_N N A := pf_L_pos (N := N) hA0
      positivity
    have hzero : |‖u‖ - T| = 0 := by simp [hu]
    have hb : (1 : ℝ) ≤ 0 := by simpa [hzero, mul_zero] using hmm
    linarith
  rcases factorization_open (f := Λ) (R := T) hTpos hΛdiff hΛ0 hcirc with ⟨g, ε, hε, hg_an, hg_nz, hfac⟩
  have hg_an_T : AnalyticOnNhd ℂ g (ball 0 T) := by
    intro w hw
    have hwT : ‖w‖ < T := by simpa [mem_ball_zero_iff] using hw
    have hw' : ‖w‖ < T + ε := by linarith [hε]
    exact hg_an w (by simpa [mem_ball_zero_iff] using hw')
  have hg_nz_T : ∀ w : ℂ, w ∈ ball 0 T → g w ≠ 0 := by
    intro w hw
    have hwT : ‖w‖ < T := by simpa [mem_ball_zero_iff] using hw
    have hw' : ‖w‖ < T + ε := by linarith [hε]
    exact hg_nz w (by simpa [mem_ball_zero_iff] using hw')
  have hfac_T : ∀ z : ℂ, z ∈ ball 0 T → Λ z = pfP N χ T z * g z := by
    intro z hz
    have hzT : ‖z‖ < T := by simpa [mem_ball_zero_iff] using hz
    have hz' : ‖z‖ < T + ε := by linarith [hε]
    have hfac' := hfac z (by simpa [mem_ball_zero_iff] using hz')
    dsimp [pfP]
    simpa [Λ] using hfac'
  let L : ℝ := L_N N A
  let LT : ℝ := L_N N T
  let ZT : ℝ := pfZ N χ T
  let Q1 : ℝ := gc * T * LT
  let Q2 : ℝ := (2 * Real.log L) * (zc * T * LT)
  let Q3 : ℝ := |Real.log ‖Λ 0‖|
  let Q4 : ℝ := (zc * T * LT) * (Real.log T + |Real.log δ₀|)
  let M0 : ℝ := Q1 + Q2 + Q3 + Q4 + 1
  have hLT : 0 ≤ LT := le_of_lt (pf_L_pos (N := N) (le_of_lt hTpos))
  have hLTpos : 0 < LT := pf_L_pos (N := N) (le_of_lt hTpos)
  have hL2 : 2 ≤ L := pf_L_ge_two (N := N) hA0
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogδ0 : 0 ≤ |Real.log δ₀| := abs_nonneg _
  have hTge0 : 0 ≤ T := le_of_lt hTpos
  have hQ1 : 0 ≤ Q1 := by dsimp [Q1]; positivity
  have hQ2 : 0 ≤ Q2 := by dsimp [Q2]; positivity
  have hQ3 : 0 ≤ Q3 := by dsimp [Q3]; positivity
  have hQ4 : 0 ≤ Q4 := by
    dsimp [Q4]
    have h1 : 0 ≤ Real.log T + |Real.log δ₀| := by linarith
    positivity
  have hM0_nonneg : 0 ≤ M0 := by dsimp [M0]; linarith
  -- boundary log-bound
  have hboundary : ∀ ζ : ℂ, ‖ζ‖ = T → Real.log ‖g ζ‖ ≤ Q1 + Q2 := by
    intro ζ hζ
    have hΛζ : Λ ζ ≠ 0 := hcirc ζ hζ
    have hPζ : pfP N χ T ζ ≠ 0 := pf_P_ne_zero_circle χ hχ hχprim hTpos hcirc hζ
    have hζε : ζ ∈ ball (0 : ℂ) (T + ε) := by
      rw [mem_ball_zero_iff]
      nlinarith [hζ, hε]
    have hgζ : g ζ ≠ 0 := hg_nz ζ hζε
    have hfacζ : Λ ζ = pfP N χ T ζ * g ζ := by
      have hfac' := hfac ζ hζε
      dsimp [pfP]
      simpa [Λ] using hfac'
    have hlog_mul : Real.log ‖Λ ζ‖ = Real.log ‖pfP N χ T ζ‖ + Real.log ‖g ζ‖ := by
      calc
        Real.log ‖Λ ζ‖ = Real.log ‖pfP N χ T ζ * g ζ‖ := by rw [hfacζ]
        _ = Real.log ‖pfP N χ T ζ‖ + Real.log ‖g ζ‖ := pf_log_eq_of_mul hPζ hgζ
    have hlogΛ := pf_LogΛ_bound (χ := χ) hT2 hgc hζ hΛζ
    have hfaclow := pf_fac_log_lower (χ := χ) (hχ := hχ) (A := A) (T := T) hA0 hTpos
      (by intro u hu; simpa [Λ] using (hmargin u hu)) hζ
    have hZle : pfZ N χ T ≤ zc * T * LT := by
      have h := hzc T hT2
      simpa [pfZ, LT, Λ] using h
    have hQ2le : (2 * Real.log L) * (zc * T * LT) ≥ (2 * Real.log L) * pfZ N χ T := by
      exact mul_le_mul_of_nonneg_left hZle (by positivity)
    have hstep1 : Real.log ‖g ζ‖ = Real.log ‖Λ ζ‖ - Real.log ‖pfP N χ T ζ‖ := by
      rw [hlog_mul]
      ring
    have hneg : -Real.log ‖pfP N χ T ζ‖ ≤ (2 * Real.log L) * pfZ N χ T := by
      simpa [pfZ, pfP, ZT] using hfaclow
    have hmain : Real.log ‖g ζ‖ ≤ Q1 + Q2 := by
      calc
        Real.log ‖g ζ‖ = Real.log ‖Λ ζ‖ - Real.log ‖pfP N χ T ζ‖ := hstep1
        _ ≤ gc * T * LT + (2 * Real.log L) * pfZ N χ T := by
            have h1 : Real.log ‖Λ ζ‖ ≤ gc * T * LT := by simpa [LT] using hlogΛ
            have h2 : -Real.log ‖pfP N χ T ζ‖ ≤ (2 * Real.log L) * pfZ N χ T := by
              simpa [pfZ, pfP, ZT] using hfaclow
            linarith
        _ ≤ gc * T * LT + (2 * Real.log L) * (zc * T * LT) := by
            have := add_le_add_left hQ2le (gc * T * LT)
            linarith
        _ = Q1 + Q2 := by dsimp only [Q1, Q2, LT]
    exact hmain
  -- ball bound via max modulus
  have hball : ∀ w : ℂ, w ∈ ball 0 T → Real.log ‖g w‖ ≤ M0 := by
    intro w hw
    have hg_cont : DiffContOnCl ℂ g (ball (0 : ℂ) T) := by
      refine DifferentiableOn.diffContOnCl ?_
      have hcl : DifferentiableOn ℂ g (Metric.closedBall 0 T) := by
        intro x hx
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        have hx' : x ∈ ball 0 (T + ε) := by
          rw [mem_ball_zero_iff]
          have hxT : ‖x‖ ≤ T := by simpa using hx
          nlinarith [hε]
        exact (hg_an.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hx')).differentiableWithinAt
      simpa [closure_ball (0 : ℂ) (ne_of_gt hTpos)] using hcl
    have hfront : ∀ ζ : ℂ, ζ ∈ frontier (ball (0 : ℂ) T) → ‖g ζ‖ ≤ Real.exp M0 := by
      intro ζ hζf
      rw [frontier_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_sphere, dist_eq_norm] at hζf
      have hζ : ‖ζ‖ = T := by simpa using hζf
      have hb := hboundary ζ hζ
      have hζε' : ζ ∈ ball 0 (T + ε) := by
        rw [mem_ball_zero_iff]
        nlinarith [hζ, hε]
      have hg0 : ‖g ζ‖ ≠ 0 := norm_ne_zero_iff.mpr (hg_nz ζ hζε')
      have hle : Real.log ‖g ζ‖ ≤ M0 := by
        have hQ12le : Q1 + Q2 ≤ M0 := by
          dsimp [M0]
          linarith [hQ3, hQ4]
        linarith
      exact le_trans (le_of_eq (Real.exp_log (norm_pos_iff.mpr (hg_nz ζ hζε'))).symm)
        (Real.exp_le_exp.mpr hle)
    have hcl : w ∈ closure (ball (0 : ℂ) T) := by
      rw [closure_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_closedBall, dist_eq_norm]
      have hw' : ‖w‖ < T := by simpa [mem_ball_zero_iff] using hw
      simpa using le_of_lt hw'
    have hnorm : ‖g w‖ ≤ Real.exp M0 := Complex.norm_le_of_forall_mem_frontier_norm_le
      (isBounded_ball (x := (0 : ℂ)) (r := T)) hg_cont hfront hcl
    have hpos : 0 < ‖g w‖ := norm_pos_iff.mpr (hg_nz_T w hw)
    have hle : Real.log ‖g w‖ ≤ Real.log (Real.exp M0) := Real.log_le_log hpos hnorm
    rwa [Real.log_exp] at hle
  -- origin bound
  have horigin : |Real.log ‖g 0‖| ≤ M0 := by
    have h0T : (0 : ℂ) ∈ ball 0 T := by
      rw [mem_ball_zero_iff]
      simpa using hTpos
    have hfac0 := hfac_T 0 h0T
    have hP0 : pfP N χ T 0 ≠ 0 := by
      have hmul : pfP N χ T 0 * g 0 ≠ 0 := by simpa [hfac0] using hΛ0
      exact (mul_ne_zero_iff.mp hmul).1
    have hg0nz : g 0 ≠ 0 := hg_nz_T 0 h0T
    have hlog_mul0 : Real.log ‖Λ 0‖ = Real.log ‖pfP N χ T 0‖ + Real.log ‖g 0‖ := by
      calc
        Real.log ‖Λ 0‖ = Real.log ‖pfP N χ T 0 * g 0‖ := by rw [hfac0]
        _ = Real.log ‖pfP N χ T 0‖ + Real.log ‖g 0‖ := pf_log_eq_of_mul hP0 hg0nz
    -- bound |log‖P0‖| ≤ Q4-ish
    have hP0_bound : |Real.log ‖pfP N χ T 0‖| ≤ (zc * T * LT) * (Real.log T + |Real.log δ₀|) := by
      have h1 := pf_P0_log_bound_p3 χ hχ (hT := le_trans (by norm_num) hT2) (δ₀ := δ₀) hδ₀pos hδ₀
      have hZle : pfZ N χ T ≤ zc * T * LT := by
        have h := hzc T hT2
        simpa [pfZ, LT, Λ] using h
      have hfac2 : (pfZ N χ T) * (Real.log T + |Real.log δ₀|) ≤ (zc * T * LT) * (Real.log T + |Real.log δ₀|) := by
        have hb : 0 ≤ Real.log T + |Real.log δ₀| := by linarith [hlogT, hlogδ0]
        exact mul_le_mul_of_nonneg_right hZle hb
      have h1' : |Real.log ‖pfP N χ T 0‖| ≤ (pfZ N χ T) * (Real.log T + |Real.log δ₀|) := by
        simpa [pfZ] using h1
      linarith [h1', hfac2]
    have hlogg0 : |Real.log ‖g 0‖| ≤ Q3 + Q4 := by
      have h1 : |Real.log ‖Λ 0‖ - Real.log ‖pfP N χ T 0‖| ≤ Q3 + (zc * T * LT) * (Real.log T + |Real.log δ₀|) := by
        have hA : |Real.log ‖Λ 0‖ - Real.log ‖pfP N χ T 0‖| ≤ |Real.log ‖Λ 0‖| + |Real.log ‖pfP N χ T 0‖| := by
          rw [sub_eq_add_neg]
          calc
            |Real.log ‖Λ 0‖ + -Real.log ‖pfP N χ T 0‖| ≤
                |Real.log ‖Λ 0‖| + |(-Real.log ‖pfP N χ T 0‖)| := abs_add_le _ _
            _ = |Real.log ‖Λ 0‖| + |Real.log ‖pfP N χ T 0‖| := by rw [abs_neg]
        linarith [hA, hP0_bound]
      have hrew : Real.log ‖g 0‖ = Real.log ‖Λ 0‖ - Real.log ‖pfP N χ T 0‖ := by
        rw [hlog_mul0]
        ring
      have h2 : |Real.log ‖g 0‖| ≤ Q3 + Q4 := by
        simpa [hrew, Q3, Q4] using h1
      simpa [Q3, Q4] using h2
    have h34 : Q3 + Q4 ≤ M0 := by
      dsimp [M0]
      have hQ1' : 0 ≤ Q1 := hQ1
      have hQ2' : 0 ≤ Q2 := hQ2
      nlinarith
    have hg0ball : Real.log ‖g 0‖ ≤ M0 := hball 0 h0T
    have h1 : Real.log ‖g 0‖ ≤ M0 := hg0ball
    have h2 : -M0 ≤ Real.log ‖g 0‖ := by
      have hle' : |Real.log ‖g 0‖| ≤ M0 := le_trans hlogg0 h34
      have habs := abs_le.mp hle'
      linarith
    exact abs_le.mpr ⟨h2, h1⟩
  have hM0_bound : M0 ≤ (4 * gc + 20 * zc + |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| + 1) *
      (A * (L_N N A) ^ 2 + 1) := by
    have hL1 : 1 ≤ L := by linarith [pf_L_ge_two (N := N) hA0]
    have hLpos2 : 0 < L := lt_of_lt_of_le (by norm_num) hL1
    have hLT2 : LT ≤ 2 * L := by
      have hmono : L_N N T ≤ L_N N (2 * A) := pf_L_mono (N := N) hTpos.le hT2A
      have h2 : L_N N (2 * A) ≤ 2 * L_N N A := pf_L_two_mul_le (N := N) hA1
      dsimp only [LT, L]
      linarith
    have hLTpos : 0 ≤ LT := hLT
    have hlogT_le_LT : Real.log T ≤ LT := by
      have h1 : Real.log T ≤ Real.log (T + 2) := Real.log_le_log hTpos (by linarith)
      have h2 : 0 ≤ Real.log (N : ℝ) := logN_nonneg (N := N)
      dsimp only [LT, L_N]
      linarith
    have hlogT_le : Real.log T ≤ 2 * L := le_trans hlogT_le_LT (le_trans hLT2 (by linarith))
    have hQ1le : Q1 ≤ 4 * gc * A * L ^ 2 := by
      have h1 : T ≤ 2 * A := hT2A
      have h2 : gc * T * LT ≤ gc * (2 * A) * (2 * L) := by
        have hT0 : 0 ≤ T := hTpos.le
        have h3 : T * LT ≤ (2 * A) * (2 * L) := by nlinarith
        have h3' := mul_le_mul_of_nonneg_left h3 hgc_nonneg
        nlinarith [h3']
      have h4 : gc * (2 * A) * (2 * L) ≤ 4 * gc * A * L ^ 2 := by nlinarith
      dsimp only [Q1]
      linarith
    have hQ2le : Q2 ≤ 8 * zc * A * L ^ 2 := by
      have hlogL : Real.log L ≤ L := Real.log_le_self (by linarith)
      have h3 : T * LT ≤ (2 * A) * (2 * L) := by
        have hT0 : 0 ≤ T := hTpos.le
        nlinarith
      have hz : zc * (T * LT) ≤ zc * ((2 * A) * (2 * L)) :=
        mul_le_mul_of_nonneg_left h3 hzc_nonneg
      have h4 : (2 * Real.log L) * (zc * T * LT) ≤ (2 * L) * (zc * (2 * A) * (2 * L)) := by
        have h5 : 2 * Real.log L ≤ 2 * L := by linarith
        have h6 : 0 ≤ zc * T * LT := by positivity
        have : (2 * Real.log L) * (zc * T * LT) ≤ (2 * L) * (zc * T * LT) :=
          mul_le_mul_of_nonneg_right h5 h6
        have h7 : (2 * L) * (zc * T * LT) ≤ (2 * L) * (zc * (2 * A) * (2 * L)) := by
          have h8 : 0 ≤ 2 * L := by linarith
          have h9 : zc * T * LT ≤ zc * ((2 * A) * (2 * L)) := by
            have : T * LT ≤ (2 * A) * (2 * L) := h3
            nlinarith
          have h9' := mul_le_mul_of_nonneg_left h9 h8
          nlinarith [h9']
        linarith
      have h10 : (2 * L) * (zc * (2 * A) * (2 * L)) ≤ 8 * zc * A * L ^ 2 := by nlinarith
      dsimp only [Q2]
      linarith
    have hQ3le : Q3 ≤ (|Real.log ‖Λ 0‖|) * (A * L ^ 2 + 1) := by
      have h1 : 1 ≤ A * L ^ 2 + 1 := by nlinarith
      dsimp only [Q3]
      nlinarith [abs_nonneg (Real.log ‖Λ 0‖)]
    have hQ4le : Q4 ≤ 12 * zc * A * L ^ 2 := by
      have h3 : T * LT ≤ (2 * A) * (2 * L) := by
        have hT0 : 0 ≤ T := hTpos.le
        nlinarith
      have hz : zc * T * LT ≤ zc * ((2 * A) * (2 * L)) := by
        have : T * LT ≤ (2 * A) * (2 * L) := h3
        nlinarith
      have hB : Real.log T + |Real.log δ₀| ≤ 2 * L + L := by linarith
      have h4 : (zc * T * LT) * (Real.log T + |Real.log δ₀|) ≤
          (zc * ((2 * A) * (2 * L))) * (2 * L + L) := by
        have h5 : 0 ≤ Real.log T + |Real.log δ₀| := by linarith [hlogT, hlogδ0]
        exact mul_le_mul hz hB h5 (by positivity)
      have h6 : (zc * ((2 * A) * (2 * L))) * (2 * L + L) ≤ 12 * zc * A * L ^ 2 := by nlinarith
      dsimp only [Q4]
      linarith
    dsimp only [M0]
    nlinarith [hQ1le, hQ2le, hQ3le, hQ4le, abs_nonneg (Real.log ‖Λ 0‖)]
  have hfacs : ∃ ε : ℝ, 0 < ε ∧ AnalyticOnNhd ℂ g (ball 0 (T + ε)) ∧
      (∀ z : ℂ, z ∈ ball 0 (T + ε) → DirichletCharacter.completedLFunction χ z =
        pfP N χ T z * g z) := by
    refine ⟨ε, hε, hg_an, ?_⟩
    intro z hz
    have hfac' := hfac z hz
    dsimp [pfP]
    simpa [Λ] using hfac'
  exact ⟨g, M0, hM0_nonneg, hg_an_T, hg_nz_T, hfac_T, hfacs, hball, horigin, hM0_bound⟩




/-- log-derivative of the completed L-function. -/
def pfLD (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (z : ℂ) : ℂ :=
  deriv (DirichletCharacter.completedLFunction χ) z / DirichletCharacter.completedLFunction χ z

/-- the partial fraction sum at radius T. -/
def pfSum (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) (s : ℂ) : ℂ :=
  ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (closedBall (0 : ℂ) T)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)

lemma pf_perterm {u s : ℂ} (d : ℤ) :
    ((d : ℂ) * (1 / (s - u) - 1 / ((0 : ℂ) - u))) = (d : ℂ) * (1 / (s - u) + 1 / u) := by
  have h : (0 : ℂ) - u = -u := by ring
  rw [h, div_neg]
  ring

/-- The main defect estimate: the partial fraction sum is close to the log-derivative difference. -/
lemma pf_defect_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A₁ : ℝ, ∀ A : ℝ, A₁ ≤ A → ∀ T : ℝ, A ≤ T → T ≤ 2 * A →
      (∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 →
        (L_N N A) ^ 2 * |‖u‖ - T| ≥ 1) → ∀ s : ℂ,
      DirichletCharacter.completedLFunction χ s ≠ 0 → 8 * ‖s‖ ≤ T →
      ‖pfSum N χ T s - (pfLD N χ s - pfLD N χ 0)‖ ≤ C * (L_N N A) ^ 2 / A * ‖s‖ := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  rcases pf_zeros_ge_delta χ hχ hχprim with ⟨δ₀, hδ₀pos, hδ₀le1, hδ₀⟩
  rcases completedL_zeroCount χ hχ hχprim with ⟨zc0, hzc0⟩
  rcases completedL_growth_circle χ hχ hχprim with ⟨gc0, hgc0⟩
  let zc : ℝ := max zc0 0
  let gc : ℝ := max gc0 0
  have hzcnn : 0 ≤ zc := le_max_right _ _
  have hgcnn : 0 ≤ gc := le_max_right _ _
  have hzc : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℝ)) ≤ zc * R * L_N N R := by
    intro R hR
    have h := hzc0 R hR
    have hle : zc0 ≤ zc := le_max_left _ _
    have hL0 : 0 ≤ L_N N R := le_of_lt (pf_L_pos (N := N) (by linarith))
    have hR0 : 0 ≤ R := by linarith
    calc
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℝ)) ≤ zc0 * R * L_N N R := h
      _ ≤ zc * R * L_N N R := by
        have h1 : zc0 * (R * L_N N R) ≤ zc * (R * L_N N R) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
        nlinarith [h1]
  have hgc : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖DirichletCharacter.completedLFunction χ z‖ ≤ Real.exp (gc * R * L_N N R) := by
    intro R hR z hz
    have h := hgc0 R hR z hz
    refine le_trans h (Real.exp_le_exp.mpr ?_)
    have hle : gc0 ≤ gc := le_max_left _ _
    have hL0 : 0 ≤ L_N N R := le_of_lt (pf_L_pos (N := N) (by linarith))
    have hR0 : 0 ≤ R := by linarith
    have hRL : 0 ≤ R * L_N N R := mul_nonneg hR0 hL0
    have h2 : gc0 * (R * L_N N R) ≤ gc * (R * L_N N R) := mul_le_mul_of_nonneg_right hle hRL
    calc
      gc0 * R * L_N N R = gc0 * (R * L_N N R) := by ring
      _ ≤ gc * (R * L_N N R) := h2
      _ = gc * R * L_N N R := by ring
  let C : ℝ := 4096 * (4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1)
  have hCnn : 0 ≤ C := by
    dsimp [C]
    have h1 : 0 ≤ 4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1 := by positivity
    positivity
  refine ⟨C, hCnn, max (Real.exp |Real.log δ₀|) 2, ?_⟩
  intro A hA T hAT hT2A hmargin s hΛs hsT
  have hA2 : 2 ≤ A := le_trans (le_max_right _ _) hA
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hTpos : 0 < T := by linarith
  have hT2 : 2 ≤ T := by linarith
  have hLgeD : |Real.log δ₀| ≤ L_N N A := by
    have hexp : Real.exp |Real.log δ₀| ≤ A := le_trans (le_max_left _ _) hA
    have h1 : |Real.log δ₀| ≤ Real.log A := by
      have h := Real.log_le_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at h
    have h2 : Real.log A ≤ L_N N A := by
      dsimp [L_N]
      have h3 : Real.log A ≤ Real.log (A + 2) := Real.log_le_log (by linarith) (by linarith)
      have h4 : 0 ≤ Real.log (N : ℝ) := logN_nonneg (N := N)
      linarith
    linarith
  rcases pf_cofactor_logbound χ hχ hχprim hA0 hA1 hTpos hT2 hT2A hmargin zc gc hzcnn hgcnn
    hzc hgc δ₀ hδ₀pos hLgeD hδ₀ with
    ⟨g, M0, hM0nn, hg_an, hg_ne, _hfac_T, hfacs, hball, horigin, hM0le⟩
  rcases hfacs with ⟨ε, hε, hg_an_ε, hfac_ε⟩
  -- generic log-derivative difference bound
  have hsT8 : ‖s‖ ≤ T / 8 := by linarith
  have hsub := pf_logDeriv_sub_of_sup (g := g) (R := T) (M0 := M0) hTpos hg_an hg_ne
    hM0nn hball horigin hsT8
  -- decomposition at s and at 0
  have hΛ0 : Λ 0 ≠ 0 := by simpa [Λ] using (completedLFunction_zero_ne_zero χ hχ hχprim)
  have hs_ball : s ∈ ball (0 : ℂ) (T + ε) := by
    rw [mem_ball_zero_iff]
    nlinarith [hsT, hε, hTpos]
  have h0_ball : (0 : ℂ) ∈ ball (0 : ℂ) (T + ε) := by
    rw [mem_ball_zero_iff]
    simpa using (by linarith [hTpos, hε] : (0 : ℝ) < T + ε)
  have hs_ballT : s ∈ ball (0 : ℂ) T := by
    rw [mem_ball_zero_iff]
    linarith [hsT, hTpos]
  have h0_ballT : (0 : ℂ) ∈ ball (0 : ℂ) T := by
    rw [mem_ball_zero_iff]
    simpa using hTpos
  have hgs : g s ≠ 0 := hg_ne s hs_ballT
  have hg0 : g 0 ≠ 0 := hg_ne 0 h0_ballT
  have hgdiff_s : DifferentiableAt ℂ g s :=
    hg_an_ε.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hs_ball)
  have hgdiff_0 : DifferentiableAt ℂ g 0 :=
    hg_an_ε.differentiableOn.differentiableAt (isOpen_ball.mem_nhds h0_ball)
  have hfac_eps : ∀ z : ℂ, z ∈ ball (0 : ℂ) (T + ε) →
      Λ z = (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T) u)) * g z := by
    intro z hz
    have h := hfac_ε z hz
    dsimp [pfP] at h
    simpa [Λ] using h
  have hdec_s := logDeriv_decompose (f := Λ) (g := g) (R := T) (ε := ε)
    (by simpa [Λ] using differentiable_completedLFunction hχ) hfac_eps hs_ball (by simpa [Λ] using hΛs)
    hgdiff_s hgs
  have hdec_0 := logDeriv_decompose (f := Λ) (g := g) (R := T) (ε := ε)
    (by simpa [Λ] using differentiable_completedLFunction hχ) hfac_eps h0_ball (by simpa [Λ] using hΛ0)
    hgdiff_0 hg0
  -- the finsum difference
  have hsupp : (Function.support (fun u : ℂ =>
      MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T) u)).Finite := pf_divisor_support_finite χ hχ T
  have hfin_sub := finsum_sub_div_one_sub (d := fun u : ℂ =>
      MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T) u) hsupp s 0
  have hper : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)) u : ℤ) : ℂ) *
      (1 / (s - u) - 1 / ((0 : ℂ) - u))) = pfSum N χ T s := by
    congr 1
    funext u
    have h := pf_perterm (u := u) (s := s) ((MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)) u)
    simpa [pfSum, Λ] using h
  have hsum_eq : ((∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)) u : ℤ) : ℂ) * (1 / (s - u))) -
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)) u : ℤ) : ℂ) * (1 / ((0 : ℂ) - u)))) =
      pfSum N χ T s := by
    rw [hfin_sub]
    exact hper
  -- defect identity
  have hdefect : pfSum N χ T s - (pfLD N χ s - pfLD N χ 0) =
      -(logDeriv g s - logDeriv g 0) := by
    have hs_dec : pfLD N χ s = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)) u : ℤ) : ℂ) * (1 / (s - u))) + logDeriv g s := by
      simpa [pfLD, logDeriv_apply, Λ] using hdec_s
    have h0_dec : pfLD N χ 0 = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)) u : ℤ) : ℂ) * (1 / ((0 : ℂ) - u))) + logDeriv g 0 := by
      simpa [pfLD, logDeriv_apply, Λ] using hdec_0
    rw [hs_dec, h0_dec, ← hsum_eq]
    ring
  -- norm bound
  have hg_bound : ‖logDeriv g s - logDeriv g 0‖ ≤ 1024 * max M0 1 * ‖s‖ / T ^ 2 := hsub
  have hC0nn : 0 ≤ 4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 := by positivity
  have hL2 : 2 ≤ L_N N A := pf_L_ge_two (N := N) hA0
  have hAL_ge : 1 ≤ A * (L_N N A) ^ 2 := by
    have h1 : 1 ≤ A := hA1
    nlinarith
  have hmaxM0 : max M0 1 ≤ (4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (A * (L_N N A) ^ 2 + 1) := by
    have hM0bound : M0 ≤ (4 * gc + 20 * zc + |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| + 1) *
        (A * (L_N N A) ^ 2 + 1) := by simpa [Λ] using hM0le
    have h1 : 1 ≤ (A * (L_N N A) ^ 2 + 1) := by nlinarith
    have h2 : 0 ≤ 4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 := hC0nn
    have h3 : (4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1) * (A * (L_N N A) ^ 2 + 1) ≤
        (4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (A * (L_N N A) ^ 2 + 1) := by
      have : 4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 ≤ 4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1 := by linarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have h4 : max M0 1 ≤ max ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1) * (A * (L_N N A) ^ 2 + 1)) 1 :=
      max_le_max hM0bound le_rfl
    have h5 : max ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1) * (A * (L_N N A) ^ 2 + 1)) 1 ≤
        (4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (A * (L_N N A) ^ 2 + 1) := by
      apply max_le
      · linarith [h3]
      · linarith
    linarith
  have hfinal : 1024 * max M0 1 * ‖s‖ / T ^ 2 ≤ C * (L_N N A) ^ 2 / A * ‖s‖ := by
    have hT0 : 0 < T := hTpos
    have hA0' : 0 < A := by linarith
    have hL0 : 0 ≤ (L_N N A) ^ 2 := by positivity
    have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
    have hstep : 1024 * max M0 1 * ‖s‖ / T ^ 2 ≤
        1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (A * (L_N N A) ^ 2 + 1)) * ‖s‖ / T ^ 2 := by
      have h1 : 1024 * max M0 1 ≤ 1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (A * (L_N N A) ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left hmaxM0 (by norm_num)
      have h2 : 0 ≤ ‖s‖ := hs0
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) (by positivity)
    have hT2' : A ^ 2 ≤ T ^ 2 := by nlinarith
    have hnum : (A * (L_N N A) ^ 2 + 1) ≤ 2 * (A * (L_N N A) ^ 2) := by nlinarith [hAL_ge]
    have hexp : 1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (A * (L_N N A) ^ 2 + 1)) * ‖s‖ / T ^ 2 ≤
        1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (2 * (A * (L_N N A) ^ 2))) * ‖s‖ / A ^ 2 := by
      have h1 : 0 ≤ 1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1)) * ‖s‖ * (1 + 0) := by positivity
      calc
        1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (A * (L_N N A) ^ 2 + 1)) * ‖s‖ / T ^ 2
            ≤ 1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (2 * (A * (L_N N A) ^ 2))) * ‖s‖ / T ^ 2 := by
              have hfac : (A * (L_N N A) ^ 2 + 1) ≤ 2 * (A * (L_N N A) ^ 2) := hnum
              have hfac2 : (4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (A * (L_N N A) ^ 2 + 1) ≤
                  (4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (2 * (A * (L_N N A) ^ 2)) :=
                mul_le_mul_of_nonneg_left hfac (by linarith [hC0nn])
              have hfac3 : 1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (A * (L_N N A) ^ 2 + 1)) ≤
                  1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (2 * (A * (L_N N A) ^ 2))) :=
                mul_le_mul_of_nonneg_left hfac2 (by norm_num)
              gcongr
        _ ≤ 1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (2 * (A * (L_N N A) ^ 2))) * ‖s‖ / A ^ 2 := by
              have hpos : 0 ≤ 1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (2 * (A * (L_N N A) ^ 2))) * ‖s‖ := by positivity
              exact div_le_div_of_nonneg_left hpos (by positivity) hT2'
    have hle' : 1024 * ((4 * gc + 20 * zc + |Real.log ‖Λ 0‖| + 1 + 1) * (2 * (A * (L_N N A) ^ 2))) * ‖s‖ / A ^ 2 ≤
        C * (L_N N A) ^ 2 / A * ‖s‖ := by
      dsimp [C]
      have hAne : A ≠ 0 := ne_of_gt hA0'
      field_simp
      nlinarith [hs0, hL0, sq_nonneg (L_N N A), abs_nonneg (Real.log ‖Λ 0‖)]
    linarith [hstep, hexp, hle']
  calc
    ‖pfSum N χ T s - (pfLD N χ s - pfLD N χ 0)‖ = ‖logDeriv g s - logDeriv g 0‖ := by
      rw [hdefect, norm_neg]
    _ ≤ 1024 * max M0 1 * ‖s‖ / T ^ 2 := hg_bound
    _ ≤ C * (L_N N A) ^ 2 / A * ‖s‖ := hfinal

/-- **Final assembly**: the log-derivative partial-fraction identity for the completed
Dirichlet L-function. -/
theorem logDeriv_pf_identity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ B : ℂ, ∀ s : ℂ,
      DirichletCharacter.completedLFunction χ s ≠ 0 →
      Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)))
        atTop (𝓝 (deriv (DirichletCharacter.completedLFunction χ) s /
          DirichletCharacter.completedLFunction χ s - B)) := by
  classical
  refine ⟨deriv (DirichletCharacter.completedLFunction χ) 0 /
    DirichletCharacter.completedLFunction χ 0, ?_⟩
  intro s hΛs
  rcases pf_defect_bound χ hχ hχprim with ⟨C, hCnn, A₁, hbound⟩
  rcases goodRadius_geometric χ hχ hχprim with ⟨Ag, _hAgpos, hgr⟩
  rcases partialFraction_conv χ hχ hχprim s with ⟨L, hL⟩
  let A₀ : ℝ := max (max A₁ Ag) (8 * ‖s‖ + 1)
  have hA₁_le : A₁ ≤ A₀ := le_trans (le_max_left A₁ Ag) (le_max_left _ _)
  have hAg_le : Ag ≤ A₀ := le_trans (le_max_right A₁ Ag) (le_max_left _ _)
  have hs_le_A₀ : 8 * ‖s‖ + 1 ≤ A₀ := le_max_right _ _
  let gr : ℝ → ℝ := fun A => if h : A₀ ≤ A then (hgr A (le_trans hAg_le h)).choose else 1
  have hgr_spec : ∀ A : ℝ, A₀ ≤ A →
      A ≤ gr A ∧ gr A ≤ 2 * A ∧
        (∀ u : ℂ, DirichletCharacter.completedLFunction χ u = 0 →
          (L_N N A) ^ 2 * |‖u‖ - gr A| ≥ 1) := by
    intro A hA
    dsimp [gr]
    rw [dif_pos hA]
    have h := (hgr A (le_trans hAg_le hA)).choose_spec
    exact h
  have hgr_ge : ∀ A : ℝ, A₀ ≤ A → A ≤ gr A := fun A hA => (hgr_spec A hA).1
  have hgr_top : Tendsto gr atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_ge_atTop A₀] with A hA
    exact hgr_ge A hA
  -- the bound tends to zero
  have hbound_tend : Tendsto (fun A : ℝ => C * (L_N N A) ^ 2 / A * ‖s‖) atTop (𝓝 0) := by
    have h0 := pf_L_sq_div_self_tendsto_zero (N := N)
    have h1 : Tendsto (fun A : ℝ => (C * ‖s‖) * ((L_N N A) ^ 2 / A)) atTop (𝓝 ((C * ‖s‖) * 0)) :=
      tendsto_const_nhds.mul h0
    have h2 : Tendsto (fun A : ℝ => (C * ‖s‖) * ((L_N N A) ^ 2 / A)) atTop (𝓝 0) := by simpa using h1
    refine h2.congr' ?_
    filter_upwards with A
    ring
  -- the approximating sequence converges to the value
  have hmain : Tendsto (fun A : ℝ => pfSum N χ (gr A) s) atTop
      (𝓝 (pfLD N χ s - pfLD N χ 0)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' ?_ ?_ hbound_tend
    · filter_upwards with A
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop A₀] with A hA
      have hspec := hgr_spec A hA
      have hA₁A : A₁ ≤ A := le_trans hA₁_le hA
      have hA0 : 0 ≤ A := le_trans (by positivity : (0:ℝ) ≤ A₀) hA
      have hT8 : 8 * ‖s‖ ≤ gr A := by
        have h1 : 8 * ‖s‖ + 1 ≤ A := le_trans hs_le_A₀ hA
        linarith [hspec.1]
      exact hbound A hA₁A (gr A) hspec.1 hspec.2.1 hspec.2.2 s hΛs hT8
  have hcomp : Tendsto (fun A : ℝ => pfSum N χ (gr A) s) atTop (𝓝 L) := by
    have := hL.comp hgr_top
    simpa [pfSum, Function.comp_def] using this
  have hLeq : L = pfLD N χ s - pfLD N χ 0 := tendsto_nhds_unique hcomp hmain
  rw [hLeq] at hL
  have hfinal : ∀ R : ℝ, (∑ᶠ u : ℂ, (((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
        (1 / (s - u) + 1 / u)) = pfSum N χ R s := fun R => rfl
  simpa [hfinal, pfLD] using hL


end Commons.NumberTheory.Linnik
