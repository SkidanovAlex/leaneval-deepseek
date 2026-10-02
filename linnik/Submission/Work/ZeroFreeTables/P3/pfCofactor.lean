/-
# ZeroFreeTables/P3/pfCofactor

The cofactor log-bound of the partial-fraction identity, `pf_cofactor_logbound`, copied into
this area's namespace.

**Why this file exists.**  The shared library contains *two* files defining the same
declarations in `Commons.NumberTheory.Linnik` — `logDeriv_pf_identity` and
`completedL_pf_identity_rect` (both define `pfP`, `pfZ`, …).  A module importing both fails with
`environment already contains 'Commons.NumberTheory.Linnik.pfP'`.  The round-2 contract
(`Submission.Work.LinnikContract2.Contract`) transitively imports `completedL_pf_identity_rect`
(via `CarryOver` → `LinnikAreas.area5`), and that file is *not* under this area's control, so
the `P₃` engine must not import `logDeriv_pf_identity`.  The only declaration of that file which
the engine needs — `pf_cofactor_logbound` (used by `P3/CompletedDerivPF`) — is therefore
reproduced here on top of `completedL_pf_identity_rect`.  The proof is verbatim the shared
one; all supporting lemmas (`pfP`, `pfZ`, `pf_fac_log_lower`, `pf_LogΛ_bound`,
`pf_P_ne_zero_circle`, `pf_P0_log_bound`, `factorization_open`, …) are the shared ones, which
the two files state identically (up to definitional unfolding of `pfZ`).
-/
import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect

open Complex DirichletCharacter Metric Filter Function Set MeromorphicOn Topology
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

namespace Work.ZeroFreeTables.P3

open Commons.NumberTheory.Linnik

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
      nlinarith only [hζ, hε]
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
        nlinarith only [hζ, hε]
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
      have h1 := pf_P0_log_bound χ hχ (hT := le_trans (by norm_num) hT2) (δ₀ := δ₀) hδ₀pos hδ₀
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
        nlinarith only [h3']
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
          nlinarith only [h9']
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





end Work.ZeroFreeTables.P3
