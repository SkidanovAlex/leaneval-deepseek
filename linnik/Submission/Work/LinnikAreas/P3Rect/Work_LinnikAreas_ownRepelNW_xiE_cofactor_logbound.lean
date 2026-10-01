import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_Defs
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_XiAux
import Submission.Work.LinnikAreas.P3Rect.LogDerivPfIdentityP3
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_ownRepelNW_xiECofactorAuxP0

open scoped Classical BigOperators
open Metric
open Work.LinnikAreas.DhK

noncomputable section

namespace Work.LinnikAreas.ownRepelNW

/-- Log-lower bound for the divisor product of `Ξ` at a point of the circle `‖ζ‖ = T`:
analogue of `Commons.NumberTheory.Linnik.pf_fac_log_lower` with `Λ := Xi`, `L := xiL A`.
(Reproduced here because the sibling module `DhK.XiFacLogLower` is currently not building.) -/
lemma xiE_cofactor_fac_log_lower {A T : ℝ} (hA0 : 0 ≤ A) (hT0 : 0 < T)
    (hmargin : ∀ u : ℂ, Xi u = 0 → (xiL A) ^ 2 * |‖u‖ - T| ≥ 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = T) :
    -Real.log ‖∏ᶠ u : ℂ, (ζ - u) ^
        (MeromorphicOn.divisor Xi (Metric.closedBall (0 : ℂ) T) u)‖ ≤
      (2 * Real.log (xiL A)) *
        (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Xi (Metric.closedBall (0 : ℂ) T)) u : ℝ)) := by
  classical
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor Xi (closedBall (0 : ℂ) T) u
  let L : ℝ := xiL A
  have hLpos : 0 < L := xiL_pos hA0
  have hL2pos : 0 < L ^ 2 := pow_pos hLpos 2
  let m : ℝ := 1 / L ^ 2
  have hmpos : 0 < m := by dsimp [m]; exact div_pos (by norm_num) hL2pos
  have hd_nonneg : ∀ u, 0 ≤ d u := by
    intro u
    dsimp [d]
    exact Xi_divisor_nonneg T u
  have hsupport : (Function.support d).Finite := by
    dsimp [d]
    exact Xi_divisor_support_finite T
  let S : Finset ℂ := hsupport.toFinset
  have hmemS : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hdist : ∀ u : ℂ, u ∈ S → m ≤ ‖ζ - u‖ := by
    intro u hu
    have hdne : d u ≠ 0 := (hmemS u).mp hu
    have hzu : Xi u = 0 := Xi_divisor_ne_zero_is_zero (R := T) (by simpa [d] using hdne)
    have hmarg := hmargin u hzu
    have hmul' : 1 ≤ |‖u‖ - T| * (L ^ 2) := by
      simpa [mul_comm, L] using hmarg
    have hle_m : m ≤ |‖u‖ - T| := (div_le_iff₀ hL2pos).mpr hmul'
    have habs : |‖u‖ - ‖ζ‖| ≤ ‖ζ - u‖ := by
      simpa [abs_sub_comm] using (abs_norm_sub_norm_le ζ u)
    have hrew : |‖u‖ - T| = |‖u‖ - ‖ζ‖| := by rw [hζ]
    exact le_trans hle_m (by rwa [hrew])
  have hprod_pos_fac : ∀ u : ℂ, u ∈ S → 0 < ‖(ζ - u) ^ (d u)‖ := by
    intro u hu
    have hb : 0 < ‖ζ - u‖ := lt_of_lt_of_le hmpos (hdist u hu)
    have hpow : ‖(ζ - u) ^ (d u)‖ = ‖ζ - u‖ ^ (d u) :=
      Commons.NumberTheory.Linnik.pf_norm_zpow_eq (ζ - u) (d u)
    rw [hpow]
    exact Commons.NumberTheory.Linnik.pf_zpow_pos hb (hd_nonneg u)
  have hlog_per : ∀ u : ℂ, u ∈ S →
      -Real.log ‖(ζ - u) ^ (d u)‖ ≤ (d u : ℝ) * (2 * Real.log L) := by
    intro u hu
    have hmle : m ≤ ‖ζ - u‖ := hdist u hu
    have hb : 0 < ‖ζ - u‖ := lt_of_lt_of_le hmpos hmle
    have hpow_le : m ^ (d u) ≤ ‖ζ - u‖ ^ (d u) :=
      Commons.NumberTheory.Linnik.pf_zpow_le_of_le (le_of_lt hmpos) hmle (hd_nonneg u)
    have hnorm : ‖(ζ - u) ^ (d u)‖ = ‖ζ - u‖ ^ (d u) :=
      Commons.NumberTheory.Linnik.pf_norm_zpow_eq (ζ - u) (d u)
    have h1 : 0 < m ^ (d u) := Commons.NumberTheory.Linnik.pf_zpow_pos hmpos (hd_nonneg u)
    have hlog_ge : Real.log (m ^ (d u)) ≤ Real.log ‖(ζ - u) ^ (d u)‖ := by
      rw [hnorm]
      exact Real.log_le_log h1 hpow_le
    have hlogm : Real.log (m ^ (d u)) = (d u : ℝ) * Real.log m :=
      Commons.NumberTheory.Linnik.pf_log_zpow hmpos (hd_nonneg u)
    have hlogmval : Real.log m = -2 * Real.log L := by
      dsimp [m]
      rw [one_div, Real.log_inv, Real.log_pow]
      ring
    have hstep : (d u : ℝ) * Real.log m ≤ Real.log ‖(ζ - u) ^ (d u)‖ := by
      simpa [hlogm] using hlog_ge
    have hcalc : -Real.log ‖(ζ - u) ^ (d u)‖ ≤ -(d u : ℝ) * Real.log m := by linarith
    have hmval : -(d u : ℝ) * Real.log m = (d u : ℝ) * (2 * Real.log L) := by
      rw [hlogmval]; ring
    linarith
  have hsubP : Function.mulSupport (fun u : ℂ => (ζ - u) ^ (d u)) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_mulSupport] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      exact hu (by simp [hd0])
    exact (hmemS u).mpr hdne
  have hprod_eq : (∏ᶠ u : ℂ, (ζ - u) ^ (d u)) = ∏ u ∈ S, (ζ - u) ^ (d u) :=
    finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (ζ - u) ^ (d u)) hsubP
  have hfin_eq : (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) = ∑ u ∈ S, ((d u : ℤ) : ℝ) := by
    refine finsum_eq_sum_of_support_subset (fun u : ℂ => ((d u : ℤ) : ℝ)) ?_
    intro u hu
    rw [Function.mem_support] at hu
    have hdne : d u ≠ 0 := by
      intro hd0
      exact hu (by simp [hd0])
    exact (hmemS u).mpr hdne
  calc
    -Real.log ‖∏ᶠ u : ℂ, (ζ - u) ^ (d u)‖
        = -Real.log ‖∏ u ∈ S, (ζ - u) ^ (d u)‖ := by rw [hprod_eq]
    _ = -Real.log (∏ u ∈ S, ‖(ζ - u) ^ (d u)‖) := by
        rw [Commons.NumberTheory.Linnik.pf_norm_finset_prod S (fun u => (ζ - u) ^ (d u))]
    _ = -(∑ u ∈ S, Real.log ‖(ζ - u) ^ (d u)‖) := by
        rw [Real.log_prod]
        intro u hu
        exact (hprod_pos_fac u hu).ne'
    _ = ∑ u ∈ S, -Real.log ‖(ζ - u) ^ (d u)‖ := by simp [Finset.sum_neg_distrib]
    _ ≤ ∑ u ∈ S, ((d u : ℤ) : ℝ) * (2 * Real.log L) :=
        Finset.sum_le_sum (fun u hu => hlog_per u hu)
    _ = (∑ u ∈ S, ((d u : ℤ) : ℝ)) * (2 * Real.log L) := by rw [Finset.sum_mul]
    _ = (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) * (2 * Real.log L) := by rw [← hfin_eq]
    _ = (2 * Real.log L) * (∑ᶠ u : ℂ, ((d u : ℤ) : ℝ)) := by ring
    _ = (2 * Real.log (xiL A)) *
        (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Xi (Metric.closedBall (0 : ℂ) T)) u : ℝ)) := by
        simp only [d, L]

/-- Log-bound for `Ξ` on a circle, from the growth hypothesis. -/
lemma xiE_cofactor_logXi_circle {T gc : ℝ} (hT2 : 2 ≤ T)
    (hgc : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R → ‖Xi z‖ ≤ Real.exp (gc * R * xiL R))
    {ζ : ℂ} (hζ : ‖ζ‖ = T) (hζnz : Xi ζ ≠ 0) :
    Real.log ‖Xi ζ‖ ≤ gc * T * xiL T := by
  have hb := hgc T hT2 ζ hζ
  have hle : Real.log ‖Xi ζ‖ ≤ Real.log (Real.exp (gc * T * xiL T)) :=
    Real.log_le_log (norm_pos_iff.mpr hζnz) hb
  rwa [Real.log_exp] at hle

theorem xiE_cofactor_logbound {A T : ℝ} (hA0 : 0 ≤ A) (hA1 : 1 ≤ A)
    (hTpos : 0 < T) (hT2 : 2 ≤ T) (hT2A : T ≤ 2 * A)
    (hmargin : ∀ u : ℂ, Work.LinnikAreas.DhK.Xi u = 0 →
      (Work.LinnikAreas.DhK.xiL A) ^ 2 * |‖u‖ - T| ≥ 1)
    (zc gc : ℝ) (hzc_nonneg : 0 ≤ zc) (hgc_nonneg : 0 ≤ gc)
    (hzc : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
        (Metric.closedBall 0 R)) u : ℝ)) ≤ zc * R * Work.LinnikAreas.DhK.xiL R)
    (hgc : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      ‖Work.LinnikAreas.DhK.Xi z‖ ≤ Real.exp (gc * R * Work.LinnikAreas.DhK.xiL R))
    (δ₀ : ℝ) (hδ₀pos : 0 < δ₀)
    (hLgeD : |Real.log δ₀| ≤ Work.LinnikAreas.DhK.xiL A)
    (hδ₀ : ∀ u : ℂ, Work.LinnikAreas.DhK.Xi u = 0 → δ₀ ≤ ‖u‖) :
    ∃ (g : ℂ → ℂ) (M0 : ℝ), 0 ≤ M0 ∧
      AnalyticOnNhd ℂ g (Metric.ball 0 T) ∧
      (∀ w : ℂ, w ∈ Metric.ball 0 T → g w ≠ 0) ∧
      (∀ z : ℂ, z ∈ Metric.ball 0 T → Work.LinnikAreas.DhK.Xi z =
        (∏ᶠ u : ℂ, (z - u) ^
          (MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 T) u)) * g z) ∧
      (∃ ε : ℝ, 0 < ε ∧ AnalyticOnNhd ℂ g (Metric.ball 0 (T + ε)) ∧
        (∀ z : ℂ, z ∈ Metric.ball 0 (T + ε) → Work.LinnikAreas.DhK.Xi z =
          (∏ᶠ u : ℂ, (z - u) ^
            (MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 T) u)) * g z)) ∧
      (∀ w : ℂ, w ∈ Metric.ball 0 T → Real.log ‖g w‖ ≤ M0) ∧
      |Real.log ‖g 0‖| ≤ M0 ∧
      M0 ≤ (4 * gc + 20 * zc + |Real.log ‖Work.LinnikAreas.DhK.Xi 0‖| + 1)
        * (A * (Work.LinnikAreas.DhK.xiL A) ^ 2 + 1) := by
  classical
  have hXi0 : Xi 0 ≠ 0 := Xi_zero_ne
  have hXidiff : Differentiable ℂ Xi := Xi_differentiable
  have hcirc : ∀ u : ℂ, ‖u‖ = T → Xi u ≠ 0 := by
    intro u hu hz
    have hmm := hmargin u hz
    have hLpos : 0 < (xiL A) ^ 2 := by
      have := xiL_pos hA0
      positivity
    have hzero : |‖u‖ - T| = 0 := by simp [hu]
    have hb : (1 : ℝ) ≤ 0 := by simpa [hzero, mul_zero] using hmm
    linarith
  rcases Commons.NumberTheory.Linnik.factorization_open (f := Xi) (R := T) hTpos hXidiff hXi0
    hcirc with ⟨g, ε, hε, hg_an, hg_nz, hfac⟩
  have hg_an_T : AnalyticOnNhd ℂ g (ball 0 T) := by
    intro w hw
    have hwT : ‖w‖ < T := by simpa [mem_ball_zero_iff] using hw
    have hw' : ‖w‖ < T + ε := by linarith
    exact hg_an w (by simpa [mem_ball_zero_iff] using hw')
  have hg_nz_T : ∀ w : ℂ, w ∈ ball 0 T → g w ≠ 0 := by
    intro w hw
    have hwT : ‖w‖ < T := by simpa [mem_ball_zero_iff] using hw
    have hw' : ‖w‖ < T + ε := by linarith
    exact hg_nz w (by simpa [mem_ball_zero_iff] using hw')
  have hfac_T : ∀ z : ℂ, z ∈ ball 0 T → Xi z =
      (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u)) * g z := by
    intro z hz
    have hzT : ‖z‖ < T := by simpa [mem_ball_zero_iff] using hz
    have hz' : ‖z‖ < T + ε := by linarith
    exact hfac z (by simpa [mem_ball_zero_iff] using hz')
  let L : ℝ := xiL A
  let LT : ℝ := xiL T
  let Z : ℝ := ∑ᶠ u : ℂ, ((MeromorphicOn.divisor Xi (closedBall 0 T)) u : ℝ)
  let Q1 : ℝ := gc * T * LT
  let Q2 : ℝ := (2 * Real.log L) * (zc * T * LT)
  let Q3 : ℝ := |Real.log ‖Xi 0‖|
  let Q4 : ℝ := (zc * T * LT) * (Real.log T + |Real.log δ₀|)
  let M0 : ℝ := Q1 + Q2 + Q3 + Q4 + 1
  have hL2 : 2 ≤ L := xiL_ge_two hA0
  have hLpos : 0 < L := xiL_pos hA0
  have hL1 : 1 ≤ L := by linarith
  have hLTpos : 0 < LT := xiL_pos (le_of_lt hTpos)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogδ0 : 0 ≤ |Real.log δ₀| := abs_nonneg _
  have hTge0 : 0 ≤ T := le_of_lt hTpos
  have hQ1 : 0 ≤ Q1 := by dsimp [Q1]; positivity
  have hQ2 : 0 ≤ Q2 := by dsimp [Q2]; positivity
  have hQ3 : 0 ≤ Q3 := by dsimp [Q3]; exact abs_nonneg _
  have hQ4 : 0 ≤ Q4 := by
    dsimp [Q4]
    have h1 : 0 ≤ Real.log T + |Real.log δ₀| := by linarith
    positivity
  have hM0_nonneg : 0 ≤ M0 := by dsimp [M0]; linarith
  have hbnd : ∀ ζ : ℂ, ‖ζ‖ = T → Real.log ‖g ζ‖ ≤ Q1 + Q2 := by
    intro ζ hζ
    have hζε : ζ ∈ ball 0 (T + ε) := by rw [mem_ball_zero_iff]; nlinarith [hζ, hε]
    have hXiζ : Xi ζ ≠ 0 := hcirc ζ hζ
    have hgζ : g ζ ≠ 0 := hg_nz ζ hζε
    have hfacζ : Xi ζ =
        (∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u)) * g ζ :=
      hfac ζ hζε
    have hPζ : (∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u)) ≠ 0 := by
      have hmul : (∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u)) * g ζ ≠ 0 := by
        simpa [hfacζ] using hXiζ
      exact (mul_ne_zero_iff.mp hmul).1
    have hlog_mul : Real.log ‖Xi ζ‖ =
        Real.log ‖(∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖
          + Real.log ‖g ζ‖ := by
      rw [hfacζ]
      exact Commons.NumberTheory.Linnik.pf_log_eq_of_mul hPζ hgζ
    have hlogXi : Real.log ‖Xi ζ‖ ≤ gc * T * LT := by
      have hb := xiE_cofactor_logXi_circle hT2 hgc hζ hXiζ
      simpa [LT] using hb
    have hfaclow : -Real.log
        ‖(∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖
          ≤ (2 * Real.log L) * Z := by
      have hb := xiE_cofactor_fac_log_lower hA0 hTpos hmargin hζ
      simpa only [L, Z] using hb
    have hZle : Z ≤ zc * T * LT := by
      have h := hzc T hT2
      simpa only [Z, LT] using h
    have hstep : Real.log ‖g ζ‖ = Real.log ‖Xi ζ‖ -
        Real.log ‖(∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖ := by
      rw [hlog_mul]; ring
    have h2L : 0 ≤ 2 * Real.log L := by linarith
    have hQ2ge : (2 * Real.log L) * Z ≤ Q2 := by
      have h := mul_le_mul_of_nonneg_left hZle h2L
      simpa only [Q2] using h
    calc Real.log ‖g ζ‖
        = Real.log ‖Xi ζ‖ -
          Real.log ‖(∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖ := hstep
      _ ≤ gc * T * LT + (2 * Real.log L) * Z := by linarith
      _ ≤ gc * T * LT + Q2 := by linarith
      _ = Q1 + Q2 := by dsimp [Q1]
  have hball : ∀ w : ℂ, w ∈ ball 0 T → Real.log ‖g w‖ ≤ M0 := by
    intro w hw
    have hg_cont : DiffContOnCl ℂ g (ball 0 T) := by
      refine DifferentiableOn.diffContOnCl ?_
      have hcl : DifferentiableOn ℂ g (closedBall 0 T) := by
        intro x hx
        rw [Metric.mem_closedBall, dist_eq_norm] at hx
        have hx' : x ∈ ball 0 (T + ε) := by
          rw [mem_ball_zero_iff]
          have hxT : ‖x‖ ≤ T := by simpa using hx
          linarith [hε]
        exact (hg_an.differentiableOn.differentiableAt
          (isOpen_ball.mem_nhds hx')).differentiableWithinAt
      simpa [closure_ball (0 : ℂ) (ne_of_gt hTpos)] using hcl
    have hfront : ∀ ζ : ℂ, ζ ∈ frontier (ball 0 T) → ‖g ζ‖ ≤ Real.exp M0 := by
      intro ζ hζf
      rw [frontier_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_sphere, dist_eq_norm] at hζf
      have hζ : ‖ζ‖ = T := by simpa using hζf
      have hb := hbnd ζ hζ
      have hζε : ζ ∈ ball 0 (T + ε) := by rw [mem_ball_zero_iff]; nlinarith [hζ, hε]
      have hle : Real.log ‖g ζ‖ ≤ M0 := by
        have hQ12 : Q1 + Q2 ≤ M0 := by dsimp [M0]; linarith [hQ3, hQ4]
        linarith
      exact le_trans (le_of_eq (Real.exp_log (norm_pos_iff.mpr (hg_nz ζ hζε))).symm)
        (Real.exp_le_exp.mpr hle)
    have hcl : w ∈ closure (ball 0 T) := by
      rw [closure_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_closedBall, dist_eq_norm]
      have hw' : ‖w‖ < T := by simpa [mem_ball_zero_iff] using hw
      simpa using le_of_lt hw'
    have hnorm : ‖g w‖ ≤ Real.exp M0 :=
      Complex.norm_le_of_forall_mem_frontier_norm_le
        (isBounded_ball (x := (0 : ℂ)) (r := T)) hg_cont hfront hcl
    have hpos : 0 < ‖g w‖ := norm_pos_iff.mpr (hg_nz_T w hw)
    have hle : Real.log ‖g w‖ ≤ Real.log (Real.exp M0) := Real.log_le_log hpos hnorm
    rwa [Real.log_exp] at hle
  have horigin : |Real.log ‖g 0‖| ≤ M0 := by
    have h0T : (0 : ℂ) ∈ ball 0 T := by rw [mem_ball_zero_iff]; simpa using hTpos
    have hfac0 := hfac_T 0 h0T
    have hP0 : (∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
        (MeromorphicOn.divisor Xi (closedBall 0 T) u)) ≠ 0 := by
      have hmul : (∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
          (MeromorphicOn.divisor Xi (closedBall 0 T) u)) * g 0 ≠ 0 := by
        simpa [hfac0] using hXi0
      exact (mul_ne_zero_iff.mp hmul).1
    have hg0nz : g 0 ≠ 0 := hg_nz_T 0 h0T
    have hlog_mul0 : Real.log ‖Xi 0‖ = Real.log
        ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖
          + Real.log ‖g 0‖ := by
      rw [hfac0]
      exact Commons.NumberTheory.Linnik.pf_log_eq_of_mul hP0 hg0nz
    have hP0b := xiECofactorAuxP0 (T := T) (δ₀ := δ₀)
      (le_trans (by norm_num) hT2) hδ₀pos hδ₀
    have hZle : Z ≤ zc * T * LT := by
      have h := hzc T hT2
      simpa only [Z, LT] using h
    have hP0le : |Real.log
        ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖| ≤ Q4 := by
      have hBnn : 0 ≤ Real.log T + |Real.log δ₀| := by linarith
      have h1 : Z * (Real.log T + |Real.log δ₀|) ≤
          (zc * T * LT) * (Real.log T + |Real.log δ₀|) :=
        mul_le_mul_of_nonneg_right hZle hBnn
      calc |Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
              (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖|
            ≤ Z * (Real.log T + |Real.log δ₀|) := by simpa only [Z] using hP0b
        _ ≤ (zc * T * LT) * (Real.log T + |Real.log δ₀|) := h1
        _ = Q4 := by dsimp [Q4]
    have hlogg0 : |Real.log ‖g 0‖| ≤ Q3 + Q4 := by
      have hAb : |Real.log ‖Xi 0‖ - Real.log
          ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖| ≤
          |Real.log ‖Xi 0‖| + |Real.log
          ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖| := by
        rw [sub_eq_add_neg]
        calc |Real.log ‖Xi 0‖ + -Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
                (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖|
              ≤ |Real.log ‖Xi 0‖| + |(-Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
                (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖)| := abs_add_le _ _
          _ = |Real.log ‖Xi 0‖| + |Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
                (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖| := by rw [abs_neg]
      have hrew : Real.log ‖g 0‖ = Real.log ‖Xi 0‖ - Real.log
          ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^ (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖ := by
        rw [hlog_mul0]; ring
      rw [hrew]
      have h3 : |Real.log ‖Xi 0‖ - Real.log ‖(∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
          (MeromorphicOn.divisor Xi (closedBall 0 T) u))‖| ≤ Q3 + Q4 := by
        have hQ3eq : |Real.log ‖Xi 0‖| = Q3 := by dsimp [Q3]
        linarith [hAb, hP0le, hQ3eq]
      exact h3
    have h34 : Q3 + Q4 ≤ M0 := by dsimp [M0]; linarith [hQ1, hQ2]
    have hg0ball : Real.log ‖g 0‖ ≤ M0 := hball 0 h0T
    have h2 : -M0 ≤ Real.log ‖g 0‖ := by
      have hle' : |Real.log ‖g 0‖| ≤ M0 := le_trans hlogg0 h34
      linarith [abs_le.mp hle']
    exact abs_le.mpr ⟨h2, hg0ball⟩
  have hM0_bound : M0 ≤ (4 * gc + 20 * zc + |Real.log ‖Xi 0‖| + 1) * (A * L ^ 2 + 1) := by
    have hLT2 : LT ≤ 2 * L := by
      have hmono : xiL T ≤ xiL (2 * A) := xiL_mono hTge0 hT2A
      have h2 : xiL (2 * A) ≤ 2 * xiL A := xiL_two_mul_le hA1
      dsimp only [LT, L]
      linarith
    have hlogT_le_LT : Real.log T ≤ LT := by
      have h1 : Real.log T ≤ Real.log (T + 2) := Real.log_le_log hTpos (by linarith)
      dsimp only [LT, xiL]
      linarith
    have hlogT_le : Real.log T ≤ 2 * L := le_trans hlogT_le_LT hLT2
    have hTl : T * LT ≤ (2 * A) * (2 * L) := by
      have h1 : T ≤ 2 * A := hT2A
      have h2 : LT ≤ 2 * L := hLT2
      nlinarith [hTge0, le_of_lt hLTpos, hA0, le_of_lt hLpos]
    have hQ1le : Q1 ≤ 4 * gc * A * L ^ 2 := by
      have hga : 0 ≤ gc * A := mul_nonneg hgc_nonneg hA0
      have hLsq : L ≤ L ^ 2 := by nlinarith [hL1]
      have hstep : gc * T * LT ≤ gc * ((2 * A) * (2 * L)) := by
        have := mul_le_mul_of_nonneg_left hTl hgc_nonneg
        nlinarith [this]
      have hstep2 : gc * ((2 * A) * (2 * L)) = 4 * (gc * A * L) := by ring
      have hstep3 : gc * A * L ≤ gc * A * L ^ 2 := mul_le_mul_of_nonneg_left hLsq hga
      calc Q1 = gc * T * LT := rfl
        _ ≤ gc * ((2 * A) * (2 * L)) := hstep
        _ = 4 * (gc * A * L) := hstep2
        _ ≤ 4 * (gc * A * L ^ 2) := by linarith
        _ = 4 * gc * A * L ^ 2 := by ring
    have hQ2le : Q2 ≤ 8 * zc * A * L ^ 2 := by
      have hlogL_le : Real.log L ≤ L := Real.log_le_self (le_of_lt hLpos)
      have h2log : 2 * Real.log L ≤ 2 * L := by linarith
      have hzT : 0 ≤ zc * T * LT := by positivity
      have hzle : zc * T * LT ≤ zc * ((2 * A) * (2 * L)) := by
        have := mul_le_mul_of_nonneg_left hTl hzc_nonneg
        nlinarith [this]
      calc Q2 = (2 * Real.log L) * (zc * T * LT) := rfl
        _ ≤ (2 * L) * (zc * T * LT) := mul_le_mul_of_nonneg_right h2log hzT
        _ ≤ (2 * L) * (zc * ((2 * A) * (2 * L))) := by
            have h2L : 0 ≤ 2 * L := by linarith
            exact mul_le_mul_of_nonneg_left hzle h2L
        _ = 8 * zc * A * L ^ 2 := by ring
    have hQ3le : Q3 ≤ |Real.log ‖Xi 0‖| * (A * L ^ 2 + 1) := by
      have h1 : 1 ≤ A * L ^ 2 + 1 := by nlinarith [hA0, sq_nonneg L]
      dsimp only [Q3]
      nlinarith [abs_nonneg (Real.log ‖Xi 0‖)]
    have hQ4le : Q4 ≤ 12 * zc * A * L ^ 2 := by
      have hB : Real.log T + |Real.log δ₀| ≤ 3 * L := by
        have h2 : |Real.log δ₀| ≤ L := by dsimp only [L]; exact hLgeD
        linarith
      have hzle : zc * T * LT ≤ zc * ((2 * A) * (2 * L)) := by
        have := mul_le_mul_of_nonneg_left hTl hzc_nonneg
        nlinarith [this]
      have hBnn : 0 ≤ Real.log T + |Real.log δ₀| := by linarith
      have hz2A : 0 ≤ zc * ((2 * A) * (2 * L)) := by positivity
      calc Q4 = (zc * T * LT) * (Real.log T + |Real.log δ₀|) := rfl
        _ ≤ (zc * ((2 * A) * (2 * L))) * (3 * L) :=
            mul_le_mul hzle hB hBnn hz2A
        _ = 12 * zc * A * L ^ 2 := by ring
    dsimp only [M0]
    nlinarith [hQ1le, hQ2le, hQ3le, hQ4le, hgc_nonneg, hzc_nonneg, hA0, sq_nonneg L,
      abs_nonneg (Real.log ‖Xi 0‖), hLpos]
  refine ⟨g, M0, hM0_nonneg, hg_an_T, hg_nz_T, hfac_T,
    ⟨ε, hε, hg_an, hfac⟩, hball, horigin, ?_⟩
  simpa only [L] using hM0_bound

end Work.LinnikAreas.ownRepelNW
