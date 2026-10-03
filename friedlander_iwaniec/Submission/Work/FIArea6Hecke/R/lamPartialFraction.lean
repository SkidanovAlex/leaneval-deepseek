import Mathlib
import Submission.Work.FIArea6Hecke.R.logDerivCore
import Submission.Work.FIArea5.HeckeZFR.Lam_partialFraction
import Submission.Work.FIArea5.HeckeZFR.Hadm.factorZero
import Submission.Work.FIArea5.HeckeZFR.Hadm.goodRadius
import Submission.Work.FIArea5.HeckeZFR.Hadm.cofactorBound
import Submission.Work.FIArea5.HeckeZFR.Hadm.pfConv
import Submission.Work.FIArea6Hecke.R.cofactorZeroFreeBall
import Submission.Work.FIArea6Hecke.R.canonicalProductCircleLower
import Submission.Work.FIArea6Hecke.R.canonicalProductZeroBound
import Submission.Work.FIArea6Hecke.R.cofactorA0Bound

set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section

/-! ### The general cofactor bound at a good radius -/

/-- **Cofactor bound at a good radius** (maximum-modulus form).  If `Λ` is entire with `Λ 0 ≠ 0`,
circle growth `C·R·(log (R+2) + K)` and zero-count bound `c·R·(log (R+2) + K)`, then at every
good radius `T` (every zero of `Λ` keeps distance at least `(log (A+2)+K+1)^{-2}` from the circle
`‖z‖ = T`) the canonical-product cofactor `g` admits a sup bound
`M0 ≤ (C+4c)·T·(log (T+2) + K + 1)^2 + A₀`, together with `|log ‖g 0‖| ≤ M0`. -/
theorem cofactorBound (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ) (h0 : Λ 0 ≠ 0)
    (C K c : ℝ) (hC : 0 < C) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hgrowth : ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      Real.log ‖Λ z‖ ≤ C * R * (Real.log (R + 2) + K))
    (hcount : ∀ R : ℝ, 1 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)) ≤
        c * R * (Real.log (R + 2) + K)) :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ A T : ℝ, 1 ≤ A → A ≤ T → T ≤ 2 * A →
      (∀ u : ℂ, Λ u = 0 → (Real.log (A + 2) + K + 1) ^ 2 * |‖u‖ - T| ≥ 1) →
      ∃ (g : ℂ → ℂ) (ε M0 : ℝ), 0 < ε ∧ 0 ≤ M0 ∧
        AnalyticOnNhd ℂ g (Metric.ball 0 (T + ε)) ∧
        (∀ w : ℂ, w ∈ Metric.ball 0 (T + ε) → g w ≠ 0) ∧
        (∀ z : ℂ, z ∈ Metric.ball 0 (T + ε) →
          Λ z = (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)) * g z) ∧
        (∀ w : ℂ, w ∈ Metric.ball 0 T → Real.log ‖g w‖ ≤ M0) ∧
        |Real.log ‖g 0‖| ≤ M0 ∧
        M0 ≤ (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 + A₀ := by
  classical
  obtain ⟨δ, hδpos, hδnz⟩ := cofactorZeroFreeBall hDiff h0
  have hδle : ∀ u : ℂ, Λ u = 0 → δ ≤ ‖u‖ := by
    intro u hu
    by_contra hlt
    rw [not_le] at hlt
    exact hδnz u hlt hu
  obtain ⟨A1, hA10, hA1⟩ := cofactorA0Bound C K c |Real.log δ| hC hK hc
  refine ⟨A1 + |Real.log ‖Λ 0‖|, by positivity, ?_⟩
  intro A T hA1' hAT hT2A hmargin
  have hA0 : 0 ≤ A := by linarith
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hAn : AnalyticOnNhd ℂ Λ (Metric.closedBall 0 T) := fun z _ => hDiff.analyticAt z
  set S : ℝ := Real.log (T + 2) + K + 1 with hSdef
  have hS1 : 1 ≤ S := by
    have h2 : (0 : ℝ) ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    rw [hSdef]; linarith
  have hSpos : 0 < S := lt_of_lt_of_le one_pos hS1
  set Z : ℝ := (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u : ℤ) : ℝ))
    with hZdef
  have hZnn : 0 ≤ Z := by
    rw [hZdef]
    exact finsum_nonneg (fun u => by
      have h := (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := Λ)
        (U := Metric.closedBall 0 T) hAn) u
      exact_mod_cast h)
  have hZbd : Z ≤ c * T * (Real.log (T + 2) + K) := by
    rw [hZdef]; exact hcount T hT1
  have hKleS : Real.log (T + 2) + K ≤ S := by rw [hSdef]; linarith
  have hZbdS : Z ≤ c * T * S := by
    refine le_trans hZbd ?_
    exact mul_le_mul_of_nonneg_left hKleS (by positivity)
  -- Λ has no zero on the circle of radius T
  have hcirc : ∀ u : ℂ, ‖u‖ = T → Λ u ≠ 0 := by
    intro u hu hzu
    have hm := hmargin u hzu
    have hzero : |‖u‖ - T| = 0 := by rw [hu, sub_self, abs_zero]
    rw [hzero, mul_zero] at hm
    linarith
  obtain ⟨g, ε, hε, hgan, hgnz, hfac⟩ :=
    Commons.NumberTheory.Linnik.factorization_open (f := Λ) (R := T) hTpos hDiff h0 hcirc
  set M0 : ℝ := (C + 4 * c) * T * S ^ 2 + A1 + |Real.log ‖Λ 0‖| with hM0def
  have hM0nn : 0 ≤ M0 := by
    rw [hM0def]
    have h1 : (0 : ℝ) ≤ (C + 4 * c) * T * S ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ |Real.log ‖Λ 0‖| := abs_nonneg _
    linarith
  -- pointwise upper bound on the circle
  have hcircU : ∀ ζ : ℂ, ‖ζ‖ = T → Real.log ‖g ζ‖ ≤ M0 := by
    intro ζ hζ
    have hΛζ : Λ ζ ≠ 0 := hcirc ζ hζ
    have hζb : ζ ∈ Metric.ball 0 (T + ε) := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    have hgζ : g ζ ≠ 0 := hgnz ζ hζb
    have hPζ : (∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)) ≠ 0 := by
      intro hh
      have hf := hfac ζ hζb
      rw [hh, zero_mul] at hf
      exact hΛζ hf
    have hlogmul : Real.log ‖Λ ζ‖ =
        Real.log ‖∏ᶠ u : ℂ, (ζ - u) ^ (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)‖
          + Real.log ‖g ζ‖ := by
      rw [hfac ζ hζb, norm_mul,
        Real.log_mul (norm_ne_zero_iff.mpr hPζ) (norm_ne_zero_iff.mpr hgζ)]
    have hΛbd : Real.log ‖Λ ζ‖ ≤ C * T * (Real.log (T + 2) + K) := hgrowth T hT1 ζ hζ
    have hPbd := canonicalProductCircleLower Λ A T K hK hA0 hTpos hAn hmargin hζ
    have hLA2 : 0 ≤ Real.log (A + 2) := Real.log_nonneg (by linarith)
    have hLApos : 0 < Real.log (A + 2) + K + 1 := by linarith
    have hLAnn : 0 ≤ Real.log (Real.log (A + 2) + K + 1) := Real.log_nonneg (by linarith)
    have hLAle : Real.log (Real.log (A + 2) + K + 1) ≤ Real.log S := by
      apply Real.log_le_log hLApos
      rw [hSdef]
      have h2 : Real.log (A + 2) ≤ Real.log (T + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    have hPbdS : -Real.log ‖∏ᶠ u : ℂ, (ζ - u) ^
          (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)‖ ≤ 2 * Real.log S * Z := by
      rw [hZdef]
      refine le_trans hPbd ?_
      apply mul_le_mul_of_nonneg_right _ (finsum_nonneg (fun u => by
        have h := (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (f := Λ)
          (U := Metric.closedBall 0 T) hAn) u
        exact_mod_cast h))
      linarith
    have hgc : Real.log ‖g ζ‖ ≤ C * T * (Real.log (T + 2) + K) + 2 * Real.log S * Z := by
      linarith [hΛbd, hPbdS, hlogmul]
    have hlogS : Real.log S ≤ S := by
      have h := Real.log_le_sub_one_of_pos hSpos
      linarith
    have hb1 : 2 * Real.log S * Z ≤ 2 * c * T * S ^ 2 := by
      calc 2 * Real.log S * Z ≤ 2 * S * (c * T * S) := by
            apply mul_le_mul _ hZbdS hZnn (by positivity)
            linarith
        _ = 2 * c * T * S ^ 2 := by ring
    have hb2 : C * T * (Real.log (T + 2) + K) ≤ C * T * S :=
      mul_le_mul_of_nonneg_left hKleS (by positivity)
    have hb3 : C * T * S ≤ C * T * S ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [hS1]
    have hb4 : C * T * S + 2 * c * T * S ^ 2 ≤ (C + 4 * c) * T * S ^ 2 := by
      have h4 : 2 * c * T * S ^ 2 ≤ 4 * c * T * S ^ 2 := by
        have : (0 : ℝ) ≤ 2 * c * T * S ^ 2 := by positivity
        nlinarith
      nlinarith [hb3, h4]
    have hb5 : (C + 4 * c) * T * S ^ 2 ≤ M0 := by
      rw [hM0def]
      have h1 : (0 : ℝ) ≤ |Real.log ‖Λ 0‖| := abs_nonneg _
      linarith
    linarith [hgc, hb1, hb2, hb4, hb5]
  -- ball bound by the maximum modulus principle
  have hball : ∀ w : ℂ, w ∈ Metric.ball 0 T → Real.log ‖g w‖ ≤ M0 := by
    intro w hw
    have hcl : DifferentiableOn ℂ g (Metric.closedBall 0 T) := by
      intro x hx
      have hxT : ‖x‖ ≤ T := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      have hxε : x ∈ Metric.ball 0 (T + ε) := by
        rw [Metric.mem_ball, dist_zero_right]; linarith
      exact ((hgan x hxε).differentiableAt).differentiableWithinAt
    have hdiffCl : DiffContOnCl ℂ g (Metric.ball 0 T) := by
      refine DifferentiableOn.diffContOnCl ?_
      simpa [closure_ball (0 : ℂ) (ne_of_gt hTpos)] using hcl
    have hfront : ∀ ζ : ℂ, ζ ∈ frontier (Metric.ball 0 T) → ‖g ζ‖ ≤ Real.exp M0 := by
      intro ζ hζf
      rw [frontier_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_sphere, dist_eq_norm] at hζf
      have hζ : ‖ζ‖ = T := by simpa using hζf
      have hb := hcircU ζ hζ
      have hζb : ζ ∈ Metric.ball 0 (T + ε) := by
        rw [Metric.mem_ball, dist_zero_right]; linarith
      have hgζ : g ζ ≠ 0 := hgnz ζ hζb
      have hpos : 0 < ‖g ζ‖ := norm_pos_iff.mpr hgζ
      calc ‖g ζ‖ = Real.exp (Real.log ‖g ζ‖) := by rw [Real.exp_log hpos]
        _ ≤ Real.exp M0 := Real.exp_le_exp.mpr hb
    have hwT : ‖w‖ < T := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hwcl : w ∈ closure (Metric.ball 0 T) := by
      rw [closure_ball (0 : ℂ) (ne_of_gt hTpos), Metric.mem_closedBall, dist_eq_norm]
      simpa using hwT.le
    have hnorm : ‖g w‖ ≤ Real.exp M0 :=
      Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdiffCl hfront hwcl
    have hwε : w ∈ Metric.ball 0 (T + ε) := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    have hwpos : 0 < ‖g w‖ := norm_pos_iff.mpr (hgnz w hwε)
    have hlogle := Real.log_le_log hwpos hnorm
    rwa [Real.log_exp] at hlogle
  -- bound at the origin
  have h0bd : |Real.log ‖g 0‖| ≤ M0 := by
    have h0b : (0 : ℂ) ∈ Metric.ball 0 (T + ε) := by
      rw [Metric.mem_ball, dist_zero_right]; simp; linarith
    have hfac0 := hfac 0 h0b
    have hP0nz : (∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
        (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)) ≠ 0 := by
      intro hh
      rw [hh, zero_mul] at hfac0
      exact h0 hfac0
    have hg0nz : g 0 ≠ 0 := hgnz 0 h0b
    have hlog0 : Real.log ‖g 0‖ = Real.log ‖Λ 0‖ -
        Real.log ‖∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
          (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)‖ := by
      have h1 : Real.log ‖Λ 0‖ = Real.log ‖∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
            (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)‖ + Real.log ‖g 0‖ := by
        rw [hfac0, norm_mul,
          Real.log_mul (norm_ne_zero_iff.mpr hP0nz) (norm_ne_zero_iff.mpr hg0nz)]
      linarith
    have hP0bd := canonicalProductZeroBound Λ T hT1 δ hδpos hAn hδle
    have hlnn : 0 ≤ Real.log T + |Real.log δ| := by
      have h1 : 0 ≤ Real.log T := Real.log_nonneg hT1
      have h2 : 0 ≤ |Real.log δ| := abs_nonneg _
      linarith
    have hstep : Z * (Real.log T + |Real.log δ|) ≤ c * T * S * (Real.log T + |Real.log δ|) :=
      mul_le_mul_of_nonneg_right hZbdS hlnn
    have hstep2 : c * T * S * (Real.log T + |Real.log δ|) ≤ (C + 4 * c) * T * S ^ 2 + A1 := by
      simpa only [← hSdef] using hA1 T hT1
    calc |Real.log ‖g 0‖| ≤ |Real.log ‖Λ 0‖| +
          |Real.log ‖∏ᶠ u : ℂ, ((0 : ℂ) - u) ^
            (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)‖| := by
            rw [hlog0]; exact abs_sub _ _
      _ ≤ |Real.log ‖Λ 0‖| + Z * (Real.log T + |Real.log δ|) := by
            rw [hZdef]; linarith [hP0bd]
      _ ≤ |Real.log ‖Λ 0‖| + ((C + 4 * c) * T * S ^ 2 + A1) := by linarith [hstep, hstep2]
      _ = M0 := by rw [hM0def]; ring
  refine ⟨g, ε, M0, hε, hM0nn, hgan, hgnz, hfac, hball, h0bd, ?_⟩
  refine le_of_eq ?_
  rw [hM0def, hSdef]
  ring

/-- **The Hadamard partial fraction for an admissible completion**, given the circle growth (the
only analytic input beyond the strictness of `χ`).  For every strict character `χ` mod `4d`, every
`m : ℤ`, every entire completion `Λ` of `Λ(s,ψ)` with `log ‖Λ z‖ ≤ C·R·(log (R+2) + K)` on
`‖z‖ = R ≥ 1`, the divisor-weighted partial sums
`Σ_{|u| ≤ R} ord(u)·(1/(s−u) − 1/(s₁−u))` converge to `Λ'/Λ(s) − Λ'/Λ(s₁)` for all `s, s₁` with
`Λ s ≠ 0 ≠ Λ s₁`. -/
theorem lamPartialFraction (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ)
    (hadm : IsCompleted d chi m Lam)
    (hgrowth : ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      Real.log ‖Lam z‖ ≤ C * R * (Real.log (R + 2) + K)) :
    ∀ s s₁ : ℂ, Lam s ≠ 0 → Lam s₁ ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ, (((divR Lam R u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop
        (nhds (deriv Lam s / Lam s - deriv Lam s₁ / Lam s₁)) := by
  obtain ⟨hd, hchi, hAn, hagree⟩ := hadm
  have hDiff : Differentiable ℂ Lam := differentiableOn_univ.mp hAn.differentiableOn
  by_cases hne : ∃ z : ℂ, Lam z ≠ 0
  · obtain ⟨k, φ, hφdiff, hφ0, hfac, hφgrowth, hdiv0, hdivne⟩ :=
      Work.FIArea5.HeckeZFR.Hadm.factorZero Lam hDiff hne hgrowth
    obtain ⟨C, K, hC, hK, hgrow⟩ := hφgrowth
    obtain ⟨c, hc0, hcount⟩ :=
      Work.FIArea5.HeckeZFR.Lam_zeroCount φ hφdiff hφ0 C K hC hK hgrow
    obtain ⟨A0, hA01, hGood⟩ :=
      Work.FIArea5.HeckeZFR.Hadm.goodRadius φ hφdiff ⟨0, hφ0⟩ K c hK hc0 hcount
    obtain ⟨A1, hA10, hCof⟩ := cofactorBound φ hφdiff hφ0 C K c hC hK hc0 hgrow hcount
    have hConv : ∀ s s₁ : ℂ, ∃ L : ℂ, Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor φ (Metric.closedBall 0 R)) u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop (nhds L) :=
      fun s s₁ => Work.FIArea5.HeckeZFR.Hadm.pfConv φ hφdiff K c hK hc0 hcount s s₁
    have hφpf := Work.FIArea5.HeckeZFR.Lam_aux_of φ hφdiff hφ0 C K hC hK hgrow c hc0 hcount
      ⟨A0, hA01, hGood⟩ ⟨A1, hA10, hCof⟩ hConv
    have hmain := Work.FIArea5.HeckeZFR.Lam_reduce_of Lam φ k hφdiff hφ0 hfac hdiv0 hdivne hφpf
    intro s s₁ hs hs₁
    have hres := hmain s s₁ hs hs₁
    simpa only [divR] using hres
  · push_neg at hne
    intro s s₁ hs hs₁
    exact absurd (hne s) hs

end

end Work.FIArea6Hecke.R
