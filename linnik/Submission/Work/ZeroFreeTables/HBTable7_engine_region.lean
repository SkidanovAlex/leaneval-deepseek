/-
# ZeroFreeTables — HB Lemma 8.7's engine, with *point* region hypotheses

The engine `Work.ZeroFreeTables.lemma8_7_engine_proof` (in `lemma8_7.lean`) carries the blanket
hypothesis

  `hδle : δ ≤ √(log log q)/log q`

which is used only to convert the window bounds `|1 - β₁| ≤ δ`, `|1 - β₂| ≤ δ` into the *region*
conditions `|1 - β_j| ≤ √(log log q)/log q` of HB Lemma 5.2.  Since `δ` is a fixed parameter of
the engine while `√(log log q)/log q → 0`, that blanket hypothesis is not satisfiable for a fixed
`δ > 0` and all `q ≥ q₀`; the consumer has to supply the region condition *directly* at the point
`β₂` (where it follows from `λ₂ · log q = (1-β₂) log q ≤ √(log log q)`, e.g. from the smallness of
`λ₂` in the branch of HB Table 7 where it is used).

This module is therefore the same engine with the single change

  `hδle`  ⟶  `hβ₂reg : |1 - β₂| ≤ √(log log q)/log q`

(the two hypotheses `|1-β₁| ≤ δ`, `|1-β₂| ≤ δ` are kept, and are the ones genuinely used: they
place `ρ₁` and `ρ₂` inside the windows of radius `δ` and bound the evaluation points in the
ball `closedBall 0 2`).  Exactly as in `lemma8_7.lean`, the hypothesis `hδle` was used *only* in
the two facts `|β₂ - 1| ≤ √(log log q)/log q` and `1 - √(log log q)/log q ≤ β₂`, so the proof
transplants verbatim.

Imported by the Table 7 assembly (`HBTable7_proof`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.lemma8_7

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory MeromorphicOn
open scoped Real Topology BigOperators

namespace Work.ZeroFreeTables

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

noncomputable section

theorem lemma8_7_region (x₀ B c₁ c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hF : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {k : ℝ} (hk : 0 ≤ k) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ₁ χ₂ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₂χ₁ : χ₂ ≠ χ₁)
        (hχ₁χ₂ : χ₁ * χ₂ ≠ 1) (hχ₂χ₂ : χ₂ * χ₂ ≠ 1) (hχ₁χ₂χ₂ : χ₁ * (χ₂ * χ₂) ≠ 1)
        (hreal : χ₁ * χ₁ = 1)
        [NeZero χ₁.conductor] [NeZero χ₂.conductor]
        [NeZero (χ₁ * χ₂).conductor] [NeZero (χ₂ * χ₂).conductor]
        [NeZero (χ₁ * (χ₂ * χ₂)).conductor]
        {β₁ β₂ γ₂ : ℝ}
        (hβ₁ : |1 - β₁| ≤ δ) (hβ₂ : |1 - β₂| ≤ δ)
        (hγ₂ : 2 * |γ₂| + 1 ≤ 10 * Real.log (q : ℝ))
        (hβ₂reg : |1 - β₂| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hzero₁ : DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0)
        (hzero₂ : DirichletCharacter.LFunction χ₂ ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I) = 0)
        (hmaxA : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂).primitiveCharacter u = 0 →
          |u.im| ≤ |γ₂| + 1 → u.re ≤ β₂)
        (hmaxB : ∀ u : ℂ, DirichletCharacter.LFunction (χ₂ * χ₂).primitiveCharacter u = 0 →
          |u.im| ≤ 2 * |γ₂| + 1 → u.re ≤ β₂)
        (hmaxC : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * (χ₂ * χ₂)).primitiveCharacter u = 0 →
          |u.im| ≤ 2 * |γ₂| + 1 → u.re ≤ β₂)
        (hmaxD : ∀ u : ℂ, DirichletCharacter.LFunction χ₂.primitiveCharacter u = 0 →
          |u.im| ≤ |γ₂| + 1 → u.re ≤ β₂)
        (hmaxE : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
          |u.im| ≤ 1 → u = (β₁ : ℂ) ∨ u.re ≤ β₂)
        (hdivB : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
            (Metric.closedBall 0 (|γ₂| + 2))) ((β₂ : ℂ) + (γ₂ : ℂ) * Complex.I) ≠ 0)
        (hdivE : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
            (Metric.closedBall 0 (|γ₂| + 2))) (β₁ : ℂ) ≠ 0)
        (H₁ : Commons.NumberTheory.Linnik.L52Hyp χ₁ c₁ ε δ)
        (H₂ : Commons.NumberTheory.Linnik.L52Hyp χ₂ c ε δ)
        (H₃ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) c ε δ)
        (H₄ : Commons.NumberTheory.Linnik.L52Hyp (χ₂ * χ₂) c ε δ)
        (H₅ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * (χ₂ * χ₂)) c ε δ),
      0 ≤ (k ^ 2 + 1/2) *
            ((∫ t in (0:ℝ)..x₀, Real.exp ((Real.log (q : ℝ) * (1 - β₂)) * t) * f t)
              - (∫ t in (0:ℝ)..x₀,
                  Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β₂))) * t) * f t))
          - 2 * k * (∫ t in (0:ℝ)..x₀, f t)
          + f 0 * ((k ^ 2 + 1/2) * (c₁ + 2 * ε) + 2 * k * (2 * c + 2 * ε) + (c + ε)) := by
  intro f hcont hsupp hf2 hBnd hf0 hfnn hF k hk ε hε δ hδ0 hδ1
  obtain ⟨q₀p, hq₀p⟩ := (Commons.NumberTheory.Linnik.Ksum_principal_le x₀ B hx₀ hB)
    hcont hsupp hf2 hBnd hε hf0
  obtain ⟨q₀a, hq₀a⟩ := (Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hF hε hδ0 hδ1
  obtain ⟨q₀b, hq₀b⟩ := (Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hF hε hδ0 hδ1
  obtain ⟨q₀n, hq₀n⟩ := (Work.LinnikAreas.DhRepel.Ksum_le_single_ne_of_L52_phi x₀ B c₁ hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hF hε hδ0 hδ1
  refine ⟨max (max (max (max q₀p q₀a) q₀b) q₀n) 8 + 6, ?_⟩
  intro q _inst hq χ₁ χ₂ hχ₁ hχ₂ hχ₂χ₁ hχ₁χ₂ hχ₂χ₂ hχ₁χ₂χ₂ hreal
    _ic₁ _ic₂ _ic₃ _ic₄ _ic₅ β₁ β₂ γ₂ hβ₁ hβ₂ hγ₂ hβ₂reg hzero₁ hzero₂
    hmaxA hmaxB hmaxC hmaxD hmaxE hdivB hdivE H₁ H₂ H₃ H₄ H₅
  have hq6 : 6 ≤ q := by omega
  have hq8 : 8 ≤ q := by omega
  have hq_ge_p : q₀p ≤ q := by omega
  have hq_ge_a : q₀a ≤ q := by omega
  have hq_ge_b : q₀b ≤ q := by omega
  have hq_ge_n : q₀n ≤ q := by omega
  have hL2 : (2:ℝ) ≤ Real.log (q:ℝ) := by
    have h1 : Real.log 8 ≤ Real.log (q:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hq8)
    have h3 : Real.log (8:ℝ) = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
    rw [h3] at h1
    have h4 : (2:ℝ) < 3 * Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    linarith
  have hLpos : 0 < Real.log (q:ℝ) := by linarith
  -- primitive characters are non-principal
  have hneA : (χ₁ * χ₂).primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₁χ₂
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ * χ₂), h]
    exact DirichletCharacter.changeLevel_one (χ₁ * χ₂).conductor_dvd_level
  have hneB : (χ₂ * χ₂).primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₂χ₂
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₂ * χ₂), h]
    exact DirichletCharacter.changeLevel_one (χ₂ * χ₂).conductor_dvd_level
  have hneC : (χ₁ * (χ₂ * χ₂)).primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₁χ₂χ₂
    rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ * (χ₂ * χ₂)), h]
    exact DirichletCharacter.changeLevel_one (χ₁ * (χ₂ * χ₂)).conductor_dvd_level
  have hneD : χ₁.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₁
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, h]
    exact DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level
  have hneE : χ₂.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ₂
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₂, h]
    exact DirichletCharacter.changeLevel_one χ₂.conductor_dvd_level
  have habsβ₂ : |β₂ - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    rw [abs_sub_comm]; exact hβ₂reg
  have hβ₂_ge : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ β₂ := by
    have h : 1 - β₂ ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) :=
      (abs_le.mp hβ₂reg).2
    linarith only [h]
  -- window thresholds
  have hT_C : |((β₂:ℂ) : ℂ).im| + δ ≤ 1 := by
    have h : ((β₂:ℂ) : ℂ).im = 0 := by simp
    rw [h, abs_zero]; linarith only [hδ1]
  have hT_D : |(((β₂:ℂ) + (γ₂:ℂ)*Complex.I) : ℂ).im| + δ ≤ |γ₂| + 1 := by
    have h : (((β₂:ℂ) + (γ₂:ℂ)*Complex.I) : ℂ).im = γ₂ := by simp
    rw [h]; linarith [abs_nonneg γ₂, hδ1]
  have hγ₂' : |γ₂ + γ₂| = 2 * |γ₂| := by
    rw [show γ₂ + γ₂ = 2 * γ₂ by ring, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hT_B : |(((β₂:ℂ) + ((γ₂:ℂ)+(γ₂:ℂ))*Complex.I) : ℂ).im| + δ ≤ 2 * |γ₂| + 1 := by
    have h : (((β₂:ℂ) + ((γ₂:ℂ)+(γ₂:ℂ))*Complex.I) : ℂ).im = γ₂ + γ₂ := by simp
    rw [h, hγ₂']; linarith [hδ1]
  -- window transfers
  have hzwE : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|((β₂:ℂ) : ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (((β₂:ℂ) : ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁:ℂ) → u.re ≤ ((β₂:ℂ) : ℂ).re :=
    Work.LinnikAreas.DhRepel.window_hzero_of_Lzero_T χ₁.primitiveCharacter hneD hδ1 hT_C (by simp) hmaxE
  have hzwD : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re :=
    Work.LinnikAreas.DhRepel.window_le_of_Lzero_T χ₂.primitiveCharacter hneE hδ1 hT_D (by simp) hmaxD
  have hzwA : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction (χ₁*χ₂).primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re :=
    Work.LinnikAreas.DhRepel.window_le_of_Lzero_T (χ₁*χ₂).primitiveCharacter hneA hδ1 hT_D (by simp) hmaxA
  have hzwB : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction (χ₂*χ₂).primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + ((((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re :=
    Work.LinnikAreas.DhRepel.window_le_of_Lzero_T (χ₂*χ₂).primitiveCharacter hneB hδ1 hT_B (by simp) hmaxB
  have hzwC : ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction (χ₁*(χ₂*χ₂)).primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + ((((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re :=
    Work.LinnikAreas.DhRepel.window_le_of_Lzero_T (χ₁*(χ₂*χ₂)).primitiveCharacter hneC hδ1 hT_B (by simp) hmaxC
  -- divisor transfers
  have hβ₁_mem : (β₁:ℂ) ∈ Metric.closedBall 0 2 := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs]
    have h1 : -(δ) ≤ 1 - β₁ := (abs_le.mp hβ₁).1
    have h2 : 1 - β₁ ≤ δ := (abs_le.mp hβ₁).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hdivE2 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|((β₂:ℂ) : ℂ).im| + 2))) (β₁:ℂ) ≠ 0 := by
    have h : ((β₂:ℂ) : ℂ).im = 0 := by simp
    rw [h, abs_zero, zero_add]
    rw [← Work.LinnikAreas.DhRepel.divisor_closedBall_congr (R := 2) (R' := |γ₂| + 2)
      (by linarith [abs_nonneg γ₂])
      (fun z _ => (DirichletCharacter.differentiable_completedLFunction hneD).analyticAt z) hβ₁_mem]
    exact hdivE
  have hdivD' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
        (Metric.closedBall 0 (|(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| + 2))) ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) ≠ 0 := by
    have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im = γ₂ := by simp
    rw [h]; exact hdivB
  -- non-negativity of the Laplace integral at the exceptional zero of χ₁
  have hρnn : 0 ≤ (∫ t in (0:ℝ)..x₀,
      Complex.exp (-((((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))) * (t:ℂ))) * ((f t:ℝ):ℂ)).re := by
    have hcast : ((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ)) = (((β₂ - β₁) * Real.log (q:ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast]
    exact Work.LinnikAreas.DhRepel.laplaceIntegral_re_nonneg hx₀.le hfnn
  have hwin1 : ‖(1:ℂ) + (((β₂:ℂ):ℂ).im : ℂ) * Complex.I - (β₁:ℂ)‖ ≤ δ := by
    have h1 : (((β₂:ℂ):ℂ).im : ℂ) = 0 := by simp
    rw [h1, zero_mul, add_zero]
    have h2 : ‖(1:ℂ) - (β₁:ℂ)‖ = |1 - β₁| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [h2]; exact hβ₁
  have hwin2 : ‖(1:ℂ) + ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) * Complex.I - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I)‖ ≤ δ := by
    have h1 : ((((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im : ℂ) = (γ₂:ℂ) := by
      have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im = γ₂ := by simp
      rw [h]
    rw [h1]
    have h2 : ‖(1:ℂ) + (γ₂:ℂ)*Complex.I - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I)‖ = |1 - β₂| := by
      rw [show (1:ℂ) + (γ₂:ℂ)*Complex.I - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) = ((1 - β₂ : ℝ):ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [h2]; exact hβ₂
  -- the s-conditions
  have hsim_1 : |((β₂:ℂ):ℂ).im| ≤ 10 * Real.log (q:ℝ) := by
    have h : ((β₂:ℂ):ℂ).im = 0 := by simp
    rw [h, abs_zero]; linarith [hLpos]
  have hsim_2 : |(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im| ≤ 10 * Real.log (q:ℝ) := by
    have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).im = γ₂ := by simp
    rw [h]
    have h2 : |γ₂| ≤ 2 * |γ₂| + 1 := by linarith [abs_nonneg γ₂]
    linarith [hγ₂, h2]
  have hsim_B : |(((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im| ≤ 10 * Real.log (q:ℝ) := by
    have h : (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).im = γ₂ + γ₂ := by simp
    rw [h, hγ₂']; linarith [hγ₂]
  have hsre_1 : |((β₂:ℂ):ℂ).re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h : ((β₂:ℂ):ℂ).re = β₂ := by simp
    rw [h]; exact habsβ₂
  have hsre_2 : |(((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re = β₂ := by simp
    rw [h]; exact habsβ₂
  have hsre_B : |(((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h : (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re = β₂ := by simp
    rw [h]; exact habsβ₂
  have hge_1 : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ ((β₂:ℂ):ℂ).re := by
    have h : ((β₂:ℂ):ℂ).re = β₂ := by simp
    rw [h]; exact hβ₂_ge
  have hge_2 : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re := by
    have h : (((β₂:ℂ)+(γ₂:ℂ)*Complex.I):ℂ).re = β₂ := by simp
    rw [h]; exact hβ₂_ge
  have hge_B : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re := by
    have h : (((β₂:ℂ)+((γ₂:ℂ)+(γ₂:ℂ))*Complex.I):ℂ).re = β₂ := by simp
    rw [h]; exact hβ₂_ge
  -- the six bounds
  have hb0 := hq₀p (q := q) hq_ge_p (β := β₂) (lam := Real.log (q:ℝ) * (1 - β₂)) rfl habsβ₂
  have hb1 := hq₀n (q := q) hq_ge_n χ₁ hχ₁ hsre_1 hsim_1 hge_1 H₁ hdivE2 hwin1 hρnn hzwE
  have hb2 := hq₀b (q := q) hq_ge_b χ₂ hχ₂ hsre_2 hsim_2 hge_2 H₂ hdivD' hwin2 hzwD
  have hb3 := hq₀a (q := q) hq_ge_a (χ₁ * χ₂) hχ₁χ₂ hsre_2 hsim_2 hge_2 H₃ hzwA
  have hb4 := hq₀a (q := q) hq_ge_a (χ₂ * χ₂) hχ₂χ₂ hsre_B hsim_B hge_B H₄ hzwB
  have hb5 := hq₀a (q := q) hq_ge_a (χ₁ * (χ₂ * χ₂)) hχ₁χ₂χ₂ hsre_B hsim_B hge_B H₅ hzwC
  -- the six-term positivity
  have h6 := Work.ZeroFreeTables.ksum_positivity_six (q := q) (β := β₂) (γ := γ₂)
    hfnn hx₀ hLpos hsupp χ₁ χ₂ hreal hk
  -- integral rewrites
  have hRe1 : (∫ t in (0:ℝ)..x₀,
      Complex.exp (-((((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))) * (t:ℂ))) * ((f t:ℝ):ℂ)).re
      = ∫ t in (0:ℝ)..x₀,
          Real.exp (-((Real.log (q:ℝ) * (1 - β₁)) - (Real.log (q:ℝ) * (1 - β₂))) * t) * f t := by
    have hz1 : (((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))).im = 0 := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_im]
    rw [Work.LinnikAreas.DhRepel.re_integral_exp_ofReal (z := ((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))) hz1 f]
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    have h : (((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))).re = (β₂ - β₁) * Real.log (q:ℝ) := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
    have harg : -((((β₂:ℂ) - (β₁:ℂ)) * (Real.log (q:ℝ))).re * t)
        = -((Real.log (q:ℝ) * (1 - β₁)) - (Real.log (q:ℝ) * (1 - β₂))) * t := by
      rw [h]; ring
    rw [harg]
  have hRe2 : (∫ t in (0:ℝ)..x₀,
      Complex.exp (-(((((β₂:ℂ)+(γ₂:ℂ)*Complex.I) - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I)) * (Real.log (q:ℝ))) * (t:ℂ))) * ((f t:ℝ):ℂ)).re
      = ∫ t in (0:ℝ)..x₀, f t := by
    have hzero : ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) - ((β₂:ℂ)+(γ₂:ℂ)*Complex.I) = 0 := sub_self _
    simp only [hzero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  -- final assembly
  rw [hRe1] at hb1
  rw [hRe2] at hb2
  exact lemma8_7_assembly (L := Real.log (q:ℝ)) (f0 := f 0)
    hLpos hk h6 hb0 hb1 hb2 hb3 hb4 hb5

end

end Work.ZeroFreeTables
