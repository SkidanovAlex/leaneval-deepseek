/-
# `Work.FQCInputs.continuous_theta_apply`

The normalised principal solution `θ_t = principal (muQC d fl hpetal.Pg t)` of the
quasiconformal deformation of the attracting Écalle cylinder is **continuous in the deformation
parameter**, pointwise at every `z : ℂ`:

`Continuous fun t : ℝ => (principal (muQC d fl hpetal.Pg t) : ℂ → ℂ) z`.

This is the consumer of the MRMT-continuity input `Work.FQCInputs.PrincipalContinuity` (S1 of the
lead's design, `Submission/Work/NOTES_LEAD_mandelbar_simple.md` §3): the continuation argument for
the simplicity of the transported parabolic point reads off `iteratedDeriv 2 (F (θ_t c)) (θ_t z₁)`
as a continuous function of `t`.

The proof is the standard sequence reduction (`tendsto_nhds_iff_seq_tendsto`, `ℝ` being a
Fréchet–Urysohn space).  Given `u j → t₀`:

* **admissibility** — every `muQC d fl Pg t` is admissible (`Work.FQC.muQC_admissible_pg`);
* **support** — the support is contained in the fixed ball `closedBall 0 (max 2 ‖c‖)`, uniformly
  in `t` (`Work.FQCInputs.support_muQC_subset_closedBall`);
* **uniform bound** — the *pointwise* bound `‖muQC d fl Pg t z‖ ≤ |t| / √(1+t²)`
  (`norm_muQC_le` below, the public form of the `private` bound inside
  `Submission/Work/FQC/muQC_admissible_pg.lean`) is monotone in `|t|`
  (`div_sqrt_le_of_abs_le`), and a convergent real sequence is bounded, so along a *tail* of `u`
  one gets a single constant `k = M / √(1+M²) < 1` (`div_sqrt_lt_one`) bounding all the
  coefficients a.e.  Discarding the finitely many initial terms loses nothing for the `atTop`
  limit (`Filter.tendsto_add_atTop_iff_nat`);
* **a.e. convergence** — the coefficients depend continuously on `t` *pointwise*
  (`Work.FQCInputs.continuous_muQC_apply`), hence converge along the sequence at every `z`, hence
  a.e.

Then S1 (`PrincipalContinuity.tendsto_apply`) gives convergence of the principal solutions at `z`.
-/
import Mathlib
import Submission.Work.FQCInputs.Defs
import Submission.Work.FQCInputs.PrincipalContinuity
import Submission.Work.FQCInputs.continuous_muQC_apply
import Submission.Work.FQCInputs.support_muQC_subset_closedBall
import Submission.Work.FQC.muQC_admissible_pg
import Submission.Work.FQC.muQC_aux_beltrami

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQCInputs

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## 1. The pull-backs do not increase the modulus

These are the `private` estimates of `Submission/Work/FQC/muQC_admissible_pg.lean`, restated here
so that the pointwise bound on the deformation coefficient is available in this file. -/

private theorem norm_mul_div_star_le (a b : ℂ) : ‖a * b / star b‖ ≤ ‖a‖ := by
  rw [norm_div, norm_mul, norm_star, mul_div_assoc]
  exact mul_le_of_le_one_right (norm_nonneg a) (div_self_le_one ‖b‖)

private theorem norm_pullAnti_le (μ f : ℂ → ℂ) (z : ℂ) :
    ‖Work.FQC.pullAnti μ f z‖ ≤ ‖μ (f z)‖ := by
  have h := norm_mul_div_star_le (star (μ (f z))) (Work.MRMT.dzbar f z)
  rw [Work.FQC.pullAnti]
  simpa only [norm_star] using h

private theorem norm_pullHolo_le (ν φ : ℂ → ℂ) (z : ℂ) :
    ‖Work.FQC.pullHolo ν φ z‖ ≤ ‖ν (φ z)‖ := by
  have h := norm_mul_div_star_le (ν (φ z)) (star (deriv φ z))
  rw [Work.FQC.pullHolo]
  simpa only [star_star] using h

private theorem norm_pullHoloOn_le (ν φ : ℂ → ℂ) (P : Set ℂ) (z : ℂ) :
    ‖Work.FQC.pullHoloOn ν φ P z‖ ≤ ‖ν (φ z)‖ := by
  unfold Work.FQC.pullHoloOn
  split
  · exact norm_pullHolo_le ν φ z
  · simp

private theorem norm_pullAntiIter_le (f : ℂ → ℂ) (n : ℕ) (μ : ℂ → ℂ) (z : ℂ) :
    ‖Work.FQC.pullAntiIter f n μ z‖ ≤ ‖μ ((f^[n]) z)‖ := by
  induction n generalizing z with
  | zero => simp [Work.FQC.pullAntiIter]
  | succ n ih =>
      rw [Work.FQC.pullAntiIter_succ]
      calc ‖Work.FQC.pullAnti (Work.FQC.pullAntiIter f n μ) f z‖
            ≤ ‖Work.FQC.pullAntiIter f n μ (f z)‖ := norm_pullAnti_le _ _ _
        _ ≤ ‖μ ((f^[n]) (f z))‖ := ih (f z)
        _ = ‖μ ((f^[n+1]) z)‖ := by rw [Function.iterate_succ_apply]

/-- **The pointwise bound on the deformation coefficient.**  The modulus of `muQC d fl P t z` is
at most the modulus `|t|/√(1+t²)` of the dilatation of the MNS twist `ℓ_t` — the pull-backs along
the Fatou coordinate and along the dynamics never increase the modulus.  This is the public form
of the bound used inside `Work.FQC.muQC_admissible_pg`. -/
theorem norm_muQC_le {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (P : Set ℂ) (t : ℝ) (z : ℂ) :
    ‖Work.FQC.muQC d fl P t z‖ ≤ |t| / Real.sqrt (1 + t^2) := by
  by_cases h : ∃ n : ℕ, (Tantibar c)^[n] z ∈ P
  · rw [Work.FQC.muQC_of_mem d (show z ∈ Work.FQC.basin d P from h)]
    calc ‖Work.FQC.pullAntiIter (Tantibar c) (Nat.find h)
            (Work.FQC.pullHoloOn (Work.MRMT.beltramiOf (Work.FQC.ell t)) fl.φa P) z‖
        ≤ ‖Work.FQC.pullHoloOn (Work.MRMT.beltramiOf (Work.FQC.ell t)) fl.φa P
            ((Tantibar c)^[Nat.find h] z)‖ :=
          norm_pullAntiIter_le _ _ _ _
      _ ≤ ‖Work.MRMT.beltramiOf (Work.FQC.ell t) (fl.φa
            ((Tantibar c)^[Nat.find h] z))‖ :=
          norm_pullHoloOn_le _ _ _ _
      _ ≤ |t| / Real.sqrt (1 + t^2) := Work.FQC.beltramiOf_ell_le t _
  · rw [Work.FQC.muQC_of_notMem d h]
    simpa using div_nonneg (abs_nonneg t) (Real.sqrt_nonneg _)

/-! ## 2. The ratio `|t|/√(1+t²)` is monotone, and always `< 1` -/

/-- The bound `|t|/√(1+t²)` of `norm_muQC_le` is monotone in `|t|`. -/
theorem div_sqrt_le_of_abs_le {t M : ℝ} (hM : 0 ≤ M) (ht : |t| ≤ M) :
    |t| / Real.sqrt (1 + t^2) ≤ M / Real.sqrt (1 + M^2) := by
  have h1 : 0 < Real.sqrt (1 + t^2) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt (1 + M^2) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_div_iff₀ h1 h2]
  have ht2 : t^2 ≤ M^2 := by
    have := pow_le_pow_left₀ (abs_nonneg t) ht 2
    rwa [sq_abs] at this
  have hsq : (|t| * Real.sqrt (1 + M ^ 2)) ^ 2 ≤ (M * Real.sqrt (1 + t ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), sq_abs]
    nlinarith
  have hL : 0 ≤ |t| * Real.sqrt (1 + M ^ 2) := mul_nonneg (abs_nonneg t) (Real.sqrt_nonneg _)
  have hR : 0 ≤ M * Real.sqrt (1 + t ^ 2) := mul_nonneg hM (Real.sqrt_nonneg _)
  have := sq_le_sq.mp hsq
  rwa [abs_of_nonneg hL, abs_of_nonneg hR] at this

/-- `M/√(1+M²) < 1` for every real `M`: this is the constant `k < 1` of the admissibility
condition, uniformly for the whole (bounded) range of the deformation parameter. -/
theorem div_sqrt_lt_one (M : ℝ) : M / Real.sqrt (1 + M^2) < 1 := by
  rcases lt_or_ge M 0 with hM | hM
  · have hpos : 0 < Real.sqrt (1 + M^2) := Real.sqrt_pos.mpr (by positivity)
    have : M / Real.sqrt (1 + M^2) < 0 := div_neg_of_neg_of_pos hM hpos
    linarith
  · rw [div_lt_one (Real.sqrt_pos.mpr (by positivity)), Real.lt_sqrt hM]
    nlinarith

/-! ## 3. Continuity of the normalised principal solution in the parameter -/

theorem continuous_theta_apply (hS1 : Work.FQCInputs.PrincipalContinuity) {c : ℂ}
    (d : Work.EL.RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) (z : ℂ) :
    Continuous fun t : ℝ =>
      (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t) : ℂ → ℂ) z := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro u hu
  change Filter.Tendsto
    (fun j => (Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg (u j)) : ℂ → ℂ) z)
    Filter.atTop (nhds ((Work.MRMT.Found.principal (Work.FQC.muQC d fl hpetal.Pg t₀) : ℂ → ℂ) z))
  -- a uniform bound for the parameter along the sequence: `M = |t₀| + 1`
  set M : ℝ := |t₀| + 1 with hMdef
  have hM : 0 ≤ M := by rw [hMdef]; positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j ≥ N, |u j| ≤ M := by
    have h1 : ∀ᶠ j : ℕ in Filter.atTop, |u j| ≤ M := by
      have hdist : ∀ᶠ j : ℕ in Filter.atTop, dist (u j) t₀ < 1 :=
        (Metric.tendsto_nhds.mp hu) 1 zero_lt_one
      filter_upwards [hdist] with j hj
      rw [Real.dist_eq] at hj
      have h2 : |u j| ≤ |u j - t₀| + |t₀| := by
        simpa only [sub_add_cancel] using abs_add_le (u j - t₀) t₀
      rw [hMdef]
      linarith
    exact Filter.eventually_atTop.mp h1
  -- finitely many terms are irrelevant for the `atTop` limit
  refine (Filter.tendsto_add_atTop_iff_nat N).mp ?_
  -- the common bound `k < 1` and the hypotheses of S1
  have hb : ∀ j : ℕ, ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖Work.FQC.muQC d fl hpetal.Pg (u (j + N)) w‖ ≤ M / Real.sqrt (1 + M^2) := by
    intro j
    refine Filter.Eventually.of_forall (fun w => ?_)
    exact le_trans (norm_muQC_le d fl hpetal.Pg (u (j + N)) w)
      (div_sqrt_le_of_abs_le hM (hN (j + N) (Nat.le_add_left N j)))
  have hb₀ : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      ‖Work.FQC.muQC d fl hpetal.Pg t₀ w‖ ≤ M / Real.sqrt (1 + M^2) := by
    refine Filter.Eventually.of_forall (fun w => ?_)
    have ht₀ : |t₀| ≤ M := by rw [hMdef]; exact le_add_of_nonneg_right zero_le_one
    exact le_trans (norm_muQC_le d fl hpetal.Pg t₀ w) (div_sqrt_le_of_abs_le hM ht₀)
  have hT : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun j => Work.FQC.muQC d fl hpetal.Pg (u (j + N)) w) Filter.atTop
        (nhds (Work.FQC.muQC d fl hpetal.Pg t₀ w)) := by
    refine Filter.Eventually.of_forall (fun w => ?_)
    exact (Work.FQCInputs.continuous_muQC_apply d fl hpetal.Pg w).continuousAt.tendsto.comp
      (hu.comp (Filter.tendsto_add_atTop_nat N))
  exact hS1.tendsto_apply (μs := fun j => Work.FQC.muQC d fl hpetal.Pg (u (j + N)))
    (μ := Work.FQC.muQC d fl hpetal.Pg t₀)
    (fun j => Work.FQC.muQC_admissible_pg d fl hpetal _)
    (Work.FQC.muQC_admissible_pg d fl hpetal t₀)
    (max 2 ‖c‖) (M / Real.sqrt (1 + M^2)) (div_sqrt_lt_one M)
    (fun j => Work.FQCInputs.support_muQC_subset_closedBall d fl hpetal _)
    (Work.FQCInputs.support_muQC_subset_closedBall d fl hpetal t₀)
    hb hb₀ hT z

end Work.FQCInputs

end
