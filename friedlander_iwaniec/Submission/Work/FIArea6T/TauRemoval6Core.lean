/-
# `Submission.Work.FIArea6T.TauRemoval6Core` — the τ-removal assembled from its four inputs

This module proves `Work.FITop4.TauRemoval6` from the four proved pieces of the lane:

* `hT2` — the L² Schur bound `Work.FIArea6T.TcutBil_le_polar`;
* `hT3` — the clean second moment `Work.FIArea6T.cleanCoeff_sq_mass_le`;
* `hT4` — the mass of the (5.9)-complement `Work.FIArea6T.cleanTau_mass_le`;
* the sesquilinear expansion `Work.FIArea6T.Tcut_sesq` of the (10.13) form.

The assembly is the one of `FIArea6/AREA6_CONTRACT_LEAD.md` §3.3, T5: with `δ = β − tauCut Pa β`,

  `Tcut (tauCut Pa β) = TcutBil β β − TcutBil β δ − TcutBil δ β + TcutBil δ δ`,

the triangle inequality gives `‖·‖ ≤ 3Λ‖β‖₂‖δ‖₂`, and the three bounds multiply as in
`Work.FIArea6T.tau_arith_log`.
-/
import Mathlib
import Submission.Work.FIArea6T.Defs
import Submission.Work.FIArea6T.Support
import Submission.Work.FIArea6T.LogArith
import Submission.Work.FIArea6T.Tcut_sesq

set_option autoImplicit false

namespace Work.FIArea6T

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

theorem tauRemoval6_core
    (C3 : ℝ) (hC3 : 0 < C3)
    (hT3 : ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsCleanCoeff6 Pa φ z0 β →
      ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2
        ≤ C3 * Pa.N * (Real.log (2 + Pa.N)) ^ 7)
    (x0τ : ℝ)
    (hT4 : ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      x0τ ≤ (Pa.x : ℝ) → Pa.τ = Work.FITop4.tauOf Pa.x Work.FITop4.Asave →
      Work.FITop4.IsCleanCoeff6 Pa φ z0 β →
      ∑ z ∈ Work.FITop.boxN Pa, ‖β z - Work.FITop4.tauCut Pa β z‖ ^ 2
        ≤ Pa.N * (Real.log Pa.N) ^ (-(4 * 10 ^ 9 : ℝ)))
    (hT2 : ∀ (Pa : Work.FITop.Params) (cut : GaussianInt → GaussianInt → ℕ → ℝ)
        (u v : GaussianInt → ℂ) (φ : ℝ),
      (∀ z1 z2 d, |cut z1 z2 d| ≤ 1) →
      (∀ z, u z ≠ 0 → Work.FITop4.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z)) →
      (∀ z, v z ≠ 0 → Work.FITop4.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z)) →
      Pa.θ ≤ 1 → 3 ≤ Pa.N →
      ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut u v‖
        ≤ 10 ^ 4 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 2
            * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖u z‖ ^ 2)
            * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖v z‖ ^ 2)) :
    Work.FITop4.TauRemoval6 := by
  refine ⟨3 * 10 ^ 4 * Real.sqrt C3 * (1 + Real.log 3) ^ 6, max x0τ (Real.exp 12), ?_, ?_⟩
  · have h3 : 0 < 3 * (10 : ℝ) ^ 4 * Real.sqrt C3 := by
      have h1 : 0 < Real.sqrt C3 := Real.sqrt_pos.mpr hC3
      positivity
    have h4 : 0 < (1 + Real.log 3) ^ 6 := by positivity
    have h := mul_pos h3 h4
    nlinarith [h]
  · intro Pa hx hpin cut hcut φ z0 β hβ
    have hxτ : x0τ ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx
    have hxe : Real.exp 12 ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx
    have hN3 : 3 ≤ Pa.N := Work.FIArea6T.threshold_N3 hxe
    have hN1 : (1 : ℝ) ≤ Pa.N := by linarith
    have hN0 : (0 : ℝ) ≤ Pa.N := by linarith
    have hθ1 : Pa.θ ≤ 1 := Work.FIArea6.theta_le_one Pa
    have hθ0 : (0 : ℝ) ≤ Pa.θ := Pa.hθ0.le
    have hM1 : 1 ≤ Real.log Pa.N := Work.FIArea6T.threshold_logN hxe
    have hL1 : 1 ≤ Real.log (2 + Pa.N) := Work.FIArea6T.log_two_add_ge_one hN3
    have hLM : Real.log (2 + Pa.N) ≤ (1 + Real.log 3) * Real.log Pa.N :=
      Work.FIArea6T.log_two_add_le hN1 hM1
    -- the (5.9)-complement
    let δ : GaussianInt → ℂ := Work.FIArea6T.tauCompl Pa β
    have hsuppβ : ∀ z, β z ≠ 0 →
        Work.FITop4.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z) :=
      fun z hz => ⟨Work.FIArea6T.IsCleanCoeff6.support hβ hz,
        Work.FIArea6T.IsCleanCoeff6.squarefree_gnorm hβ hz⟩
    have hsuppδ : ∀ z, δ z ≠ 0 →
        Work.FITop4.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z) := by
      intro z hz
      exact hsuppβ z (Work.FIArea6T.tauCompl_ne_zero_imp hz)
    -- the three Schur bounds
    have hD := hT2 Pa cut δ δ φ hcut hsuppδ hsuppδ hθ1 hN3
    have hB := hT2 Pa cut β δ φ hcut hsuppβ hsuppδ hθ1 hN3
    have hC := hT2 Pa cut δ β φ hcut hsuppδ hsuppβ hθ1 hN3
    -- the two masses
    have hmβ := hT3 Pa φ z0 β hβ
    have hmδ := hT4 Pa φ z0 β hxτ hpin hβ
    -- the L² norms
    let Sβ : ℝ := Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2)
    let Sδ : ℝ := Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖δ z‖ ^ 2)
    have hSβ0 : 0 ≤ Sβ := Real.sqrt_nonneg _
    have hSδ0 : 0 ≤ Sδ := Real.sqrt_nonneg _
    have hSδβ : Sδ ≤ Sβ := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun z _ => ?_)
      exact pow_le_pow_left₀ (norm_nonneg _) (Work.FIArea6T.norm_tauCompl_le Pa β z) 2
    have hbSβ : Sβ ≤ Real.sqrt C3 * Real.sqrt Pa.N * (Real.log (2 + Pa.N)) ^ 4 := by
      refine le_trans (Real.sqrt_le_sqrt hmβ) ?_
      exact Work.FIArea6T.sqrt_sq_mass_le hC3.le hN0 hL1
    have hbSδ : Sδ ≤ Real.sqrt Pa.N * (Real.log Pa.N) ^ (-(2 * 10 ^ 9 : ℝ)) := by
      refine le_trans (Real.sqrt_le_sqrt hmδ) ?_
      exact Work.FIArea6T.sqrt_mass_le hN0 (Real.log_nonneg hN1)
    -- the expansion of the (10.13) form
    have hexp : Work.FITop4.Tcut (Work.FITop.radN Pa) cut (Work.FITop4.tauCut Pa β)
          - Work.FITop4.Tcut (Work.FITop.radN Pa) cut β
        = Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ δ
          - Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut β δ
          - Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ β := by
      show Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut (fun z => Work.FITop4.tauCut Pa β z)
            (fun z => Work.FITop4.tauCut Pa β z)
          - Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut β β
          = Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ δ
            - Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut β δ
            - Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ β
      rw [Work.FIArea6T.tauCut_eq_sub_tauCompl, Work.FIArea6T.Tcut_sesq]
      ring
    -- the Schur factor
    have hK0 : 0 ≤ 10 ^ 4 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 2 := by positivity
    have hmain : ‖Work.FITop4.Tcut (Work.FITop.radN Pa) cut (Work.FITop4.tauCut Pa β)
          - Work.FITop4.Tcut (Work.FITop.radN Pa) cut β‖
        ≤ 3 * (10 ^ 4 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 2) * Sβ * Sδ := by
      rw [hexp]
      have htri : ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ δ
            - Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut β δ
            - Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ β‖
          ≤ ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ δ‖
            + ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut β δ‖
            + ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ β‖ := by
        have h1 : ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ δ
              - Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut β δ
              - Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ β‖
            ≤ ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ δ
              - Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut β δ‖
              + ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ β‖ :=
          norm_sub_le _ _
        have h2 : ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ δ
              - Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut β δ‖
            ≤ ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut δ δ‖
              + ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut β δ‖ :=
          norm_sub_le _ _
        linarith [h1, h2]
      refine le_trans htri ?_
      have h4 : Sδ * Sδ ≤ Sβ * Sδ := mul_le_mul_of_nonneg_right hSδβ hSδ0
      have h4' : 10 ^ 4 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 2 * (Sδ * Sδ)
          ≤ 10 ^ 4 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 2 * (Sβ * Sδ) :=
        mul_le_mul_of_nonneg_left h4 hK0
      nlinarith [hD, hB, hC, h4', hK0]
    refine le_trans hmain ?_
    have hK20 : 0 ≤ 3 * (10 ^ 4 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 2) := by positivity
    have hbound : 3 * (10 ^ 4 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 2) * Sβ * Sδ
        ≤ 3 * (10 ^ 4 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 2)
          * (Real.sqrt C3 * Real.sqrt Pa.N * (Real.log (2 + Pa.N)) ^ 4)
          * (Real.sqrt Pa.N * (Real.log Pa.N) ^ (-(2 * 10 ^ 9 : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hbSβ hK20) hbSδ hSδ0 (by positivity)
    refine le_trans hbound ?_
    exact Work.FIArea6T.tau_arith_log C3 Pa.θ Pa.N hθ0 hθ1 hN0 hL1 hM1 hLM

end

end Work.FIArea6T
