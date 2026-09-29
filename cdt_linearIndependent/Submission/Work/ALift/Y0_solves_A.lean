import Mathlib
import Submission.Work.ALift.defs
import Submission.Work.ALift.ode_hold_A
import Submission.Work.ALift.hasDerivAt_HU
import Submission.Work.ALift.Phi_avoid

/-!
# Area ALift — the initial solution `Y₀ = (U₀, U₁) ∘ Φ` of the pulled-back system

For `‖z‖ ≤ 1/25` the lift `Φ` takes values in `‖Φ z‖ ≤ 9/10 < 10/11`, so both `U₀` and `U₁` are
defined and holomorphic at `Φ z` (`hasDerivAt_HU`); the chain rule makes `Y₀ = (U₀ ∘ Φ, U₁ ∘ Φ)`
holomorphic on the disc `‖z‖ < 1/25`.

On the annulus `1/31 < ‖z‖ < 1/25` the system identity holds: the first component is
`deriv Φ z · U₁(Φ z)` (the first row of `sysA`), and the second is `deriv Φ z · U₂(Φ z)`, which the
ODE `HU_ode` solved for `U₂` (`U₂ = (rhs - Q·U₁ - R·U₀)/P`, legitimate because `Φ z` avoids the
zero `0` of `P`, `Phi_avoid`) turns into the second row of `sysA` plus the inhomogeneity `sysb`.
-/

open Metric

namespace Work.ALift

open Submission.CDTPlan

noncomputable section

theorem Y0_solves_A (a b c : ℤ) (hRel : ARel a b c) (hN : ANumerics) (Φ : ℂ → ℂ)
    (hL : LiftData phiA Φ)
    (hsmall : ∀ z : ℂ, ‖z‖ ≤ rA1 → ‖Φ z‖ ≤ 9 / 10) :
    DifferentiableOn ℂ (Y0v a b c Φ) (ball (0 : ℂ) rA1) ∧
      (∀ z : ℂ, rA0 < ‖z‖ → ‖z‖ < rA1 →
        HasDerivAt (Y0v a b c Φ)
          (fun i => ∑ j, sysA Φ z i j * Y0v a b c Φ z j + sysb b c Φ z i) z) := by
  have hrA0 : rA0 = 1 / 31 := rfl
  have hrA1 : rA1 = 1 / 25 := rfl
  have hav : ∀ z : ℂ, 1 / 31 < ‖z‖ → ‖z‖ < 1 → Pd (Φ z) ≠ 0 ∧ (1 - Φ z) ≠ 0 :=
    Phi_avoid hN Φ hL
  have hΦdiff : DifferentiableOn ℂ Φ (ball (0 : ℂ) 1) := hL.1
  -- differentiability of `U₀ ∘ Φ` and `U₁ ∘ Φ` on the disc `‖z‖ < rA1`
  have hU0d : DifferentiableOn ℂ (fun z => HU0 a b c (Φ z)) (ball (0 : ℂ) rA1) := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz
    have hq : ‖Φ z‖ ≤ 9 / 10 := hsmall z hz.le
    have hzmem : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right]; linarith
    have hΦat : DifferentiableAt ℂ Φ z := hΦdiff.differentiableAt (isOpen_ball.mem_nhds hzmem)
    have hU : DifferentiableAt ℂ (HU0 a b c) (Φ z) :=
      ((hasDerivAt_HU a b c hRel (Φ z) hq).1).differentiableAt
    exact (hU.comp z hΦat).differentiableWithinAt
  have hU1d : DifferentiableOn ℂ (fun z => HU1 a b c (Φ z)) (ball (0 : ℂ) rA1) := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz
    have hq : ‖Φ z‖ ≤ 9 / 10 := hsmall z hz.le
    have hzmem : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right]; linarith
    have hΦat : DifferentiableAt ℂ Φ z := hΦdiff.differentiableAt (isOpen_ball.mem_nhds hzmem)
    have hU : DifferentiableAt ℂ (HU1 a b c) (Φ z) :=
      ((hasDerivAt_HU a b c hRel (Φ z) hq).2).differentiableAt
    exact (hU.comp z hΦat).differentiableWithinAt
  constructor
  · unfold Y0v
    rw [differentiableOn_pi]
    intro i
    fin_cases i
    · simpa only [Fin.isValue, Fin.zero_eta, reduceIte] using hU0d
    · show DifferentiableOn ℂ (fun z => HU1 a b c (Φ z)) (ball (0 : ℂ) rA1)
      exact hU1d
  · intro z hzr hz1
    have hq : ‖Φ z‖ ≤ 9 / 10 := hsmall z hz1.le
    have hzmem : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right]; linarith
    have hΦat : HasDerivAt Φ (deriv Φ z) z :=
      (hΦdiff.differentiableAt (isOpen_ball.mem_nhds hzmem)).hasDerivAt
    obtain ⟨hd0, hd1⟩ := hasDerivAt_HU a b c hRel (Φ z) hq
    have hc0 : HasDerivAt (fun z => HU0 a b c (Φ z)) (HU1 a b c (Φ z) * deriv Φ z) z :=
      hd0.comp z hΦat
    have hc1 : HasDerivAt (fun z => HU1 a b c (Φ z)) (HU2 a b c (Φ z) * deriv Φ z) z :=
      hd1.comp z hΦat
    have hzr' : 1 / 31 < ‖z‖ := by rw [← hrA0]; exact hzr
    have hPd : Pd (Φ z) ≠ 0 := (hav z hzr' (by linarith)).1
    have hU2 : HU2 a b c (Φ z)
        = (rhsA b c (Φ z) - Qd (Φ z) * HU1 a b c (Φ z)
            - Rd (Φ z) * HU0 a b c (Φ z)) / Pd (Φ z) := by
      rw [eq_div_iff hPd]
      have hode := HU_ode a b c hRel (Φ z) hq
      linear_combination hode
    refine hasDerivAt_pi.mpr ?_
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · refine hc0.congr_deriv ?_
      rw [Fin.sum_univ_two, sysA_00, sysA_01, Y0v_0, Y0v_1, sysb_0]
      ring
    · refine hc1.congr_deriv ?_
      rw [Fin.sum_univ_two, sysA_10, sysA_11, Y0v_0, Y0v_1, sysb_1, hU2]
      field_simp
      ring

end

end Work.ALift
