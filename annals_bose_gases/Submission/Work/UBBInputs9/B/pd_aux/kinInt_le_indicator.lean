import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.UBBInputs9.B.pd_aux.proj_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.pd_aux.kinInt_le_indicator`

**The unprojected Dirichlet integrand `kinInt` is bounded by a constant times the indicator of
a ball in the sliding variable `u`** (uniformly over `x ∈ abox 1 ℓ`).

`kinInt ℓ d Φ u x = Σ_k (∂_k (χ_{B(u)}·Φ)(x))²` where `χ_{B(u)}` is the sliding window.  Two
facts give the claim.

* *Boundedness*: `kinInt ℓ d Φ u x = Σ_k (chiBLc ℓ d Φ k (u,x))²` (`proj_decomp.kinInt_eq`) and
  `chiBLc ℓ d Φ k` is continuous on `ℝ³ × X 1` (`proj_decomp.continuous_chiBLc`), so on the
  compact set `closedBall 0 R ×ˢ abox 1 ℓ` the integrand is bounded by a constant `C`.
* *Vanishing for large `u`*: the window factor `χ_{ℓd}(x 0 - (ℓd)•u)` and its derivative both
  vanish as soon as `‖x 0 - (ℓd)•u‖ > ℓd/2`; for `‖u‖` large this holds for every `x` in the
  box, because `‖x 0‖` is bounded on `acube ℓ` (`acube_isBounded`).  The Leibniz form
  `Basic.fderiv_chiBPhi_eq` then gives `kinInt = 0` there.

Both facts together: take `R` as in the proof (of the size `(ℓd/2 + B + 1)/(ℓd)`) and
`C := max C 0`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission.BoseGases

namespace Work.UBBInputs9.B.pd_aux

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

lemma kinInt_le_indicator {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {Φ : Submission.BoseGases.X 1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hcs : HasCompactSupport Φ) : ∃ R C : ℝ, 0 ≤ C ∧ ∀ (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X 1), x ∈ Submission.BoseGases.abox 1 ℓ → Work.UBBInputs9.B.kinInt ℓ d Φ u x ≤ C * (Metric.closedBall 0 R).indicator (fun _ => (1 : ℝ)) u := by
  have hL : 0 < ℓ * d := mul_pos hℓ hd
  -- a norm bound for the centred cube
  obtain ⟨B, hB⟩ := (Submission.BoseGases.acube_isBounded ℓ hℓ.le).exists_norm_le
  set B' : ℝ := max B 1 with hB'def
  have hB'1 : (1 : ℝ) ≤ B' := le_max_right _ _
  set R : ℝ := (ℓ * d / 2 + B' + 1) / (ℓ * d) with hRdef
  -- the integrand is continuous on `ℝ³ × X 1`
  have hcont : Continuous (fun p : ℝ³ × X1 => Work.UBBInputs9.B.kinInt ℓ d Φ p.1 p.2) := by
    have hEq : (fun p : ℝ³ × X1 => Work.UBBInputs9.B.kinInt ℓ d Φ p.1 p.2)
        = fun p => ∑ k : Fin 3, (chiBLc ℓ d Φ k p) ^ 2 := by
      funext p
      exact kinInt_eq (ℓ := ℓ) (d := d) hℓ hd p.1 (Φ := Φ) hΦ p.2
    rw [hEq]
    exact continuous_finsetSum Finset.univ
      (fun k _ => (continuous_chiBLc (ℓ := ℓ) (d := d) hℓ hd Φ hΦ k).pow 2)
  have hKc : IsCompact (Metric.closedBall (0 : ℝ³) R ×ˢ abox 1 ℓ) :=
    (isCompact_closedBall (0 : ℝ³) R).prod (abox_isCompact 1 ℓ)
  obtain ⟨C', hC'⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨R, max C' 0, le_max_right _ _, ?_⟩
  intro u x hx
  by_cases huR : u ∈ Metric.closedBall (0 : ℝ³) R
  · -- inside the ball: the compactness bound
    rw [Set.indicator_of_mem huR]
    have hKmem : (u, x) ∈ Metric.closedBall (0 : ℝ³) R ×ˢ abox 1 ℓ := ⟨huR, hx⟩
    have h1 : ‖Work.UBBInputs9.B.kinInt ℓ d Φ u x‖ ≤ C' := hC' (u, x) hKmem
    have h2 : Work.UBBInputs9.B.kinInt ℓ d Φ u x ≤ max C' 0 :=
      le_trans (le_abs_self _) (le_trans h1 (le_max_left _ _))
    simpa using h2
  · -- outside the ball: the integrand vanishes
    rw [Set.indicator_of_notMem huR, mul_zero]
    have hu' : R < ‖u‖ := by
      simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at huR
      exact lt_of_not_ge huR
    have hx0 : x 0 ∈ Submission.BoseGases.acube ℓ :=
      (Submission.BoseGases.mem_abox_iff 1 ℓ x).mp hx 0
    have hx0' : ‖x 0‖ ≤ B' := le_trans (hB (x 0) hx0) (le_max_left _ _)
    -- `x 0 - (ℓd)•u` lies outside `acube (ℓd)`, hence outside the support of the window
    have hbig : ℓ * d / 2 < ‖x 0 - (ℓ * d) • u‖ := by
      have hLu : ‖(ℓ * d) • u‖ = (ℓ * d) * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
      have htri : ‖(ℓ * d) • u‖ - ‖x 0‖ ≤ ‖x 0 - (ℓ * d) • u‖ := by
        rw [norm_sub_rev (x 0) ((ℓ * d) • u)]
        exact norm_sub_norm_le _ _
      have hmul : (ℓ * d) * R < (ℓ * d) * ‖u‖ := mul_lt_mul_of_pos_left hu' hL
      have hRval : (ℓ * d) * R = ℓ * d / 2 + B' + 1 := by
        rw [hRdef]
        field_simp
      rw [hLu] at htri
      nlinarith [hmul, hRval, htri, hx0']
    have hchi : chiScale (ℓ * d) (x 0 - (ℓ * d) • u) = 0 := by
      by_contra hne
      have h := Submission.BoseGases.chiScale_support_le hL hne
      linarith
    have hzero : Work.UBBInputs9.B.kinInt ℓ d Φ u x = 0 := by
      unfold Work.UBBInputs9.B.kinInt
      refine Finset.sum_eq_zero (fun k _ => ?_)
      have hder : fderiv ℝ (chiScale (ℓ * d)) (x 0 - (ℓ * d) • u) (kcStdBasis k) = 0 :=
        Work.UBBInputs9.B.fderiv_chiScale_eq_zero_of_norm_gt hL hbig
      rw [Work.UBBInputs9.B.fderiv_chiBPhi_eq ℓ d hΦ u x k, hchi, hder]
      ring
    rw [hzero]

end Work.UBBInputs9.B.pd_aux
