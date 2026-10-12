import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.box_avg
import Submission.Work.BoseKinLoc.NeuFrac.exists_trial_smooth
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_le_box_L2
import Submission.Work.BoseKinLoc.NeuFrac.raFrac_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseKinLoc.NeuFrac.neumann_bound` — BS `eq:Neumannineq` (FS `(44)`)

The residual `NeumannBound` of `Submission.Work.BoseKinLoc.Residuals`: the `u`-average of the
box (Neumann) resolvent fractions is dominated by the full-space resolvent fraction.

## The route

Write `Λ(u) = lamBox ℓ u` (the corpus's `bsBox`), `c = (dℓ)⁻²`, and

`boxWord u θ := ∫_{Λ(u)}ψ² − 2c∫_{Λ(u)}ψθ + c(Σ_k∫_{Λ(u)}(∂_kθ)² + c∫_{Λ(u)}θ²)`.

By *definition* of `neuFrac` as an `sInf` over smooth compactly supported trials, and because
the trial functional only sees the restriction of the trial to `Λ(u)` (cut `θ` off by a bump
`η ≡ 1` on a neighbourhood of the box; the cutoff is invisible in the box integrals,
`trial_value_mul_eq`), one has the one-sided variational inequality

`neuFrac ℓ c u ψ ≤ boxWord u θ` for **every** smooth `θ` (`neuFrac_le_box_smooth`).

Averaging in `u` and using the exact tiling identity `∫_u ∫_{Λ(u)}F = ∫F` (multiplicity one,
`box_avg`) gives

`∫_u neuFrac ℓ c u ψ ≤ ∫ψ² − c·Q(θ)`, `Q(θ) := 2∫ψθ − Σ_k∫(∂_kθ)² − c∫θ²`.

The analytic input (`exists_trial_smooth`) is the *attained* supremum `sup_θ Q(θ) = V`, where
`V = (2π)⁻³∫_p ‖fhat ψ p‖²/(‖p‖²+c)dp`: the maximiser is the resolvent `(−Δ+c)⁻¹ψ`, produced
as `Re 𝓕⁻¹((‖2πξ‖²+c)⁻¹ · 𝓕ψ)` — a Schwartz function, since `ψ` is smooth with compact
support — and Plancherel plus the Fourier derivative rule give `Q = V` exactly.  Finally
`raFrac_eq_smooth` rewrites the right-hand side as `∫ψ² − c·V`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.NeuFrac

open Submission.BoseGases
open Work.BSKinetic

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- **The one-sided variational inequality for `neuFrac` at a smooth trial** (`ψ ∈ L²`).

`neuFrac` is the `sInf` of the trial values over smooth compactly supported `g`; the trial
functional only sees the restriction to the box `Λ(u) = lamBox ℓ u`, so cutting an arbitrary
smooth `θ` off by a bump `η ≡ 1` on a neighbourhood of the box produces an admissible trial
with exactly the same box integrals (`trial_value_mul_eq`). -/
lemma neuFrac_le_box_smooth {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 ≤ a2) (u : ℝ³)
    (ψ : ℝ³ → ℝ) (θ : ℝ³ → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hψ : Integrable (fun z : ℝ³ => (ψ z) ^ 2)) :
    neuFrac ℓ a2 u ψ ≤
      (∫ z in lamBox ℓ u, (ψ z) ^ 2)
        - 2 * a2 * (∫ z in lamBox ℓ u, ψ z * θ z)
        + a2 * ((∑ k : Fin 3, ∫ z in lamBox ℓ u, (fderiv ℝ θ z (kcStdBasis k)) ^ 2)
                + a2 * (∫ z in lamBox ℓ u, (θ z) ^ 2)) := by
  obtain ⟨R, η, hbox, hηdiff, hηcs, hη1⟩ := exists_box_bump ℓ u
  have hadm : ContDiff ℝ ∞ (fun z : ℝ³ => η z * θ z) := hηdiff.mul hθ
  have hcs : HasCompactSupport (fun z : ℝ³ => η z * θ z) := hηcs.mul_right
  have h := neuFrac_le_trial_of_integrableSq (ℓ := ℓ) (a2 := a2) ha2 u hψ hadm hcs
  rwa [trial_value_mul_eq (ℓ := ℓ) (a2 := a2) (R := R) (u := u) (ψ := ψ) (θ := θ)
    (η := η) hbox hη1] at h

/-- **`raFrac` in the `L²` form used by the assembly** (`ψ` smooth with compact support):
`raFrac ℓ d ψ = ∫ψ² − (dℓ)⁻²` times the resolvent density
`(2π)⁻³∫_p ‖fhat ψ p‖²/(‖p‖²+(dℓ)⁻²)`.

This is `Work.BoseKinLoc.NeuFrac.raFrac_eq` re-proved at the honest smoothness hypothesis
(`ContDiff ℝ ∞`, not the analytic `⊤`): the pointwise split `p²/(p²+a²) = 1 − a²/(p²+a²)`
(`raSym_mul_eq`) plus the `p`-convention Plancherel theorem. -/
theorem raFrac_eq_smooth (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hcs : HasCompactSupport ψ) :
    raFrac ℓ d ψ =
      (∫ x : ℝ³, (ψ x) ^ 2)
        - (d * ℓ) ^ (-2 : ℤ) * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : ℝ³, ‖fhat ψ p‖ ^ 2 / (‖p‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ))) := by
  have ha : 0 < (d * ℓ) ^ (-2 : ℤ) := by positivity
  have hFint : Integrable
      (fun p : ℝ³ => ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2) :=
    Work.BSKinetic.integrable_kinFT_sq ψ hψ hcs
  have hGint : Integrable
      (fun p : ℝ³ => ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2 /
        (‖p‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ))) :=
    integrable_div_quad _ ha hFint
  unfold raFrac fhat
  have hpt : ∀ p : ℝ³,
      raSym ℓ d p * ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2
        = ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2
          - (d * ℓ) ^ (-2 : ℤ) * (‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2
              / (‖p‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ))) :=
    fun p => raSym_mul_eq ℓ d ha p _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_sub hFint (hGint.const_mul _), integral_const_mul, mul_sub,
    Work.BSKinetic.plancherel_pconv ψ hψ hcs]
  ring

theorem neumann_bound : NeumannBound := by
  intro ψ hψ hcs ℓ d hℓ hd hInt
  set c : ℝ := (d * ℓ) ^ (-2 : ℤ) with hc_def
  have hpos : 0 < d * ℓ := mul_pos hd hℓ
  have hcpos : 0 < c := by
    rw [hc_def]
    exact zpow_pos hpos _
  have hψ2 : Integrable (fun z : ℝ³ => (ψ z) ^ 2) :=
    Continuous.integrable_of_hasCompactSupport (hψ.continuous.pow 2)
      (hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))
  obtain ⟨θ, hθ, hθ2, hθd2, hψθ, hcrux⟩ := exists_trial_smooth ψ hψ hcs (c := c) hcpos
  -- the four `u`-functions of the box word
  set F1 : ℝ³ → ℝ := fun u => ∫ z in lamBox ℓ u, (ψ z) ^ 2 with hF1
  set F2 : ℝ³ → ℝ := fun u => ∫ z in lamBox ℓ u, ψ z * θ z with hF2
  set F3 : ℝ³ → ℝ := fun u =>
    ∑ k : Fin 3, ∫ z in lamBox ℓ u, (fderiv ℝ θ z (kcStdBasis k)) ^ 2 with hF3
  set F4 : ℝ³ → ℝ := fun u => ∫ z in lamBox ℓ u, (θ z) ^ 2 with hF4
  have e1 : (∫ u : ℝ³, F1 u) = ∫ z : ℝ³, (ψ z) ^ 2 :=
    (box_avg hℓ (fun z : ℝ³ => (ψ z) ^ 2) hψ2).2
  have e2 : (∫ u : ℝ³, F2 u) = ∫ z : ℝ³, ψ z * θ z :=
    (box_avg hℓ (fun z : ℝ³ => ψ z * θ z) hψθ).2
  have e4 : (∫ u : ℝ³, F4 u) = ∫ z : ℝ³, (θ z) ^ 2 :=
    (box_avg hℓ (fun z : ℝ³ => (θ z) ^ 2) hθ2).2
  have e3 : (∫ u : ℝ³, F3 u)
      = ∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ θ z (kcStdBasis k)) ^ 2 := by
    rw [hF3]
    rw [integral_finsetSum Finset.univ
      (fun k _ => (box_avg hℓ (fun z : ℝ³ => (fderiv ℝ θ z (kcStdBasis k)) ^ 2) (hθd2 k)).1)]
    exact Finset.sum_congr rfl fun k _ =>
      (box_avg hℓ (fun z : ℝ³ => (fderiv ℝ θ z (kcStdBasis k)) ^ 2) (hθd2 k)).2
  have hIntF1 : Integrable F1 := (box_avg hℓ (fun z : ℝ³ => (ψ z) ^ 2) hψ2).1
  have hIntF2 : Integrable F2 := (box_avg hℓ (fun z : ℝ³ => ψ z * θ z) hψθ).1
  have hIntF4 : Integrable F4 := (box_avg hℓ (fun z : ℝ³ => (θ z) ^ 2) hθ2).1
  have hIntF3 : Integrable F3 := by
    rw [hF3]
    exact integrable_finsetSum Finset.univ fun k _ =>
      (box_avg hℓ (fun z : ℝ³ => (fderiv ℝ θ z (kcStdBasis k)) ^ 2) (hθd2 k)).1
  -- the pointwise inequality, and its integral
  have hpt : ∀ u : ℝ³, neuFrac ℓ c u ψ ≤ F1 u - 2 * c * F2 u + c * (F3 u + c * F4 u) :=
    fun u => neuFrac_le_box_smooth hℓ hcpos.le u ψ θ hθ hψ2
  have hIntG : Integrable (fun u : ℝ³ => F1 u - 2 * c * F2 u + c * (F3 u + c * F4 u)) :=
    (hIntF1.sub (hIntF2.const_mul (2 * c))).add ((hIntF3.add (hIntF4.const_mul c)).const_mul c)
  have h1 : (∫ u : ℝ³, neuFrac ℓ c u ψ)
      ≤ ∫ u : ℝ³, (F1 u - 2 * c * F2 u + c * (F3 u + c * F4 u)) :=
    integral_mono hInt hIntG hpt
  -- evaluate the averaged right-hand side
  have hA : Integrable (fun u : ℝ³ => F1 u - 2 * c * F2 u) :=
    hIntF1.sub (hIntF2.const_mul (2 * c))
  have hB : Integrable (fun u : ℝ³ => c * (F3 u + c * F4 u)) :=
    (hIntF3.add (hIntF4.const_mul c)).const_mul c
  have h2 : (∫ u : ℝ³, (F1 u - 2 * c * F2 u + c * (F3 u + c * F4 u)))
      = ((∫ z : ℝ³, (ψ z) ^ 2) - 2 * c * (∫ z : ℝ³, ψ z * θ z))
        + c * ((∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ θ z (kcStdBasis k)) ^ 2)
                + c * (∫ z : ℝ³, (θ z) ^ 2)) := by
    rw [integral_add hA hB, integral_sub hIntF1 (hIntF2.const_mul (2 * c)),
      integral_const_mul (2 * c) F2,
      integral_const_mul c (fun u : ℝ³ => F3 u + c * F4 u),
      integral_add hIntF3 (hIntF4.const_mul c), integral_const_mul c F4,
      e1, e2, e3, e4]
  -- the crux: the variational value is attained
  have hV : ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖fhat ψ p‖ ^ 2 / (‖p‖ ^ 2 + c)
      ≤ 2 * (∫ x : ℝ³, ψ x * θ x)
        - (∑ k : Fin 3, ∫ x : ℝ³, (fderiv ℝ θ x (kcStdBasis k)) ^ 2)
        - c * (∫ x : ℝ³, (θ x) ^ 2) := hcrux
  have h3 : ((∫ z : ℝ³, (ψ z) ^ 2) - 2 * c * (∫ z : ℝ³, ψ z * θ z))
        + c * ((∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ θ z (kcStdBasis k)) ^ 2)
                + c * (∫ z : ℝ³, (θ z) ^ 2))
      ≤ raFrac ℓ d ψ := by
    have hkey : ((∫ z : ℝ³, (ψ z) ^ 2) - 2 * c * (∫ z : ℝ³, ψ z * θ z))
          + c * ((∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ θ z (kcStdBasis k)) ^ 2)
                  + c * (∫ z : ℝ³, (θ z) ^ 2))
        = (∫ z : ℝ³, (ψ z) ^ 2)
          - c * (2 * (∫ z : ℝ³, ψ z * θ z)
            - (∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ θ z (kcStdBasis k)) ^ 2)
            - c * (∫ z : ℝ³, (θ z) ^ 2)) := by ring
    rw [hkey, raFrac_eq_smooth ℓ d hℓ hd hψ hcs, ← hc_def]
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hV hcpos.le) _
  exact le_trans h1 (le_trans (le_of_eq h2) h3)

end Work.BoseKinLoc.NeuFrac
