import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.LatSym.integrable_symOp_integrand
import Submission.Work.BoseBoxFock.LatSym.integral_conj_mul_exp_inner
import Submission.Work.BoseBoxFock.LatSym.integral_mul_invFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.LatSym

noncomputable section

open MeasureTheory
open scoped Real BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.LatSym.integral_conj_mul_symOp`

`Work.BoseBoxFock.symOp σ g y = (2π)⁻³ ∫ p, exp (I ⟪p,y⟫) * (σ p : ℂ) * kinFT g p`
(`Submission/Work/BoseBoxFock/FRKDefs.lean`).

Target: the Parseval/Fubini identity relating the *position-space* pairing of `symOp σ g` with
`conj ∘ g` to the *momentum-space* integral of `σ` against `‖kinFT g‖²`:

  `∫ x, conj (g x) * symOp σ g (x + η) = (2π)⁻³ ∫ p, (σ p : ℂ) * (‖kinFT g p‖² : ℂ) * exp (I ⟪η,p⟫)`.

## Route (elementary Fubini)

Write `c p = exp (I ⟪p,η⟫) * σ p * ĝ(p)`, which is `L¹` by the polynomial growth of `σ` and the
superpolynomial decay of `ĝ = kinFT g` (`integrable_symOp_integrand`, from
`SqrtKin.kinFT_decay_gen`).  Since `⟪p,x+η⟫ = ⟪p,x⟫ + ⟪p,η⟫`, the `symOp` integrand at `x + η` is
`c p * exp (I ⟪p,x⟫)`, so the `x`- and `p`-integrals may be swapped
(`Work.BoseBoxFock.LatSym.integral_mul_invFT`, a Fubini swap justified by joint `L¹`-ness with
majorant `‖conj g x‖ · ‖c p‖`).  Then `∫ x, conj (g x) exp (I ⟪p,x⟫) = conj (kinFT g p)`
(`Work.BoseBoxFock.LatSym.integral_conj_mul_exp_inner`) and
`conj (kinFT g p) * kinFT g p = (‖kinFT g p‖² : ℂ)` (`Complex.normSq_eq_conj_mul_self`), which
leaves the stated momentum-space integral.
-/

/-- The pointwise rearrangement `conj z · (e · σ · z) = σ · ‖z‖² · e`, with `e = exp (I ⟪p,η⟫)`
(the phase is rewritten from `⟪η,p⟫` to `⟪p,η⟫` by symmetry of the real inner product). -/
private lemma star_kinFT_mul_exp (σ : E3 → ℝ) (g : E3 → ℂ) (η p : E3) :
    (starRingEnd ℂ) (Submission.BoseGases.kinFT g p) *
        (Complex.exp (Complex.I * (inner ℝ p η : ℂ)) * (σ p : ℂ) * Submission.BoseGases.kinFT g p)
      = (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ η p : ℂ)) := by
  have hz : (starRingEnd ℂ) (Submission.BoseGases.kinFT g p) * Submission.BoseGases.kinFT g p
      = ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [real_inner_comm p η]
  calc (starRingEnd ℂ) (Submission.BoseGases.kinFT g p) *
        (Complex.exp (Complex.I * (inner ℝ p η : ℂ)) * (σ p : ℂ) * Submission.BoseGases.kinFT g p)
      = ((starRingEnd ℂ) (Submission.BoseGases.kinFT g p) * Submission.BoseGases.kinFT g p) *
          (Complex.exp (Complex.I * (inner ℝ p η : ℂ)) * (σ p : ℂ)) := by ring
    _ = ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (inner ℝ p η : ℂ)) * (σ p : ℂ)) := by rw [hz]
    _ = (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ p η : ℂ)) := by ring

theorem integral_conj_mul_symOp {σ : EuclideanSpace ℝ (Fin 3) → ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (hσg : ∃ A : ℝ, ∀ p : EuclideanSpace ℝ (Fin 3), |σ p| ≤ A * (1 + ‖p‖) ^ 2)
    (η : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (g x) * Work.BoseBoxFock.symOp σ g (x + η))
      = (((2 * Real.pi) ^ 3 : ℝ) : ℂ)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), (σ p : ℂ) *
          ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
            Complex.exp (Complex.I * (inner ℝ η p : ℂ))) := by
  have hgInt : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hgc' : HasCompactSupport (fun x : E3 => (starRingEnd ℂ) (g x)) := by
    simpa [Function.comp_def] using hgc.comp_left (map_zero (starRingEnd ℂ))
  have hF : Integrable (fun x : E3 => (starRingEnd ℂ) (g x)) :=
    (Complex.continuous_conj.comp hg.continuous).integrable_of_hasCompactSupport hgc'
  have hc : Integrable (fun p : E3 => Complex.exp (Complex.I * (inner ℝ p η : ℂ)) *
      (σ p : ℂ) * Submission.BoseGases.kinFT g p) :=
    integrable_symOp_integrand hg hgc hσ hσg η
  have hshift : ∀ x : E3, (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p (x + η) : ℂ)) *
        (σ p : ℂ) * Submission.BoseGases.kinFT g p)
      = ∫ p : E3, (Complex.exp (Complex.I * (inner ℝ p η : ℂ)) * (σ p : ℂ) *
          Submission.BoseGases.kinFT g p) * Complex.exp (Complex.I * (inner ℝ p x : ℂ)) := by
    intro x
    apply integral_congr_ae
    filter_upwards with p
    rw [inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  calc (∫ x : E3, (starRingEnd ℂ) (g x) * Work.BoseBoxFock.symOp σ g (x + η))
      = ∫ x : E3, (starRingEnd ℂ) (g x) * (((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) *
          (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p (x + η) : ℂ)) * (σ p : ℂ) *
            Submission.BoseGases.kinFT g p)) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Work.BoseBoxFock.symOp]
    _ = ∫ x : E3, ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) *
          ((starRingEnd ℂ) (g x) * (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p (x + η) : ℂ)) *
            (σ p : ℂ) * Submission.BoseGases.kinFT g p)) := by
        apply integral_congr_ae
        filter_upwards with x
        ring
    _ = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) *
          ∫ x : E3, (starRingEnd ℂ) (g x) * (∫ p : E3,
            Complex.exp (Complex.I * (inner ℝ p (x + η) : ℂ)) * (σ p : ℂ) *
              Submission.BoseGases.kinFT g p) := by
        rw [integral_const_mul]
    _ = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) *
          ∫ x : E3, (starRingEnd ℂ) (g x) * (∫ p : E3,
            (Complex.exp (Complex.I * (inner ℝ p η : ℂ)) * (σ p : ℂ) *
              Submission.BoseGases.kinFT g p) * Complex.exp (Complex.I * (inner ℝ p x : ℂ))) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        rw [hshift x]
    _ = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) *
          ∫ p : E3, (∫ x : E3, (starRingEnd ℂ) (g x) *
            Complex.exp (Complex.I * (inner ℝ p x : ℂ))) *
            (Complex.exp (Complex.I * (inner ℝ p η : ℂ)) * (σ p : ℂ) *
              Submission.BoseGases.kinFT g p) := by
        rw [integral_mul_invFT hF hc]
    _ = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) *
          ∫ p : E3, (starRingEnd ℂ) (Submission.BoseGases.kinFT g p) *
            (Complex.exp (Complex.I * (inner ℝ p η : ℂ)) * (σ p : ℂ) *
              Submission.BoseGases.kinFT g p) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with p
        rw [integral_conj_mul_exp_inner hgInt p]
    _ = ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) *
          ∫ p : E3, (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
            Complex.exp (Complex.I * (inner ℝ η p : ℂ)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with p
        exact star_kinFT_mul_exp σ g η p
    _ = (((2 * Real.pi) ^ 3 : ℝ) : ℂ)⁻¹ *
          ∫ p : E3, (σ p : ℂ) * ((‖Submission.BoseGases.kinFT g p‖ ^ 2 : ℝ) : ℂ) *
            Complex.exp (Complex.I * (inner ℝ η p : ℂ)) := by
        rw [Complex.ofReal_inv]

end

end Work.BoseBoxFock.LatSym
