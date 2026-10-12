import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseKinLoc.NeuFrac.kinetic_pconv_deriv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.deriv_sum_pconv`

The **full** kinetic-energy identity in the `p`-convention of
`Submission.BoseGases.kinFT` (`kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy = 𝓕u((2π)⁻¹•p)`):

    ∑_k ∫_x ‖∂_k F(x)‖² = (2π)⁻³ ∫_p ‖p‖² ‖kinFT F p‖²        (`∂_k = fderiv ℝ F · (kcStdBasis k)`),

for a complex Schwartz function `F`.  This is the `Σ_k`-summed form of
`Work.BoseKinLoc.NeuFrac.kinetic_pconv_deriv`, the `p`-convention counterpart of the
corpus's Dirichlet word `kinWord`.

## Proof

The summandwise identity `kinetic_pconv_deriv` reads

    ∫_x ‖∂_k F(x)‖² = (2π)⁻³ ∫_p ⟨p,e_k⟩² ‖kinFT F p‖²      (`e_k = kcStdBasis k`),

so the left-hand side is `(2π)⁻³ ∑_k ∫_p h_k p` with `h_k p = ⟨p,e_k⟩²‖kinFT F p‖²`.  The two
remaining ingredients are

* `h_k ∈ L¹` for each `k` (`integrable_inner_sq_kinFT`), which allows the finite sum to be
  exchanged with the `p`-integral (`MeasureTheory.integral_finsetSum`), and
* the orthonormal-basis identity `∑_k ⟨p,e_k⟩² = ‖p‖²`
  (`Submission.BoseGases.sum_inner_kcStdBasis_sq`), which turns `∑_k h_k p` into the
  integrand `‖p‖²‖kinFT F p‖²` of the right-hand side.

The integrability `h_k ∈ L¹` is proved on the `ξ = (2π)⁻¹p` side, where `kinFT F` becomes
Mathlib's `𝓕F`: the function `ξ ↦ ⟨ξ,e_k⟩` has temperate growth, so
`ξ ↦ ⟨ξ,e_k⟩ • 𝓕F(ξ)` is again Schwartz (`SchwartzMap.smulLeftCLM`), and a Schwartz function
is in every `Lᵖ` (`SchwartzMap.memLp`); then `ξ ↦ ‖⟨ξ,e_k⟩ • 𝓕F(ξ)‖²` is integrable
(`MeasureTheory.memLp_two_iff_integrable_sq_norm`), and integrability is transported back
along the dilation `ξ = (2π)⁻¹p` (`MeasureTheory.Integrable.comp_smul`).
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform

namespace Work.BoseKinLoc.NeuFrac

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Integrability of the `k`-th kinetic density in the `p`-convention**: for a complex
Schwartz function `F` and a coordinate direction `e_k`, the function
`p ↦ ⟨p,e_k⟩²‖kinFT F p‖²` is Lebesgue integrable on `ℝ³`.

This is what makes the `p`-integral form of the `k`-th summand of the kinetic energy
non-junk, and it is exactly the hypothesis needed to exchange `∑_k` with `∫_p`.

Proof: on the `ξ = (2π)⁻¹p` side, `⟨·,e_k⟩` has temperate growth, so
`ξ ↦ ⟨ξ,e_k⟩ • (𝓕F) ξ` is a Schwartz function, hence `L²`
(`SchwartzMap.memLp` / `MeasureTheory.memLp_two_iff_integrable_sq_norm`); its squared norm is
`⟨ξ,e_k⟩²‖(𝓕F) ξ‖²`.  Integrability is then pulled back along the dilation
`p ↦ (2π)⁻¹ • p` (`MeasureTheory.Integrable.comp_smul`), using
`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`. -/
theorem integrable_inner_sq_kinFT (F : SchwartzMap ℝ³ ℂ) (k : Fin 3) :
    Integrable (fun p : ℝ³ =>
      (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2 *
        ‖Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p‖ ^ 2) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hπne : (2 * Real.pi : ℝ) ≠ 0 := hπ.ne'
  -- The multiplier `ξ ↦ ⟨ξ,e_k⟩` has temperate growth.
  have htg : Function.HasTemperateGrowth
      (fun x : ℝ³ => inner ℝ x (Submission.BoseGases.kcStdBasis k)) :=
    ((innerSL ℝ).flip (Submission.BoseGases.kcStdBasis k)).hasTemperateGrowth
  -- `ξ ↦ ⟨ξ,e_k⟩ • 𝓕F(ξ)` is Schwartz.
  let G : SchwartzMap ℝ³ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (inner ℝ · (Submission.BoseGases.kcStdBasis k)) (𝓕 F)
  have hmem : MemLp (G : ℝ³ → ℂ) 2 (volume : Measure ℝ³) := SchwartzMap.memLp G 2 volume
  have hint : Integrable (fun ξ : ℝ³ => ‖G ξ‖ ^ 2) := hmem.norm.integrable_sq
  have hreal : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
    intro r
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  -- Its squared norm is `⟨ξ,e_k⟩²‖(𝓕F) ξ‖²`.
  have hpoint : ∀ ξ : ℝ³, ‖G ξ‖ ^ 2
      = (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2 * ‖(𝓕 F) ξ‖ ^ 2 := by
    intro ξ
    have hG : G ξ = ((inner ℝ ξ (Submission.BoseGases.kcStdBasis k) : ℝ) : ℂ) • (𝓕 F) ξ := by
      have h := congrFun (SchwartzMap.smulLeftCLM_apply htg (𝓕 F)) ξ
      simpa using h
    rw [hG, norm_smul, mul_pow, hreal]
  have hint' : Integrable (fun ξ : ℝ³ =>
      (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2 * ‖(𝓕 F) ξ‖ ^ 2) :=
    hint.congr (Filter.Eventually.of_forall hpoint)
  -- Pull back along `p ↦ (2π)⁻¹ • p`.
  have hcomp : Integrable (fun p : ℝ³ =>
      (inner ℝ ((2 * Real.pi)⁻¹ • p) (Submission.BoseGases.kcStdBasis k)) ^ 2 *
        ‖(𝓕 F) ((2 * Real.pi)⁻¹ • p)‖ ^ 2) :=
    hint'.comp_smul (R := (2 * Real.pi)⁻¹) (inv_ne_zero hπne)
  -- Rewrite `(𝓕F)((2π)⁻¹•p) = kinFT F p` and remove the constant `(2π)⁻²` coming from the
  -- scaling of `⟨·,e_k⟩`.
  refine (hcomp.const_mul ((2 * Real.pi) ^ 2)).congr
    (Filter.Eventually.of_forall (fun p => ?_))
  beta_reduce
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, real_inner_smul_left,
    SchwartzMap.fourier_coe]
  ring_nf
  rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 (by positivity : Real.pi ≠ 0)), one_mul]

theorem deriv_sum_pconv (F : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    (∑ k : Fin 3, ∫ x : EuclideanSpace ℝ (Fin 3),
        ‖fderiv ℝ (F : EuclideanSpace ℝ (Fin 3) → ℂ) x (Submission.BoseGases.kcStdBasis k)‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT (F : EuclideanSpace ℝ (Fin 3) → ℂ) p‖ ^ 2 := by
  have hInt : ∀ k : Fin 3, Integrable (fun p : ℝ³ =>
      (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2 *
        ‖Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p‖ ^ 2) := fun k => integrable_inner_sq_kinFT F k
  -- The summandwise identity `kinetic_pconv_deriv`.
  have hstep : (∑ k : Fin 3, ∫ x : ℝ³,
        ‖fderiv ℝ (F : ℝ³ → ℂ) x (Submission.BoseGases.kcStdBasis k)‖ ^ 2)
      = ∑ k : Fin 3, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
          (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2 *
            ‖Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p‖ ^ 2 :=
    Finset.sum_congr rfl (fun k _ => kinetic_pconv_deriv F k)
  rw [hstep, ← Finset.mul_sum]
  congr 1
  -- Exchange `∑_k` with `∫_p` (each summand is integrable).
  rw [← MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin 3))
    (f := fun k (p : ℝ³) => (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2 *
            ‖Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p‖ ^ 2)
    (fun k _ => hInt k)]
  -- `∑_k ⟨p,e_k⟩² = ‖p‖²` pointwise.
  congr 1 with p
  rw [← Finset.sum_mul, Submission.BoseGases.sum_inner_kcStdBasis_sq]

end Work.BoseKinLoc.NeuFrac
