/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W.Ae.Assembly` — the reduction of `level0Ae` to three estimates

This module performs the *assembly* part of the proof of
`Work.FTS.EllipticEst.H2W.level0Ae` (the paper's `(radialandangularweightL2)`, i.e. Steps 1–2
of Proposition `prop:H2` of Elgindi, Annals **194** (2021), in the *almost everywhere* class
`Work.FTS.EllipticEst.H2W.Ae.AeData`).

The three analytic inputs are stated here as `Prop`s (`Step1`, `Step2`, `Step3`) and proved
elsewhere:

* `Step1` — the paper's **Step 1** in the `ρ = w²σ`-norm (with the `σ`-upgrade of the radial
  first-order term): `u` and `z ∂_z u` are honest and
  `‖u‖_ρ ≤ C ‖G‖_ρ`, `α ‖z ∂_z u‖_ρ ≤ C ‖G‖_ρ`;
* `Step2` — the paper's **Step 2**: `‖∂_θθ u‖_ρ ≤ C (‖G‖_ρ + α ‖z ∂_z u‖_ρ)`;
* `Step3` — the paper's radial second-order recovery from the equation
  `α² z²∂_zz u = -G - α(5+α) z∂_z u - ∂_θθ u + ∂_θ(tan θ u) - 6u`:
  `α² ‖z²∂_zz u‖_ρ ≤ C (‖G‖_ρ + α ‖z ∂_z u‖_ρ + ‖∂_θθ u‖_ρ + ‖u‖_ρ)`.

Given the three, the estimate is the arithmetic of the quadratic form
`(α² A + B)² ≥ α⁴ A² + B²` together with Step 1's absorption of `α b` and `m`.

## Why the decomposition is the right one

* The signs of the `α`-powers are those of the paper: `α²` on the radial second-order term,
  `α` on the radial first-order term; the norms are the *squares* of `nrm`, so the target's
  `α⁴` is the square of `α²`.
* No *triangle* inequality for `HkSq` is needed in the assembly: `Step2`/`Step3` already
  deliver the combined quantities `‖∂_θθu‖_ρ` and `α²‖z²∂_zzu‖_ρ` in terms of `‖G‖_ρ` and the
  two absorbed terms, so the assembly is pure real arithmetic plus `√(HkSq`² `= HkSq`.
* The `HkMem` conjuncts of `Step1` (and the `HkMem` of the remaining quantities, which are
  fields of `AeData`) are what make `HkSq` honest; nothing else in the assembly uses them.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false

/-- **Step 1** (paper: `(radialweightonlyL2)` with the `σ`-upgrade): in the class `AeData` the
functions `u` and `z ∂_z u` are honest in `ℋ⁰`, and `‖u‖_ρ ≤ C‖G‖_ρ`,
`α‖z∂_z u‖_ρ ≤ C‖G‖_ρ`. -/
def Step1 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      Work.Spaces.HkMem α 0 u ∧
      Work.Spaces.HkMem α 0 (grad u) ∧
      nrm α u ≤ C * nrm α G ∧
      α * nrm α (grad u) ≤ C * nrm α G

/-- **Step 2** (paper: `(radialandangularweightL2)`, angular half):
`‖∂_θθ u‖_ρ ≤ C(‖G‖_ρ + α‖z∂_z u‖_ρ)`. -/
def Step2 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      nrm α (ang2 u) ≤ C * (nrm α G + α * nrm α (grad u))

/-- **Step 3** (the radial second-order term recovered from the equation):
`α²‖z²∂_zz u‖_ρ ≤ C(‖G‖_ρ + α‖z∂_z u‖_ρ + ‖∂_θθ u‖_ρ + ‖u‖_ρ)`. -/
def Step3 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        ≤ C * (nrm α G + α * nrm α (grad u) + nrm α (ang2 u) + nrm α u)

/-- **The assembly.**  Steps 1–3 imply the level-`0` `η`-weighted estimate. -/
theorem level0Ae_of (h1 : Step1) (h2 : Step2) (h3 : Step3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
        α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)
        ≤ C * Work.Spaces.HkSq α 0 G := by
  obtain ⟨C₁, hC₁, h1'⟩ := h1
  obtain ⟨C₂, hC₂, h2'⟩ := h2
  obtain ⟨C₃, hC₃, h3'⟩ := h3
  have hC₁0 : (0 : ℝ) ≤ C₁ := le_of_lt hC₁
  have hC₂0 : (0 : ℝ) ≤ C₂ := le_of_lt hC₂
  have hC₃0 : (0 : ℝ) ≤ C₃ := le_of_lt hC₃
  -- the coefficient of the final estimate
  have hp1 : 0 ≤ C₂ * (1 + C₁) := mul_nonneg hC₂0 (by linarith)
  have hp2 : 0 ≤ C₃ * (1 + C₁ + C₂ * (1 + C₁) + C₁) := mul_nonneg hC₃0 (by linarith)
  set K : ℝ := C₃ * (1 + C₁ + C₂ * (1 + C₁) + C₁) + C₂ * (1 + C₁) with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  refine ⟨max (K ^ 2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro α u G hA
  obtain ⟨hmemU, hmemGu, huB, hgB⟩ := h1' α u G hA
  have hX' := h2' α u G hA
  have hA2' := h3' α u G hA
  obtain ⟨hα, hα4, heq, hdir0, hdirpi, hsmooth, hmemG, hmemA, hmemB, hmomU, hmomG⟩ := hA
  have hα0 : (0 : ℝ) ≤ α := le_of_lt hα
  have hf0 : 0 ≤ nrm α G := Real.sqrt_nonneg _
  have hb0 : 0 ≤ nrm α (grad u) := Real.sqrt_nonneg _
  have hm0 : 0 ≤ nrm α u := Real.sqrt_nonneg _
  have hX0 : 0 ≤ nrm α (ang2 u) := Real.sqrt_nonneg _
  have ha0 : 0 ≤ nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :=
    Real.sqrt_nonneg _
  -- Step 2, with Step 1's absorption of `α ‖z∂_z u‖_ρ`
  have hprod1 : C₂ * (α * nrm α (grad u)) ≤ C₂ * (C₁ * nrm α G) :=
    mul_le_mul_of_nonneg_left hgB hC₂0
  have hXf : nrm α (ang2 u) ≤ C₂ * (1 + C₁) * nrm α G := by
    nlinarith [hX', hprod1, hf0, hC₂0, hC₁0]
  -- Step 3, with the same absorption and with `X` bounded
  have hsum33 : nrm α G + α * nrm α (grad u) + nrm α (ang2 u) + nrm α u
      ≤ (1 + C₁ + C₂ * (1 + C₁) + C₁) * nrm α G := by
    nlinarith [hgB, huB, hXf, hf0, hb0, hm0, hC₁0, hC₂0]
  have haf : nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      ≤ K * nrm α G := by
    have hmult : C₃ * (nrm α G + α * nrm α (grad u) + nrm α (ang2 u) + nrm α u)
        ≤ C₃ * ((1 + C₁ + C₂ * (1 + C₁) + C₁) * nrm α G) :=
      mul_le_mul_of_nonneg_left hsum33 hC₃0
    have hre : C₃ * ((1 + C₁ + C₂ * (1 + C₁) + C₁) * nrm α G)
        = (C₃ * (1 + C₁ + C₂ * (1 + C₁) + C₁)) * nrm α G := by ring
    rw [hK]
    linarith [hA2', hmult, hre]
  -- the sum of the two quantities
  have hsum : nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      + nrm α (ang2 u) ≤ K * nrm α G := by
    nlinarith [haf, hXf, hK0, hf0, hC₂0, hC₁0]
  -- square everything
  have hsq : (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      + nrm α (ang2 u)) ^ 2 ≤ (K * nrm α G) ^ 2 := by
    nlinarith [hsum, ha0, hX0, hf0, hK0]
  have hexp : (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      + nrm α (ang2 u)) ^ 2
      = (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))) ^ 2
        + (nrm α (ang2 u)) ^ 2
        + 2 * (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)))
          * (nrm α (ang2 u)) := by ring
  have hcross : 0 ≤ 2 * (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)))
      * (nrm α (ang2 u)) := by
    have := mul_nonneg ha0 hX0
    linarith
  have ha2 : (nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))) ^ 2
      = α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) := by
    rw [nrm, Work.FTS.EllipticEst.Honest.hksq_sqrt_sq,
      Work.FTS.EllipticEst.Honest.HkSq_zero_const_mul]
    ring
  have hX2 : (nrm α (ang2 u)) ^ 2 = Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u) := by
    rw [nrm, Work.FTS.EllipticEst.Honest.hksq_sqrt_sq]
    rfl
  have hK2 : (K * nrm α G) ^ 2 = K ^ 2 * Work.Spaces.HkSq α 0 G := by
    rw [mul_pow, nrm, Work.FTS.EllipticEst.Honest.hksq_sqrt_sq]
  rw [hexp, ha2, hX2] at hsq
  rw [hK2] at hsq
  calc α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
        + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)
      ≤ K ^ 2 * Work.Spaces.HkSq α 0 G := by linarith [hsq, hcross]
    _ ≤ max (K ^ 2) 1 * Work.Spaces.HkSq α 0 G :=
        mul_le_mul_of_nonneg_right (le_max_left (K ^ 2) 1)
          (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α G)

end Work.FTS.EllipticEst.H2W.Ae
