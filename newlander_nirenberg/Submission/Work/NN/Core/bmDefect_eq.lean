import Mathlib
import Submission.Work.NN.Core.bmRow
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps
import Submission.Work.NN.Core.bmPotential_dbarDefect_eq
import Submission.Work.NN.Final.bmDefectTwo

namespace Work.NN.Core

open scoped NNReal ENNReal
open MeasureTheory Set Filter
open Work.CR.Flat

noncomputable section

variable {n : ℕ}

/-! ## Elementary `∂̄`-calculus lemmas

The defect identity propagates the constant `-γ⁻¹` of `bmRow` through `∂̄`, so we record the
two elementary facts needed: `∂̄` kills constants, and `∂̄` of a constant multiple is the
constant multiple of the `∂̄`. -/

/-- `∂̄_j` of a constant function is zero. -/
private lemma dbarCoord_const (j : Fin n) (c : ℂ) (z : Fin n → ℂ) :
    dbarCoord j (fun _ : Fin n → ℂ => c) z = 0 := by
  simp [dbarCoord]

/-- `∂̄_j` of a constant multiple: the Leibniz rule applied to a constant factor. -/
private lemma dbarCoord_const_mul (j : Fin n) (c : ℂ) (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) :
    dbarCoord j (fun w => c * u w) z = c * dbarCoord j u z := by
  have h := Work.CR.Flat.Polydisc.dbarCoord_mul j (fun _ : Fin n → ℂ => c) u z
    (differentiableAt_const c) hu
  simpa [dbarCoord_const j c z] using h

/-- The Bochner–Martinelli row potential of `C¹` compactly supported data is differentiable. -/
private lemma differentiableAt_bmPot {f : Fin n → (Fin n → ℂ) → ℂ}
    (hn : 0 < n) (hf : ∀ j, ContDiff ℝ 1 (f j)) (hcs : ∀ j, HasCompactSupport (f j))
    (z : Fin n → ℂ) : DifferentiableAt ℝ (Work.CR.Flat.Cauchy.bmPot f) z := by
  have hc : ContDiff ℝ 1 (fun y => Work.CR.Flat.Cauchy.bmPotential f y) :=
    Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn (i := 1) hf hcs
  have hfun : Work.CR.Flat.Cauchy.bmPot f = fun y => Work.CR.Flat.Cauchy.bmPotential f y :=
    funext fun y => (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f y).symm
  rw [hfun]
  exact (hc.differentiable one_ne_zero).differentiableAt

/-- The pointwise Leibniz expansion of the combination
`∂̄_j (χ ζ_{km}) - ∂̄_k (χ ζ_{jm}) + ∂̄_m (χ ζ_{jk})`: the `χ`-derivative part is `bmH χ ζ j k m`
and the remaining part is `χ · (∂̄_j ζ_{km} - ∂̄_k ζ_{jm} + ∂̄_m ζ_{jk})`, which vanishes for
`∂̄`-closed `ζ`. -/
private lemma dbarCoord_mul_combination (χ : Cn n → ℂ) (hχ : ContDiff ℝ 1 χ)
    (ζ : Fin n → Fin n → Cn n → ℂ) (hζ : ∀ i l, ContDiff ℝ 1 (ζ i l))
    (hclosed : IsClosedTwo ζ) (j k m : Fin n) (w : Cn n) :
    dbarCoord j (fun y => χ y * ζ k m y) w - dbarCoord k (fun y => χ y * ζ j m y) w
      + dbarCoord m (fun y => χ y * ζ j k y) w = bmH χ ζ j k m w := by
  have hχd : DifferentiableAt ℝ χ w := (hχ.differentiable one_ne_zero).differentiableAt
  have hζd : ∀ i l, DifferentiableAt ℝ (ζ i l) w :=
    fun i l => ((hζ i l).differentiable one_ne_zero).differentiableAt
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul j χ (ζ k m) w hχd (hζd k m),
    Work.CR.Flat.Polydisc.dbarCoord_mul k χ (ζ j m) w hχd (hζd j m),
    Work.CR.Flat.Polydisc.dbarCoord_mul m χ (ζ j k) w hχd (hζd j k)]
  simp only [bmH]
  linear_combination (χ w) * hclosed j k m w

/-- **The defect of one Bochner–Martinelli step.**

Let `χ : ℂⁿ → ℂ` be `C¹` and supported in the closed ball of radius `R > 0`, and let
`ζ : Fin n → Fin n → ℂⁿ → ℂ` have `C¹` components and be `∂̄`-closed (`Work.NN.Core.IsClosedTwo`,
i.e. `∂̄_j ζ_{lm} - ∂̄_l ζ_{jm} + ∂̄_m ζ_{jl} = 0`).  With
`bmH χ ζ j k l w = ∂̄_l χ w · ζ_{jk} w + ∂̄_j χ w · ζ_{kl} w - ∂̄_k χ w · ζ_{jl} w` and
`bmDefect χ ζ j k = (χ - 1) ζ_{jk} - γ⁻¹ bmPot (bmH χ ζ j k ·)` (both defined in
`Submission.Work.NN.Core.bmRow`), one has for all `j k z`

  `∂̄_j (bmRow (χ · ζ))_k z - ∂̄_k (bmRow (χ · ζ))_j z = ζ_{jk} z + bmDefect χ ζ j k z`,

where `(χ · ζ)_{il} w = χ w · ζ_{il} w`.

Intended proof: differentiate under the integral sign (`bmPot_dbarCoord`) for the families
`(χζ)_{k·}` and `(χζ)_{j·}`, expand `∂̄_j(χ ζ_{kl}) - ∂̄_k(χ ζ_{jl})` into the `χ`-derivative part
plus `χ (∂̄_j ζ_{kl} - ∂̄_k ζ_{jl})`, use closedness to write the second part as `-χ ∂̄_l ζ_{jk}` and
the identity `χ ∂̄_l ζ_{jk} = ∂̄_l (χ ζ_{jk}) - ∂̄_l χ · ζ_{jk}` together with the divergence formula
`Σ_l ∫ bmKernel l x ∂̄_l (χ ζ_{jk}) (z+x) dx = γ χ z ζ_{jk} z` for the compactly supported translate
(copy the private `bmKernel_divergence_translate` from
`Submission/Work/NN/Core/bmPotential_dbarDefect_eq.lean`, with
`Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral` and
`Work.CR.Flat.Cauchy.integrable_bmWeight`).  The bracket that remains is exactly
`Σ_l ∫ bmKernel l x · bmH χ ζ j k l (z+x) dx`, i.e. `bmPot (bmH χ ζ j k ·)`.
`Work.NN.Final.bmDefectTwo` (in `Submission/Work/NN/Final/bmDefectTwo.lean`) already carries out
this computation for the products `χ · ζ` and can be adapted. -/
theorem bmDefect_eq {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    (χ : Work.NN.Core.Cn n → ℂ) (hχ : ContDiff ℝ 1 χ)
    (hχsupp : ∀ z : Work.NN.Core.Cn n, R ≤ ‖z‖ → χ z = 0)
    (ζ : Fin n → Fin n → Work.NN.Core.Cn n → ℂ)
    (hζ : ∀ i l, ContDiff ℝ 1 (ζ i l)) (hclosed : Work.NN.Core.IsClosedTwo ζ) :
    ∀ j k (z : Work.NN.Core.Cn n),
      Work.CR.Flat.dbarCoord j (Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) k) z
        - Work.CR.Flat.dbarCoord k (Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) j) z
      = ζ j k z + Work.NN.Core.bmDefect χ ζ j k z := by
  intro j k z
  -- `χ · ζ` is `C¹` with compact support, so `Work.NN.Final.bmDefectTwo` applies to it
  have hXc : ∀ i l : Fin n, ContDiff ℝ 1 (fun w : Cn n => χ w * ζ i l w) :=
    fun i l => hχ.mul (hζ i l)
  have hXs : ∀ i l : Fin n, HasCompactSupport (fun w : Cn n => χ w * ζ i l w) :=
    fun i l => Work.CR.Flat.Cauchy.bmPotDbar_hasCompactSupport_of_norm
      (fun x hx => by rw [hχsupp x hx, zero_mul])
  have hG : Work.CR.Flat.Cauchy.bmGamma n ≠ 0 :=
    Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
  have hT := Work.NN.Final.bmDefectTwo (n := n) hn
    (X := fun i l w => χ w * ζ i l w) hXc hXs j k z
  -- restate it with the two rows written out
  have hT' : Work.CR.Flat.dbarCoord j
        (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ k m w)) z
      - Work.CR.Flat.dbarCoord k
        (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ j m w)) z
      = (∑ m : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x *
          (Work.CR.Flat.dbarCoord j (fun w => χ w * ζ k m w) (z + x)
            - Work.CR.Flat.dbarCoord k (fun w => χ w * ζ j m w) (z + x)
            + Work.CR.Flat.dbarCoord m (fun w => χ w * ζ j k w) (z + x)))
        - Work.CR.Flat.Cauchy.bmGamma n * (χ z * ζ j k z) := hT
  -- the surviving bracket is exactly `bmH χ ζ j k m`
  have hsum : (∑ m : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x *
        (Work.CR.Flat.dbarCoord j (fun w => χ w * ζ k m w) (z + x)
          - Work.CR.Flat.dbarCoord k (fun w => χ w * ζ j m w) (z + x)
          + Work.CR.Flat.dbarCoord m (fun w => χ w * ζ j k w) (z + x)))
      = Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j k l) z := by
    rw [Work.CR.Flat.Cauchy.bmPot]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    congr 1
    exact dbarCoord_mul_combination χ hχ ζ hζ hclosed j k m (z + x)
  have hfinal : Work.CR.Flat.dbarCoord j
        (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ k m w)) z
      - Work.CR.Flat.dbarCoord k
        (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ j m w)) z
      = Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j k l) z
        - Work.CR.Flat.Cauchy.bmGamma n * (χ z * ζ j k z) := by
    rw [hT', hsum]
  -- `bmRow` is `-γ⁻¹ bmPot` of the row, so `∂̄` picks up the constant factor
  have hAk : Work.CR.Flat.dbarCoord j (Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) k) z
      = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.dbarCoord j
              (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ k m w)) z := by
    have hrow : Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) k
        = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) *
            Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ k m w) y := rfl
    rw [hrow]
    exact dbarCoord_const_mul j _ _ z
      (differentiableAt_bmPot hn (fun m => hXc k m) (fun m => hXs k m) z)
  have hAj : Work.CR.Flat.dbarCoord k (Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) j) z
      = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.dbarCoord k
              (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ j m w)) z := by
    have hrow : Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) j
        = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) *
            Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ j m w) y := rfl
    rw [hrow]
    exact dbarCoord_const_mul k _ _ z
      (differentiableAt_bmPot hn (fun m => hXc j m) (fun m => hXs j m) z)
  rw [hAk, hAj]
  have hkey : -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
        * Work.CR.Flat.dbarCoord j
            (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ k m w)) z
      - (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
        * Work.CR.Flat.dbarCoord k
            (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ j m w)) z)
      = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
        * (Work.CR.Flat.dbarCoord j
              (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ k m w)) z
          - Work.CR.Flat.dbarCoord k
              (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ j m w)) z) := by
    ring
  rw [hkey, hfinal, Work.NN.Core.bmDefect_apply]
  have hg1 : (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmGamma n = 1 :=
    inv_mul_cancel₀ hG
  rw [show -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
        * (Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j k l) z
            - Work.CR.Flat.Cauchy.bmGamma n * (χ z * ζ j k z))
      = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => bmH χ ζ j k l) z
        + ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmGamma n)
            * (χ z * ζ j k z) from by ring]
  rw [hg1, one_mul]
  ring

end

end Work.NN.Core
