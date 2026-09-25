import Mathlib
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.bmDefect_eq
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Final

open scoped NNReal ENNReal
open MeasureTheory Set Filter
open Work.CR.Flat

noncomputable section

variable {n : ℕ}

/-! ## Elementary `∂̄`-calculus lemmas (localised copy of the private lemmas of
`Submission/Work/NN/Core/bmDefect_eq.lean`) -/

/-- `∂̄_j` of a constant function is zero. -/
private lemma dbarCoord_const_local (j : Fin n) (c : ℂ) (z : Fin n → ℂ) :
    dbarCoord j (fun _ : Fin n → ℂ => c) z = 0 := by
  simp [dbarCoord]

/-- `∂̄_j` of a constant multiple: the Leibniz rule applied to a constant factor. -/
private lemma dbarCoord_const_mul_local (j : Fin n) (c : ℂ) (u : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hu : DifferentiableAt ℝ u z) :
    dbarCoord j (fun w => c * u w) z = c * dbarCoord j u z := by
  have h := Work.CR.Flat.Polydisc.dbarCoord_mul j (fun _ : Fin n → ℂ => c) u z
    (differentiableAt_const c) hu
  simpa [dbarCoord_const_local j c z] using h

/-- The Bochner–Martinelli row potential of `C¹` compactly supported data is differentiable. -/
private lemma differentiableAt_bmPot_local {f : Fin n → (Fin n → ℂ) → ℂ}
    (hn : 0 < n) (hf : ∀ j, ContDiff ℝ 1 (f j)) (hcs : ∀ j, HasCompactSupport (f j))
    (z : Fin n → ℂ) : DifferentiableAt ℝ (Work.CR.Flat.Cauchy.bmPot f) z := by
  have hc : ContDiff ℝ 1 (fun y => Work.CR.Flat.Cauchy.bmPotential f y) :=
    Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn (i := 1) hf hcs
  have hfun : Work.CR.Flat.Cauchy.bmPot f = fun y => Work.CR.Flat.Cauchy.bmPotential f y :=
    funext fun y => (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f y).symm
  rw [hfun]
  exact (hc.differentiable one_ne_zero).differentiableAt

/-- **Localised Leibniz expansion.**  The pointwise Leibniz expansion of the combination
`∂̄_j (χ ζ_{km}) - ∂̄_k (χ ζ_{jm}) + ∂̄_m (χ ζ_{jk})`: the `χ`-derivative part is `bmH χ ζ j k m`
and the remaining part is `χ · (∂̄_j ζ_{km} - ∂̄_k ζ_{jm} + ∂̄_m ζ_{jk})`, which vanishes because
it is multiplied by `χ` and `ζ` is closed at the points where `χ` does not vanish.

This is `Work.NN.Core.dbarCoord_mul_combination` (private) with the *global* closedness hypothesis
replaced by closedness on a set `U` containing the support of `χ`. -/
private lemma dbarCoord_mul_combination_local (χ : Work.NN.Core.Cn n → ℂ) (hχ : ContDiff ℝ 1 χ)
    (ζ : Fin n → Fin n → Work.NN.Core.Cn n → ℂ) (hζ : ∀ i l, ContDiff ℝ 1 (ζ i l))
    {U : Set (Work.NN.Core.Cn n)} (hχU : ∀ z, χ z ≠ 0 → z ∈ U)
    (hclosed : ∀ (j k m : Fin n) (z : Work.NN.Core.Cn n), z ∈ U →
      dbarCoord j (ζ k m) z - dbarCoord k (ζ j m) z + dbarCoord m (ζ j k) z = 0)
    (j k m : Fin n) (w : Work.NN.Core.Cn n) :
    dbarCoord j (fun y => χ y * ζ k m y) w - dbarCoord k (fun y => χ y * ζ j m y) w
      + dbarCoord m (fun y => χ y * ζ j k y) w = Work.NN.Core.bmH χ ζ j k m w := by
  have hχd : DifferentiableAt ℝ χ w := (hχ.differentiable one_ne_zero).differentiableAt
  have hζd : ∀ i l, DifferentiableAt ℝ (ζ i l) w :=
    fun i l => ((hζ i l).differentiable one_ne_zero).differentiableAt
  rw [Work.CR.Flat.Polydisc.dbarCoord_mul j χ (ζ k m) w hχd (hζd k m),
    Work.CR.Flat.Polydisc.dbarCoord_mul k χ (ζ j m) w hχd (hζd j m),
    Work.CR.Flat.Polydisc.dbarCoord_mul m χ (ζ j k) w hχd (hζd j k)]
  simp only [Work.NN.Core.bmH]
  by_cases hw : χ w = 0
  · rw [hw]; ring
  · have hc := hclosed j k m w (hχU w hw)
    linear_combination (χ w) * hc

end

/-- **The defect of one Bochner–Martinelli step, with the closedness hypothesis only on a
neighbourhood of the support of the cutoff.**  This is `Work.NN.Core.bmDefect_eq` with the
*global* closedness hypothesis weakened to closedness on a set `U` containing the support of `χ`:
in the proof the closedness of `ζ` is only used at the points `z + x` at which the products
`χ(·) ζ_{i l}(·)` (and their `∂̄`'s) are evaluated, and there it is multiplied by `χ`.

Let `χ : ℂⁿ → ℂ` be `C¹`, vanishing outside the ball of radius `R`, with `{z | χ z ≠ 0} ⊆ U`,
let `ζ` have `C¹` components and be `∂̄`-closed *on `U`*.  Then for all `j k z`

  `∂̄_j (bmRow (χ · ζ))_k z - ∂̄_k (bmRow (χ · ζ))_j z = ζ_{jk} z + bmDefect χ ζ j k z`,

with `bmH χ ζ j k l w = ∂̄_l χ w · ζ_{jk} w + ∂̄_j χ w · ζ_{kl} w - ∂̄_k χ w · ζ_{jl} w` and
`bmDefect χ ζ j k = (χ - 1) ζ_{jk} - γ⁻¹ bmPot (bmH χ ζ j k ·)` as in `Work.NN.Core.bmRow`.
This is the form needed when the `(0,2)`-datum `η` is only known to be closed on a polydisc (the
cutoff then has its support inside that polydisc); the proof is `bmDefect_eq` with a case split in
`dbarCoord_mul_combination`. -/
theorem bmDefect_eq_local {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) {U : Set (Fin n → ℂ)}
    (hUopen : IsOpen U)
    (χ : Work.NN.Core.Cn n → ℂ) (hχ : ContDiff ℝ 1 χ)
    (hχsupp : ∀ z : Work.NN.Core.Cn n, R ≤ ‖z‖ → χ z = 0)
    (hχU : ∀ z : Work.NN.Core.Cn n, χ z ≠ 0 → z ∈ U)
    (ζ : Fin n → Fin n → Work.NN.Core.Cn n → ℂ) (hζ : ∀ i l, ContDiff ℝ 1 (ζ i l))
    (hclosed : ∀ (j k m : Fin n) (z : Work.NN.Core.Cn n), z ∈ U →
      Work.CR.Flat.dbarCoord j (ζ k m) z - Work.CR.Flat.dbarCoord k (ζ j m) z
        + Work.CR.Flat.dbarCoord m (ζ j k) z = 0) :
    ∀ (j k : Fin n) (z : Work.NN.Core.Cn n),
      Work.CR.Flat.dbarCoord j
          (Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) k) z
        - Work.CR.Flat.dbarCoord k
          (Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) j) z
      = ζ j k z + Work.NN.Core.bmDefect χ ζ j k z := by
  intro j k z
  have hXc : ∀ i l : Fin n, ContDiff ℝ 1 (fun w : Work.NN.Core.Cn n => χ w * ζ i l w) :=
    fun i l => hχ.mul (hζ i l)
  have hXs : ∀ i l : Fin n, HasCompactSupport (fun w : Work.NN.Core.Cn n => χ w * ζ i l w) :=
    fun i l => Work.CR.Flat.Cauchy.bmPotDbar_hasCompactSupport_of_norm
      (fun x hx => by rw [hχsupp x hx, zero_mul])
  have hG : Work.CR.Flat.Cauchy.bmGamma n ≠ 0 :=
    Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
  have hT := Work.NN.Final.bmDefectTwo (n := n) hn
    (X := fun i l w => χ w * ζ i l w) hXc hXs j k z
  have hT' : Work.CR.Flat.dbarCoord j
        (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ k m w)) z
      - Work.CR.Flat.dbarCoord k
        (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ j m w)) z
      = (∑ m : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x *
          (Work.CR.Flat.dbarCoord j (fun w => χ w * ζ k m w) (z + x)
            - Work.CR.Flat.dbarCoord k (fun w => χ w * ζ j m w) (z + x)
            + Work.CR.Flat.dbarCoord m (fun w => χ w * ζ j k w) (z + x)))
        - Work.CR.Flat.Cauchy.bmGamma n * (χ z * ζ j k z) := hT
  have hsum : (∑ m : Fin n, ∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel m x *
        (Work.CR.Flat.dbarCoord j (fun w => χ w * ζ k m w) (z + x)
          - Work.CR.Flat.dbarCoord k (fun w => χ w * ζ j m w) (z + x)
          + Work.CR.Flat.dbarCoord m (fun w => χ w * ζ j k w) (z + x)))
      = Work.CR.Flat.Cauchy.bmPot (fun l => Work.NN.Core.bmH χ ζ j k l) z := by
    rw [Work.CR.Flat.Cauchy.bmPot]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    congr 1
    exact dbarCoord_mul_combination_local χ hχ ζ hζ hχU hclosed j k m (z + x)
  have hfinal : Work.CR.Flat.dbarCoord j
        (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ k m w)) z
      - Work.CR.Flat.dbarCoord k
        (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ j m w)) z
      = Work.CR.Flat.Cauchy.bmPot (fun l => Work.NN.Core.bmH χ ζ j k l) z
        - Work.CR.Flat.Cauchy.bmGamma n * (χ z * ζ j k z) := by
    rw [hT', hsum]
  have hAk : Work.CR.Flat.dbarCoord j (Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) k) z
      = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.dbarCoord j
              (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ k m w)) z := by
    have hrow : Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) k
        = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) *
            Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ k m w) y := rfl
    rw [hrow]
    exact dbarCoord_const_mul_local j _ _ z
      (differentiableAt_bmPot_local hn (fun m => hXc k m) (fun m => hXs k m) z)
  have hAj : Work.CR.Flat.dbarCoord k (Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) j) z
      = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.dbarCoord k
              (Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ j m w)) z := by
    have hrow : Work.NN.Core.bmRow (fun i l w => χ w * ζ i l w) j
        = fun y => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) *
            Work.CR.Flat.Cauchy.bmPot (fun m => fun w => χ w * ζ j m w) y := rfl
    rw [hrow]
    exact dbarCoord_const_mul_local k _ _ z
      (differentiableAt_bmPot_local hn (fun m => hXc j m) (fun m => hXs j m) z)
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
        * (Work.CR.Flat.Cauchy.bmPot (fun l => Work.NN.Core.bmH χ ζ j k l) z
            - Work.CR.Flat.Cauchy.bmGamma n * (χ z * ζ j k z))
      = -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)
          * Work.CR.Flat.Cauchy.bmPot (fun l => Work.NN.Core.bmH χ ζ j k l) z
        + ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹ * Work.CR.Flat.Cauchy.bmGamma n)
            * (χ z * ζ j k z) from by ring]
  rw [hg1, one_mul]
  ring

end Work.NN.Final
