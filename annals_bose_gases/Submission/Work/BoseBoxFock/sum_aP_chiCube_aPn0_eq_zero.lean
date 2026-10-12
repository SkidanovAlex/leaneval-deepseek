import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRowDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sum_aP_chiCube_aPn0_eq_zero`

The `n₀ ∘ (χ²−1) ∘ n₀` row of the number operator vanishes on the box.

With `aP ℓ i Φ x = (ℓ³)⁻¹ ∫_{Λ(ℓ)} Φ(x[i ↦ y]) dy` the mean over the cube `Λ(ℓ) = acube ℓ`
in the `i`-th particle, and `chiCube ℓ = χ_Λ² − 1` (the χ-row weight of
`Work.BoseBoxFock.chiRowDefs`), the claim is

  `∑ i, ∫_{Λ(ℓ)^N} (aPᵢΦ)(x) · chiCube ℓ (xᵢ) · (aPᵢ (∑ j, aPⱼΦ))(x) dx = 0`.

The mechanism — the same one that makes the *diagonal* χ-row vanish
(`Work.BoseBoxFock.chiRow_diagZero`) — is:

* `aP ℓ i Ψ` does not depend on the coordinate `xᵢ` (`Work.BoseBoxFock.aP_update`), for **any** `Ψ`;
* the box measure `volume ↾ Λ(ℓ)^N` is the product of the measures
  `volume ↾ Λ(ℓ)` on the coordinates (`Submission.BoseGases.restrict_abox_eq_pi`), so an integral of
  the form `∫ G(x) · w(xᵢ)` with `G` independent of `xᵢ` factorises into `(∫ G) · (∫_{Λ(ℓ)} w)`;
* `∫_{Λ(ℓ)} chiCube ℓ = 0` (`Work.BoseBoxFock.integral_chiCube_acube`).

Consequently the statement holds **for every** `Φ` and every `Ψ` in the second slot — no continuity
of `Φ` is needed (the hypothesis `hΦc` of the requested statement is inherited from the χ-row context
and is unused here). The general form is isolated as `aP_mul_of_integral_eq_zero` below, since the χ-row
assembly of `PotChiLin_exists` needs it with an arbitrary mean-zero weight rather than `chiCube`.

Everything here is `sorry`-free.
-/

set_option linter.style.haveILetI false

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

/-- **A mean-zero weight annihilates the two condensing slots.**  For any `i`, any weight `w` with
vanishing cube mean, and **any** `Φ Ψ`,

  `∫_{Λ(ℓ)^N} (aP ℓ i Φ)(x) · w(xᵢ) · (aP ℓ i Ψ)(x) dx = 0`.

Indeed both `aP ℓ i Φ` and `aP ℓ i Ψ` are independent of `xᵢ` (`aP_update`), so the integrand is
`G(x) · w(xᵢ)` with `G` independent of `xᵢ`; the product structure of the box measure and
`∫_{Λ(ℓ)} w = 0` finish it (`piIntegral_factor_zero`). -/
lemma aP_mul_of_integral_eq_zero {N : ℕ} {ℓ : ℝ} (i : Fin N)
    {w : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hmean : (∫ z in Submission.BoseGases.acube ℓ, w z) = 0)
    (Φ Ψ : Submission.BoseGases.X N → ℝ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
      Submission.BoseGases.aP ℓ i Φ x *
        (w (x i) * Submission.BoseGases.aP ℓ i Ψ x)) = 0 := by
  classical
  -- `(aPᵢΦ)·(aPᵢΨ)` is independent of the `i`-th coordinate.
  have hG : ∀ (x : Submission.BoseGases.X N) (z : EuclideanSpace ℝ (Fin 3)),
      (fun y : Submission.BoseGases.X N =>
          Submission.BoseGases.aP ℓ i Φ y * Submission.BoseGases.aP ℓ i Ψ y)
        (Function.update x i z)
      = (fun y : Submission.BoseGases.X N =>
          Submission.BoseGases.aP ℓ i Φ y * Submission.BoseGases.aP ℓ i Ψ y) x := by
    intro x z
    simp only [aP_update]
  -- Factorise the product measure along the `i`-th coordinate.
  have hmain : (∫ y, (Submission.BoseGases.aP ℓ i Φ y * Submission.BoseGases.aP ℓ i Ψ y) *
      w (y i)
      ∂(MeasureTheory.Measure.pi (fun _ : Fin N =>
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)))) = 0 :=
    piIntegral_factor_zero i _ w
      (fun y => Submission.BoseGases.aP ℓ i Φ y * Submission.BoseGases.aP ℓ i Ψ y) hG hmean
  rw [Submission.BoseGases.restrict_abox_eq_pi N ℓ]
  rw [show (fun x : Submission.BoseGases.X N =>
        Submission.BoseGases.aP ℓ i Φ x *
          (w (x i) * Submission.BoseGases.aP ℓ i Ψ x))
      = (fun x => (Submission.BoseGases.aP ℓ i Φ x * Submission.BoseGases.aP ℓ i Ψ x) *
          w (x i)) from
        funext (fun x => by ring)]
  exact hmain

/-- **The `n₀ ∘ (χ_Λ² − 1) ∘ n₀` row vanishes on the box**: with `aP` the cube mean in the `i`-th
particle and `chiCube ℓ = χ_Λ² − 1` the (mean-zero on the cube) χ-row weight, the sum over the
particles of the two-slot sandwich `⟨Φ, n₀ (χ²−1) n₀ Φ⟩` is zero.  Each term is
`aP_mul_of_integral_eq_zero` at the weight `chiCube ℓ`, whose cube mean vanishes
(`integral_chiCube_acube`). -/
theorem sum_aP_chiCube_aPn0_eq_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x *
          (Work.BoseBoxFock.chiCube ℓ (x i) *
            (Submission.BoseGases.aP ℓ i (fun y : Submission.BoseGases.X n =>
              ∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ y) x)) = 0 := by
  classical
  refine Finset.sum_eq_zero (fun i _ => ?_)
  exact aP_mul_of_integral_eq_zero i (integral_chiCube_acube hℓ) Φ
    (fun y : Submission.BoseGases.X n => ∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ y)

end Work.BoseBoxFock
