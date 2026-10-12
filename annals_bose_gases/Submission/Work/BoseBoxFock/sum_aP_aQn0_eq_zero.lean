import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiA_const
import Submission.Work.BoseBoxFock.chiRowDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sum_aP_aQn0_eq_zero` — the `Pᵢ · Qᵢ n₀` sum vanishes

For a continuous state `Φ` on the `n`-particle centred box,

    ∑ᵢ ∫_{abox n ℓ} (PᵢΦ)·(Qᵢ n₀Φ) = 0 ,     n₀Φ := ∑ⱼ PⱼΦ ,

a *termwise* cancellation: for **every** slot `i` and **every** pair of continuous `Φ, Ψ`,

    ∫_{abox n ℓ} (PᵢΦ)·(QᵢΨ) = 0        (`Work.BoseBoxFock.aP_mul_aQ_box`)

because `QᵢΨ = Ψ − PᵢΨ` has vanishing `i`-th fibre mean while `PᵢΦ` does not depend on the
`i`-th coordinate (self-adjointness of the box mean `aP_sym_box` + idempotency `aP_idem`).
Applying that with `Ψ := ∑ⱼ PⱼΦ` (continuous, a finite sum of continuous fibre means,
`Submission.BoseGases.aP_continuous`) gives each summand `0`, hence the sum.

Everything here is `sorry`-free.
-/

namespace Work.BoseBoxFock

open scoped BigOperators

theorem sum_aP_aQn0_eq_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) :
    ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ i Φ x *
          (Submission.BoseGases.aQ ℓ i (fun y : Submission.BoseGases.X n =>
            ∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ y) x) = 0 := by
  classical
  -- the fibre-mean sum `n₀Φ = ∑ⱼ PⱼΦ` is continuous
  have hΨc : Continuous (fun y : Submission.BoseGases.X n =>
      ∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ y) :=
    continuous_finsetSum (Finset.univ : Finset (Fin n))
      (fun j _ => Submission.BoseGases.aP_continuous hℓ j hΦc)
  -- each slot contributes `∫ (PᵢΦ)·(QᵢΨ) = 0`
  refine Finset.sum_eq_zero (fun i _ => ?_)
  exact aP_mul_aQ_box hℓ i hΦc hΨc

end Work.BoseBoxFock
