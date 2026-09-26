import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KPlusRefCoeffs

/-!
# The `Sm1Ref` `q`-expansion: `Φ_ref - Φ_ref^0 = q·Q₁ + q²·W0q`

`Sm1Ref = j(τ)(Φ_ref - Φ_ref^0) - E4Ref³·Q₁·(q·DeltaInvRef - 1) - E4Ref³·W0'·DeltaInvRef`.

* The second summand is already a polynomial in `q`: `q·DeltaInvRef - 1 = 24q`
  (`DeltaInvRef_mul_q`), so it contributes `E4Ref³·Q₁·24q`.
* The first summand needs the `q`-expansion of `Φ_ref - Φ_ref^0` (with `Φ_ref^0 = Phiref`).
  Computing it from the reference definitions gives
  `Φ_ref - Phiref = q·Q₁ + q²·W0q`, an identity in the `τ`-atoms and `S0z z`: the `q⁰` term is
  *exactly* `0` (the `q⁰` parts of `Φ_ref` and `Phiref` coincide: both are
  `6(r₀+r₂)(1-S0²) + r₁(-12j + 8640 + (12j-12096)S0²) + 3456 r₁ S0`), and the `q¹` term is
  *exactly* `Q₁`.
* Consequently `W0' = Φ_ref - Phiref - qQ₁ = q²·W0q`, so the third summand is
  `E4Ref³·q²·W0q·(q⁻¹ + 24) = E4Ref³·(q + 24q²)·W0q` — a polynomial in `q`, the `q⁻¹` cancelling
  against `q²`.

So `Sm1Ref` is a polynomial in `q` of degree `≤ 7`, all of whose coefficients are now explicit.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- The `q²`-onwards part of `Φ_ref - Phiref`, extracted from the reference definitions. -/
def W0q (τ z : ℍ) : ℂ :=
  (9504 * (Work.Asymptotics.K24F.r0 τ + Work.Asymptotics.K24F.r2 τ)
      + 864 * (Work.Asymptotics.K24F.r0 τ + Work.Asymptotics.K24F.r2 τ)
          * Work.Asymptotics.K24F.S0 z
      + 73156608 * Work.Asymptotics.K24F.r1 τ
      + 553900032 * Work.Asymptotics.K24F.r1 τ * Work.Asymptotics.K24F.S0 z
      - 19008 * Work.Asymptotics.K24F.r1 τ * Work.Kernels.jInvariantFun τ
      - 1728 * Work.Asymptotics.K24F.r1 τ * Work.Kernels.jInvariantFun τ
          * Work.Asymptotics.K24F.S0 z)
    + Work.Kernels.qParamFun z
        * (-20736 * (Work.Asymptotics.K24F.r0 τ + Work.Asymptotics.K24F.r2 τ)
            - 13108469760 * Work.Asymptotics.K24F.r1 τ
            + 461155368960 * Work.Asymptotics.K24F.r1 τ * Work.Asymptotics.K24F.S0 z
            + 41472 * Work.Asymptotics.K24F.r1 τ * Work.Kernels.jInvariantFun τ)
    + (Work.Kernels.qParamFun z) ^ 2
        * (-31104 * (Work.Asymptotics.K24F.r0 τ + Work.Asymptotics.K24F.r2 τ)
            - 11107546951680 * Work.Asymptotics.K24F.r1 τ
            - 230452452311040 * Work.Asymptotics.K24F.r1 τ * Work.Asymptotics.K24F.S0 z
            + 62208 * Work.Asymptotics.K24F.r1 τ * Work.Kernels.jInvariantFun τ)
    + (Work.Kernels.qParamFun z) ^ 3 * (5497655668899840 * Work.Asymptotics.K24F.r1 τ)
    + (Work.Kernels.qParamFun z) ^ 4 * (16592576566394880 * Work.Asymptotics.K24F.r1 τ)

/-- **The `q`-expansion of `Φ_ref - Phiref`**: `= q·Q₁ + q²·W0q`. -/
lemma PhiRef_sub_Phiref_eq (τ z : ℍ) :
    PhiRef τ z - Work.Asymptotics.K24F.Phiref τ z
      = Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Q1 τ z
        + (Work.Kernels.qParamFun z) ^ 2 * W0q τ z := by
  have hS0 : Work.Asymptotics.KhatE1.S0z z = Work.Asymptotics.K24F.S0 z := rfl
  simp only [PhiRef, PfunRef, VfunRef, E4Ref, E2SRef, E14Ref, I4Ref, W0q,
    Work.Asymptotics.K24F.Phiref, Work.Asymptotics.K24F.Pref,
    Work.Asymptotics.K24F.Q1, Work.Asymptotics.K24F.P1]
  rw [hS0]
  ring

/-- **`W0' = q²·W0q`**: `Φ_ref - Phiref - qQ₁ = q²·W0q`. -/
lemma W0'_factor (τ z : ℍ) :
    W0' τ z = (Work.Kernels.qParamFun z) ^ 2 * W0q τ z := by
  have h := PhiRef_sub_Phiref_eq τ z
  simp only [W0']
  rw [h]
  ring

/-- **The `q⁻¹` cancellation in the third summand**: `W0'·DeltaInvRef` is a polynomial in `q`. -/
lemma W0'_mul_DeltaInvRef (τ z : ℍ) :
    W0' τ z * DeltaInvRef z
      = W0q τ z * (Work.Kernels.qParamFun z + 24 * (Work.Kernels.qParamFun z) ^ 2) := by
  have hq := q_mul_qinv z
  rw [W0'_factor τ z]
  simp only [DeltaInvRef]
  linear_combination (Work.Kernels.qParamFun z * W0q τ z) * hq

/-- **The second summand of `Sm1Ref` in `q`-form**: `E4Ref³·Q₁·(q·DeltaInvRef - 1)
= E4Ref³·Q₁·24q`. -/
lemma Sm1Ref_term2_q (τ z : ℍ) :
    E4Ref z ^ 3 * Work.Asymptotics.K24F.Q1 τ z
        * (Work.Kernels.qParamFun z * DeltaInvRef z - 1)
      = E4Ref z ^ 3 * Work.Asymptotics.K24F.Q1 τ z * (24 * Work.Kernels.qParamFun z) := by
  rw [DeltaInvRef_mul_q z]

end

end Work.Asymptotics.KhatE1Core
