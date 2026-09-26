import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Sm4RefCoeffs

/-!
# Packaging the `K₊` reference `E²` coefficient: `KPlusQ1`

All five `Sm_iRef` are explicit polynomials in `q = qParamFun z`, so the `E²`-coefficient of
`KPlus24Ref = -(c·z²·KPlusSumRef)` is the `q¹`-coefficient of `KPlusSumRef`, and that quartic
is the sum of the five `q¹`-coefficients.  This module

* consolidates `Sm1Ref` into its `q`-form (the three summands of `Sm1RefCoeffs` combined), and
* records the `q¹`-coefficient of each `Sm_iRef` (`Sm2Ref_q1` … `Sm5Ref_q1`, each a rearrangement
  of the corresponding `_qexp`), and
* defines `KPlusQ1` as their sum: the `E²`-coefficient of `KPlusSumRef`.

`KPlusQ1` is an explicit expression in the `τ`-atoms (`E2Fun`, `E4Fun`, `E6Fun`, `jInvariantFun`,
`psi2`, `psi4`, `r0`, `r1`, `r2`, `R0`, `Q1`, `Phiref`, `Th0`, `Uref`, `(τ:ℂ)`) and in
`S0z z` only — no `q`-expansion remains on the plus side.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-! ## `Sm1Ref` consolidated into `q`-form -/

/-- The `q⁰`-part of `W0q`, i.e. the `q²`-coefficient of `Φ_ref - Phiref` (needed on its own as
the `E²`-contribution of the third summand of `Sm1Ref`). -/
def W0q0 (τ z : ℍ) : ℂ :=
  9504 * (Work.Asymptotics.K24F.r0 τ + Work.Asymptotics.K24F.r2 τ)
    + 864 * (Work.Asymptotics.K24F.r0 τ + Work.Asymptotics.K24F.r2 τ)
        * Work.Asymptotics.K24F.S0 z
    + 73156608 * Work.Asymptotics.K24F.r1 τ
    + 553900032 * Work.Asymptotics.K24F.r1 τ * Work.Asymptotics.K24F.S0 z
    - 19008 * Work.Asymptotics.K24F.r1 τ * Work.Kernels.jInvariantFun τ
    - 1728 * Work.Asymptotics.K24F.r1 τ * Work.Kernels.jInvariantFun τ
        * Work.Asymptotics.K24F.S0 z

/-- `W0q = W0q0 + q·(…) + q²·(…)`, i.e. `W0q0` really is the `q⁰`-part of `W0q`. -/
lemma W0q_eq_W0q0_add (τ z : ℍ) :
    ∃ W : ℂ, W0q τ z = W0q0 τ z + Work.Kernels.qParamFun z * W :=
  ⟨(-20736 * (Work.Asymptotics.K24F.r0 τ + Work.Asymptotics.K24F.r2 τ)
        - 13108469760 * Work.Asymptotics.K24F.r1 τ
        + 461155368960 * Work.Asymptotics.K24F.r1 τ * Work.Asymptotics.K24F.S0 z
        + 41472 * Work.Asymptotics.K24F.r1 τ * Work.Kernels.jInvariantFun τ)
      + Work.Kernels.qParamFun z
          * (-31104 * (Work.Asymptotics.K24F.r0 τ + Work.Asymptotics.K24F.r2 τ)
              - 11107546951680 * Work.Asymptotics.K24F.r1 τ
              - 230452452311040 * Work.Asymptotics.K24F.r1 τ * Work.Asymptotics.K24F.S0 z
              + 62208 * Work.Asymptotics.K24F.r1 τ * Work.Kernels.jInvariantFun τ)
      + (Work.Kernels.qParamFun z) ^ 2 * (5497655668899840 * Work.Asymptotics.K24F.r1 τ)
      + (Work.Kernels.qParamFun z) ^ 3 * (16592576566394880 * Work.Asymptotics.K24F.r1 τ),
    by simp only [W0q, W0q0]; ring⟩

/-- **`Sm1Ref` in consolidated `q`-form**: the three summands of `Sm1RefCoeffs` combined.  Its
`E²`-coefficient (the coefficient of `q¹`) is therefore `j(τ)Q₁ - 24 Q₁ - W0q0`. -/
lemma Sm1Ref_qform (τ z : ℍ) :
    Sm1Ref τ z
      = Work.Kernels.jInvariantFun τ
          * (Work.Kernels.qParamFun z * Work.Asymptotics.K24F.Q1 τ z
              + (Work.Kernels.qParamFun z) ^ 2 * W0q τ z)
        - E4Ref z ^ 3 * Work.Asymptotics.K24F.Q1 τ z * (24 * Work.Kernels.qParamFun z)
        - E4Ref z ^ 3 * W0q τ z
            * (Work.Kernels.qParamFun z + 24 * (Work.Kernels.qParamFun z) ^ 2) := by
  have h1 := PhiRef_sub_Phiref_eq τ z
  have h2 := Sm1Ref_term2_q τ z
  have h3' : E4Ref z ^ 3 * W0' τ z * DeltaInvRef z
      = E4Ref z ^ 3
          * (W0q τ z * (Work.Kernels.qParamFun z + 24 * (Work.Kernels.qParamFun z) ^ 2)) := by
    rw [mul_assoc, W0'_mul_DeltaInvRef τ z]
  simp only [Sm1Ref]
  rw [h1, h2, h3']
  ring

/-! ## The five `q¹`-coefficients -/

/-- **`Sm2Ref`'s `E²`-coefficient.** -/
lemma Sm2Ref_q1 (τ z : ℍ) :
    Sm2Ref τ z
      = Work.Kernels.qParamFun z
          * (24 * Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z)
        + (Work.Kernels.qParamFun z) ^ 2
            * (-252 * Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z) :=
  Sm2Ref_qexp τ z

/-- **`Sm5Ref`'s `E²`-coefficient.** -/
lemma Sm5Ref_q1 (τ z : ℍ) :
    Sm5Ref τ z
      = Work.Kernels.qParamFun z
          * (-(Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Th0 τ z))
        + (Work.Kernels.qParamFun z) ^ 2
            * (24 * Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Th0 τ z)
        + (Work.Kernels.qParamFun z) ^ 3
            * (-252 * Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Th0 τ z) :=
  Sm5Ref_qexp τ z

/-! ## The packaged `E²`-coefficient of the `K₊` reference -/

/-- **The `E²`-coefficient (= `q¹`-coefficient) of `KPlusSumRef`**, i.e. the sum of the `q¹`
coefficients of the five `Sm_iRef`. -/
def KPlusQ1 (τ z : ℍ) : ℂ :=
  -- `Sm1Ref`: `j(τ)Q₁ - 24 Q₁ - W0q0`
  (Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Q1 τ z
      - 24 * Work.Asymptotics.K24F.Q1 τ z - W0q0 τ z)
  -- `Sm2Ref`: `24 j(τ)Φ_ref`
  + 24 * Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z
  -- `Sm3Ref`: `82944 R₀ + 5059584 R₀S0`
  + (82944 + 5059584 * Work.Asymptotics.K24F.S0 z) * Work.Asymptotics.K24F.R0 τ
  -- `Sm4Ref`: `-82944 r₀S0 + 414720 r₂ - 720 Uref`
  + (-82944 * Work.Asymptotics.K24F.r0 τ * Work.Asymptotics.K24F.S0 z
      + 414720 * Work.Asymptotics.K24F.r2 τ - 720 * Work.Asymptotics.K24F.Uref τ z)
  -- `Sm5Ref`: `-(j(τ)Θ₀)`
  + (-(Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Th0 τ z))

end

end Work.Asymptotics.KhatE1Core
