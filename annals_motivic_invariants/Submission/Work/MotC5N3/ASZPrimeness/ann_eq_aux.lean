import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZGC.Defs
import Submission.Work.MotAS.ASRulV2M.ASZQuadDetGen
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary data for `Work.MotC5N3.ASZPrimeness.ann_eq_gen`

This file collects the two "normalisation" identities that the colon statement
`(P, D0) : (R0) ⊆ (P, D0, R0)` of the AS residual plane model needs, together with the
`X 0`-decomposition of the graph coefficient `D0`.

* `D0_eq_ziasGraphD0`, `R0_eq_ziasGraphR` : `ASZGC.D0`/`ASZGC.R0` agree with the `ziasGraph*`
  normalisation used by `Work.MotAS.ASRulV2M.ASZQuadDetGen` (they differ by a multiple of `5`).
* `M0` and `D0_decomp` : in characteristic `5`,
  `D0 = -(2(a + 2b)^6) + X 0 · M0`, i.e. `D0` has a *unit* constant coefficient in `X 0`;
  equivalently `X 0` is a unit modulo `(D0)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.MotC5N3.ASZPrimeness

open MvPolynomial

/-- `ASZGC.D0` agrees with `ziasGraphD0` in characteristic `5` (the two normalisations use
different representatives of the same coefficients modulo `5`). -/
theorem D0_eq_ziasGraphD0 (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotAS.ASZGC.D0 a b g = Work.MotAS.ziasGraphD0 a b g := by
  rw [Work.MotAS.ASZGC.D0, Work.MotAS.ziasGraphD0]
  haveI hchar : CharP (MvPolynomial (Fin 2) K) 5 := inferInstance
  simp only [map_mul, map_pow, map_neg, map_ofNat, map_natCast,
    MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_add, MvPolynomial.C_neg,
    MvPolynomial.C_1, MvPolynomial.C_0]
  reduce_mod_char!

/-- `ASZGC.R0` agrees with `ziasGraphR` in characteristic `5`. -/
theorem R0_eq_ziasGraphR (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotAS.ASZGC.R0 a b g = Work.MotAS.ziasGraphR a b g := by
  rw [Work.MotAS.ASZGC.R0, Work.MotAS.ziasGraphR]
  haveI hchar : CharP (MvPolynomial (Fin 2) K) 5 := inferInstance
  simp only [map_mul, map_pow, map_neg, map_ofNat, map_natCast,
    MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_add, MvPolynomial.C_neg,
    MvPolynomial.C_1, MvPolynomial.C_0]
  reduce_mod_char!

/-- The `X 0`-cofactor of `D0`: in characteristic `5`,
`D0 = C (-(2(a + 2b)^6)) + X 0 · M0`. -/
noncomputable def M0 (K : Type) [Field K] (a b g : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (4 * b ^ 6 + 3 * a * b ^ 5 + 2 * a ^ 5 * b + 4 * a ^ 6)
    + MvPolynomial.C (a * b * (a + 2 * b) ^ 4) * MvPolynomial.X 0
    + MvPolynomial.C (g * (a + 2 * b) ^ 6) * MvPolynomial.X 1

/-- The integral form of `D0_decomp`: the difference is an explicit multiple of `5`, so this is
a polynomial identity in every commutative ring. -/
theorem D0_sub_decomp (K : Type) [Field K] (a b g : K) :
    Work.MotAS.ASZGC.D0 a b g
        - (MvPolynomial.C (-(2 * (a + 2 * b) ^ 6))
            + MvPolynomial.X 0 * M0 K a b g)
      = 5 * (MvPolynomial.C (a ^ 6 + 5 * a ^ 5 * b + 24 * a ^ 4 * b ^ 2 + 64 * a ^ 3 * b ^ 3
              + 96 * a ^ 2 * b ^ 4 + 77 * a * b ^ 5 + 26 * b ^ 6)
          - MvPolynomial.C (a ^ 4 * b ^ 2) * MvPolynomial.X 0 ^ 2
          - 4 * (MvPolynomial.C (a ^ 3 * b ^ 3) * MvPolynomial.X 0 ^ 2)
          - 6 * (MvPolynomial.C (a ^ 2 * b ^ 4) * MvPolynomial.X 0 ^ 2)
          - 3 * (MvPolynomial.C (a * b ^ 5) * MvPolynomial.X 0 ^ 2)
          - 2 * (MvPolynomial.C (a ^ 5 * b * g) * (MvPolynomial.X 0 * MvPolynomial.X 1))
          - 12 * (MvPolynomial.C (a ^ 4 * b ^ 2 * g) * (MvPolynomial.X 0 * MvPolynomial.X 1))
          - 32 * (MvPolynomial.C (a ^ 3 * b ^ 3 * g) * (MvPolynomial.X 0 * MvPolynomial.X 1))
          - 48 * (MvPolynomial.C (a ^ 2 * b ^ 4 * g) * (MvPolynomial.X 0 * MvPolynomial.X 1))
          - 38 * (MvPolynomial.C (a * b ^ 5 * g) * (MvPolynomial.X 0 * MvPolynomial.X 1))
          - 12 * (MvPolynomial.C (b ^ 6 * g) * (MvPolynomial.X 0 * MvPolynomial.X 1))) := by
  simp only [Work.MotAS.ASZGC.D0, M0, map_add, map_sub, map_mul, map_pow, map_one, map_zero,
    map_neg, map_ofNat, map_natCast]
  first | refl_ring1 | ring

/-- The `X 0`-decomposition of the graph coefficient:
`D0 = C (-(2(a + 2b)^6)) + X 0 · M0` in characteristic `5`. -/
theorem D0_decomp (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotAS.ASZGC.D0 a b g
      = MvPolynomial.C (-(2 * (a + 2 * b) ^ 6)) + MvPolynomial.X 0 * M0 K a b g := by
  have h := D0_sub_decomp K a b g
  have h5 : (5 : MvPolynomial (Fin 2) K) = 0 := CharP.cast_eq_zero _ 5
  rw [h5, zero_mul] at h
  exact sub_eq_zero.mp h

end Work.MotC5N3.ASZPrimeness
