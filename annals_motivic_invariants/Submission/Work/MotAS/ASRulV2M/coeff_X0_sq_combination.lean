import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZplane.ZIAS_X2_saturated
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRulV2M.coeff_X0_sq_combination`

The `X₀²`-coefficient of `s·C₂ − (s+b)·C₄` (`s = a − 3b`, `C k = zcubAS a b g k`) is `2s⁵`.

The proof uses the chart computation of `Submission/Work/MotAS/ASZplane/ZIAS_X2_saturated.lean`:
`zcubAS a b g k = zQ k + X₂ · zH k`, and the certificate `zE_cert`
`2 s⁴ E = s·Q₂ − (s+b)·Q₄ + 5·J` (valid modulo `5`), where
`E = s X₀² − (s+b) X₁² + s X₁`.  The `X₂`-multiples do not contribute to the `X₀²`-coefficient,
and the `X₀²`-coefficient of `E` is `s`; the result follows.
-/

namespace Work.MotAS.ASRulV2M

open MvPolynomial

theorem coeff_X0_sq_combination (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (MvPolynomial.C (a - 3 * b) * Work.MotAS.zcubAS a b g 2
        - MvPolynomial.C ((a - 3 * b) + b) * Work.MotAS.zcubAS a b g 4).coeff
        (Finsupp.single (0 : Fin 3) 2) = 2 * (a - 3 * b) ^ 5 := by
  classical
  -- The two chart cubics, split off their `X₂`-part.
  have h2 : Work.MotAS.zcubAS a b g 2
      = Work.MotAS.ASZplane.zQ2 a b g + X 2 * Work.MotAS.ASZplane.zH2 a b g :=
    Work.MotAS.ASZplane.zcub2 (R := K) a b g
  have h4 : Work.MotAS.zcubAS a b g 4
      = Work.MotAS.ASZplane.zQ4 a b g + X 2 * Work.MotAS.ASZplane.zH4 a b g :=
    Work.MotAS.ASZplane.zcub4 (R := K) a b g
  -- `zS` and `zS + b` as constants.
  have hzS : Work.MotAS.ASZplane.zS a b
      = (MvPolynomial.C (a - 3 * b) : MvPolynomial (Fin 3) K) := by
    simp only [Work.MotAS.ASZplane.zS, map_sub, map_mul, map_ofNat]
  have hzSb : Work.MotAS.ASZplane.zS a b + MvPolynomial.C b
      = (MvPolynomial.C ((a - 3 * b) + b) : MvPolynomial (Fin 3) K) := by
    rw [hzS, ← map_add]
  -- In characteristic `5` the scalar `5` is zero.
  have hfive : (5 : MvPolynomial (Fin 3) K) = 0 := by
    have h : ((5 : ℕ) : MvPolynomial (Fin 3) K) = 0 := by
      rw [← map_natCast (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) 5,
        CharP.cast_eq_zero, map_zero]
    simpa using h
  -- The scalar `2` is the constant polynomial `C 2`, and `2 · (C s)⁴ = C (2 s⁴)`.
  have h2C : (2 : MvPolynomial (Fin 3) K) = MvPolynomial.C (2 : K) := by
    simpa using (map_natCast (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K) 2).symm
  have h2s : (2 : MvPolynomial (Fin 3) K) * (MvPolynomial.C (a - 3 * b)) ^ 4
      = MvPolynomial.C (2 * (a - 3 * b) ^ 4) := by
    rw [h2C, ← map_pow, ← map_mul]
  -- The certificate `zE_cert`, written in terms of `C (a - 3b)` and `C ((a - 3b) + b)`.
  have hcert : 2 * (MvPolynomial.C (a - 3 * b) : MvPolynomial (Fin 3) K) ^ 4
        * Work.MotAS.ASZplane.zE a b
      = MvPolynomial.C (a - 3 * b) * Work.MotAS.ASZplane.zQ2 a b g
        - MvPolynomial.C ((a - 3 * b) + b) * Work.MotAS.ASZplane.zQ4 a b g
        + 5 * Work.MotAS.ASZplane.zJ1 a b := by
    have h := Work.MotAS.ASZplane.zE_cert (R := K) a b g
    rw [hzSb, hzS] at h
    exact h
  -- The `X₀²`-coefficient of the eliminant relation `E`.
  have hE : (Work.MotAS.ASZplane.zE a b).coeff (Finsupp.single (0 : Fin 3) 2)
      = a - 3 * b := by
    simp only [Work.MotAS.ASZplane.zE]
    rw [hzSb, hzS]
    simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_X_pow, Finsupp.single_eq_single_iff]
    norm_num
  -- The `5 · zJ1`-term is zero.
  have hJ0 : (5 * Work.MotAS.ASZplane.zJ1 a b).coeff (Finsupp.single (0 : Fin 3) 2) = 0 := by
    rw [hfive, zero_mul]
    simp
  -- Splitting off the `X₂`-parts.
  have hsplit : MvPolynomial.C (a - 3 * b) * Work.MotAS.zcubAS a b g 2
        - MvPolynomial.C ((a - 3 * b) + b) * Work.MotAS.zcubAS a b g 4
      = (MvPolynomial.C (a - 3 * b) * Work.MotAS.ASZplane.zQ2 a b g
          - MvPolynomial.C ((a - 3 * b) + b) * Work.MotAS.ASZplane.zQ4 a b g)
        + X 2 * (MvPolynomial.C (a - 3 * b) * Work.MotAS.ASZplane.zH2 a b g
            - MvPolynomial.C ((a - 3 * b) + b) * Work.MotAS.ASZplane.zH4 a b g) := by
    rw [h2, h4]
    first | refl_ring1 | ring
  have hmem : (2 : Fin 3) ∉ (Finsupp.single (0 : Fin 3) 2).support := by simp
  -- The `Q₂`/`Q₄`-combination is `2 s⁴ E − 5 J`.
  have hpoly : MvPolynomial.C (a - 3 * b) * Work.MotAS.ASZplane.zQ2 a b g
        - MvPolynomial.C ((a - 3 * b) + b) * Work.MotAS.ASZplane.zQ4 a b g
      = 2 * (MvPolynomial.C (a - 3 * b) : MvPolynomial (Fin 3) K) ^ 4
          * Work.MotAS.ASZplane.zE a b
        - 5 * Work.MotAS.ASZplane.zJ1 a b := by
    rw [hcert]
    first | refl_ring1 | ring
  rw [hsplit, MvPolynomial.coeff_add, MvPolynomial.coeff_X_mul', if_neg hmem, add_zero, hpoly,
    MvPolynomial.coeff_sub, h2s, MvPolynomial.coeff_C_mul, hE, hJ0, sub_zero]
  first | refl_ring1 | ring

end Work.MotAS.ASRulV2M
