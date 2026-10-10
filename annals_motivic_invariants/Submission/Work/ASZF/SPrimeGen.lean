import Mathlib
import Submission.Work.MotC5N3.X2AuxInputs
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.satGraphIsPrimeGen
import Submission.Work.MotAS.ASZElimP_irreducible
import Submission.Work.MotAS.ASZGC.not_dvd_D0
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000

namespace Work.ASZF

open MvPolynomial

/-- The `X 0`-coefficient `D` of the small graph element, as defined in `X2AuxInputs` (with the
monomials distributed over `X 1, X 2`), is the `Fin.succ`-extension of the two-variable polynomial
`ASZGC.D0`. -/
theorem D_eq_renameD0 (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotC5N3.X2AuxInputs.D a b g
      = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g) := by
  rw [Work.MotC5N3.X2AuxInputs.D, Work.MotAS.ASZGC.D0]
  haveI hchar : CharP (MvPolynomial (Fin 3) K) 5 := inferInstance
  simp only [map_add, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat,
    map_natCast, MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_add, MvPolynomial.C_neg,
    MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.rename_C, MvPolynomial.rename_X,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  reduce_mod_char!
  first | refl_ring1 | ring

/-- The `X 0`-free part `R` of the small graph element, as defined in `X2AuxInputs`, is the
`Fin.succ`-extension of the two-variable polynomial `ASZGC.R0`. -/
theorem R_eq_renameR0 (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotC5N3.X2AuxInputs.R a b g
      = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g) := by
  rw [Work.MotC5N3.X2AuxInputs.R, Work.MotAS.ASZGC.R0]
  haveI hchar : CharP (MvPolynomial (Fin 3) K) 5 := inferInstance
  simp only [map_add, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat,
    map_natCast, MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_add, MvPolynomial.C_neg,
    MvPolynomial.C_1, MvPolynomial.C_0, MvPolynomial.rename_C, MvPolynomial.rename_X,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  reduce_mod_char!
  first | refl_ring1 | ring

theorem SPrimeGen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    (Ideal.span {x : MvPolynomial (Fin 3) K | ∃ N : ℕ,
      (Work.MotC5N3.X2AuxInputs.D a b g) ^ N * x ∈
        Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g,
                    Work.MotC5N3.X2AuxInputs.G a b g}}).IsPrime := by
  have hD := D_eq_renameD0 K a b g
  have hR := R_eq_renameR0 K a b g
  have hkey := Work.MotAS.satGraphIsPrimeGen (K := K) (Work.MotAS.ASZElim.P a b g)
      (Work.MotAS.ASZGC.D0 a b g) (Work.MotAS.ASZGC.R0 a b g)
      (Work.MotAS.ASZElimP_irreducible K a b g ha hg)
      (Work.MotAS.ASZGC.not_dvd_D0 K a b g ha hg)
  simpa only [hD, hR, Work.MotC5N3.X2AuxInputs.Pemb, Work.MotC5N3.X2AuxInputs.G] using hkey

end Work.ASZF
