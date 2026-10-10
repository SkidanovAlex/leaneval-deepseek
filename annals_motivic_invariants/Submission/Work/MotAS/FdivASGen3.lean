import Mathlib
import Submission.Work.MotAS.CensusASGen
import Submission.Work.MotV5.CensusAux.fAS_notMem_pe
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The third component of the forward chart map is a non-zero denominator

Item 3 of the repair plan for `MotAS.linkCertAS` (`Submission/Work/MotAS/Guide_AS.lean`): with
`i = 3` as the normalising component of the affine chart, the source denominator

  `FdivAS_gen · 3 = linAS · sAS · fwVecAS · 3`

is non-zero as soon as `fwVecAS · 3 ≠ 0`, `sAS ≠ 0` and the unit `linAS` are non-zero.  This file
supplies the first of these, which is the only one that needs the (degenerate) chart data:

* `MotAS.ne_zero_331776` : `331776 ≠ 0` in characteristic `5` (`331776 = 5 · 66355 + 1`);
* `MotAS.fAS_ne_zero` : `fAS 𝕜 = X³ + X ≠ 0`, immediate from the proved
  `Work.MotV5.CensusAux.fAS_notMem_pe` (`fAS` is not an Artin–Schreier value, and `0` is one);
* `MotAS.fwVecAS_three_ne_zero_gen`, `MotAS.fwVecAS_three_ne_zero` : `fwVecAS a b g 3 ≠ 0`, by
  evaluating at the origin of the chart, where the value is `331776 · g · (a² − ab − b²)³`
  (`MotAS.aeval_zero_fwVecAS_three`).

The companion facts `sAS ≠ 0` and `GdivAS ≠ 0` are part of the class/junk clauses of
`MotAS.CensusAS_gen` and are being proved in the sibling files.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

namespace Work.MotAS

open MvPolynomial

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- `331776 = 5 · 66355 + 1` is nonzero in a ring of characteristic `5`. -/
theorem ne_zero_331776 {K : Type*} [CommRing K] [Nontrivial K] [CharP K 5] :
    ((331776 : ℕ) : K) ≠ 0 := by
  have h5 : ((5 : ℕ) : K) = 0 := CharP.cast_eq_zero K 5
  rw [show (331776 : ℕ) = 5 * 66355 + 1 from by norm_num, Nat.cast_add, Nat.cast_mul, h5,
    zero_mul, zero_add, Nat.cast_one]
  exact one_ne_zero

/-- `fAS 𝕜 = X³ + X` is nonzero: it is not an Artin–Schreier value (`fAS_notMem_pe`), while `0` is
one. -/
theorem fAS_ne_zero : Work.MotV.fAS 𝕜 ≠ 0 := by
  intro h
  refine Work.MotV5.CensusAux.fAS_notMem_pe 𝕜 ⟨0, ?_⟩
  rw [show (RatFunc.X ^ 3 + RatFunc.X : RatFunc 𝕜) = 0 from h]
  first | refl_ring1 | ring

/-- **The third component of the forward chart map is a non-zero polynomial** whenever `g ≠ 0` and
`a² − ab − b² ≠ 0`: evaluating at the origin of the chart gives `331776 g (a² − ab − b²)³`. -/
theorem fwVecAS_three_ne_zero_gen {K : Type*} [Field K] [CharP K 5] (a b g : K) (hg : g ≠ 0)
    (hab : a ^ 2 - a * b - b ^ 2 ≠ 0) : fwVecAS a b g 3 ≠ 0 := by
  intro h
  have h0 := congrArg (MvPolynomial.aeval (fun _ : Fin 3 => (0 : K))) h
  rw [aeval_zero_fwVecAS_three, map_zero] at h0
  exact (mul_ne_zero (mul_ne_zero (ne_zero_331776 (K := K)) hg) (pow_ne_zero 3 hab)) h0

/-- The same for the census data: `fwVecAS (aK D) (bK D) (fAS 𝕜) 3 ≠ 0`.  In particular the third
component is a legitimate chart denominator, whereas the fourth is identically zero
(`MotAS.fwVecAS_four_eq_zero`). -/
theorem fwVecAS_three_ne_zero (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) :
    fwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 3 ≠ 0 :=
  fwVecAS_three_ne_zero_gen (aK D) (bK D) (Work.MotV.fAS 𝕜) fAS_ne_zero (aK_sq_sub_ne D hD)

/-- **`FdivAS_gen · 3 ≠ 0`, modulo `sAS ≠ 0`** — the assembly skeleton for the repaired census:
the source divisor `linAS · sAS · fwVecAS · 3` is non-zero once its three factors are.  Two of the
three are proved here (`MotAS.isUnit_linAS` for the unit `linAS`, `MotAS.fwVecAS_three_ne_zero` for
the third component); the middle factor is `MotAS.censusAS_sAS_ne_zero`, so the moment that lemma is
importable the unconditional form is the one-liner

  `theorem FdivAS_gen_three_ne_zero (D) (hD) : FdivAS_gen (aK D) (bK D) (fAS 𝕜) 3 ≠ 0 :=
     FdivAS_gen_three_ne_zero_of D hD (censusAS_sAS_ne_zero D hD)`

(`MvPolynomial (Fin 3) (RatFunc 𝕜)` is a domain, so `mul_ne_zero` applies). -/
theorem FdivAS_gen_three_ne_zero_of (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (hsAS : sAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ≠ 0) :
    FdivAS_gen (aK D) (bK D) (Work.MotV.fAS 𝕜) 3 ≠ 0 := by
  have hlin : linAS (aK D) (bK D) ≠ 0 := (isUnit_linAS D hD).ne_zero
  have hfw : fwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 3 ≠ 0 := fwVecAS_three_ne_zero D hD
  have hfac : FdivAS_gen (aK D) (bK D) (Work.MotV.fAS 𝕜) 3
      = linAS (aK D) (bK D) * sAS (aK D) (bK D) (Work.MotV.fAS 𝕜)
          * fwVecAS (aK D) (bK D) (Work.MotV.fAS 𝕜) 3 := rfl
  rw [hfac]
  exact mul_ne_zero (mul_ne_zero hlin hsAS) hfw

end Work.MotAS
