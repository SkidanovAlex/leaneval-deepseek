import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.TGen.CubTRedDefs
import Submission.Work.MotK.TGen.CubTPara
import Submission.Work.MotK.TGen.BwVec4Prime
import Submission.Work.MotK.TGen.CubTFactor
import Submission.Work.MotK.TGen.CubTPrimeAlt
import Submission.Work.MotK.TGen.CubTResidue
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

theorem CubTRational (K : Type) [Field K] (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∃ hpr : (Ideal.span {Work.MotK.TGen.cubT a b h} : Ideal (MvPolynomial (Fin 3) K)).IsPrime,
      Ideal.height (Ideal.span {Work.MotK.TGen.cubT a b h} : Ideal (MvPolynomial (Fin 3) K)) = 1 ∧
      Nonempty (Work.MotV.resF K ⟨Ideal.span {Work.MotK.TGen.cubT a b h}, hpr⟩ ≃ₐ[K]
        RatFunc (RatFunc K)) := by
  -- `cubT` is a unit multiple of the explicit cubic `cubTRed`
  have hfac : cubT a b h = MvPolynomial.C (a * b * h) * cubTRed a b h :=
    CubTFactor K a b h ha hb hh
  have hunit : IsUnit (MvPolynomial.C (a * b * h) : MvPolynomial (Fin 3) K) :=
    IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha hb) hh))
  have hspan : (Ideal.span {cubT a b h} : Ideal (MvPolynomial (Fin 3) K)) = cubTIdeal a b h := by
    rw [hfac, Ideal.span_singleton_mul_left_unit hunit]
    rfl
  rw [hspan]
  -- `cubTRed` is prime, hence so is its principal ideal, and the latter has height one
  have hprimeH : Prime (cubTRed a b h) := CubTPrimeAlt K a b h ha hb hh
  have hne : cubTRed a b h ≠ 0 := hprimeH.ne_zero
  have hnotunit : ¬ IsUnit (cubTRed a b h) := hprimeH.not_unit
  -- the residue field of `(cubTRed)` is the rational surface
  obtain ⟨hiso⟩ := CubTResidue K a b h ha hb hh hprimeH
  exact ⟨(Ideal.span_singleton_prime hne).mpr hprimeH,
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hne) hnotunit,
    ⟨hiso⟩⟩

end Work.MotK.TGen
