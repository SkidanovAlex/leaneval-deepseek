import Mathlib
import ChallengeDeps
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.aK`, `Work.MotC5N3.bK` — the Klein parameters pushed to a general base field

Generic (`K` in place of `RatFunc 𝕜`) versions of `Work.MotAS.aK` / `Work.MotAS.bK`
(`Submission/Work/MotAS/AK.lean`): the coefficients `a`, `b` of a Klein datum `D` over `𝕜`, pushed
into the base field `K` of the Artin–Schreier link.

Together with the vocabulary of `Submission/Work/MotC5N3/Defs.lean` these are the only definitions
the census (`Work.MotC5N3.CensusAux.CensusAS2Gen`) needs; everything else it consumes is already
generic in the coordinates `(a, b, g)` in `Submission/Work/MotAS/{CensusAS2,CensusAS2Aux}.lean`.
-/

set_option autoImplicit false

namespace Work.MotC5N3
noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- The coefficient `a` of the Klein datum, pushed to the base field `K`. -/
def aK (K : Type) [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) : K :=
  algebraMap 𝕜 K D.a

/-- The coefficient `b` of the Klein datum, pushed to the base field `K`. -/
def bK (K : Type) [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) : K :=
  algebraMap 𝕜 K D.b

@[simp] theorem aK_eq (K : Type) [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) :
    aK K D = algebraMap 𝕜 K D.a := rfl

@[simp] theorem bK_eq (K : Type) [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) :
    bK K D = algebraMap 𝕜 K D.b := rfl

/-- `aK ^ 2 - aK * bK - bK ^ 2` is nonzero for the pushed Klein data of `ASGood D`.
(Generic form of `Work.MotAS.aK_sq_sub_ne`, `Submission/Work/MotAS/CensusLinAS.lean`.) -/
theorem aK_sq_sub_ne {K : Type} [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    aK K D ^ 2 - aK K D * bK K D - bK K D ^ 2 ≠ 0 := by
  have hcoe : aK K D ^ 2 - aK K D * bK K D - bK K D ^ 2
      = (algebraMap 𝕜 K) (D.a ^ 2 - D.a * D.b - D.b ^ 2) := by
    simp only [aK, bK, map_sub, map_mul, map_pow]
  rw [hcoe]
  intro h
  exact hD.2.2.2 ((algebraMap 𝕜 K).injective (by rw [h, map_zero]))

/-- The `aK`-clause in the form used by the census: `a ≠ 0`. -/
theorem aK_ne_zero {K : Type} [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) : aK K D ≠ 0 := by
  rw [aK]
  intro h
  have h0 : D.a = 0 := (algebraMap 𝕜 K).injective (by rw [h, map_zero])
  exact hD.1.ab_ne (by rw [h0, zero_mul])

/-- The `bK`-clause in the form used by the census: `b ≠ 0`. -/
theorem bK_ne_zero {K : Type} [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) : bK K D ≠ 0 := by
  rw [bK]
  intro h
  have h0 : D.b = 0 := (algebraMap 𝕜 K).injective (by rw [h, map_zero])
  exact hD.1.ab_ne (by rw [h0, mul_zero])

end
end Work.MotC5N3
