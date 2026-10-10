import Mathlib
import Submission.Work.MotAS.azThetaDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.Az

/-- `aeval` commutes with the AS stereographic map (the AS analogue of
`Work.MotK.TGen.aeval_kleinTwStereo_gen` in `Submission/Work/MotK/TGen/AevalFwPoly.lean`).
Route: `fin_cases i`, unfold `kleinStereoAS`, `kleinQAS`, `kleinBilinAS`, push `aeval` through the
ring operations with `map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat,
MvPolynomial.aeval_C` and `ring`/`ring_nf`. -/
theorem aeval_kleinStereoAS_gen {K A σ : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a b : K) (P V : Fin 5 → MvPolynomial σ K) (y : σ → A) (i : Fin 5) :
    MvPolynomial.aeval y (Work.MotAS.kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) P V i)
      = Work.MotAS.kleinStereoAS (algebraMap K A a) (algebraMap K A b)
          (fun j => MvPolynomial.aeval y (P j)) (fun j => MvPolynomial.aeval y (V j)) i := by
  simp only [Work.MotAS.kleinStereoAS, Work.MotAS.kleinBilinAS, Work.MotAS.kleinQAS,
    Pi.add_apply]
  simp only [map_add, map_sub, map_mul, map_neg, map_pow, MvPolynomial.aeval_C, map_ofNat]

end Work.MotAS.Az
