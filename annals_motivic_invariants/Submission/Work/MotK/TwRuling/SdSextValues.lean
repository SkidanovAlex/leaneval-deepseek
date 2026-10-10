import Mathlib
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.KleinTwData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000

namespace Work.MotK.TwRuling

-- The explicit values of the ruling data of the T-twisted Crauder--Katz link at the point
-- `c = (a, 0, -a, -b, b)` of the twisted Klein curve (`kleinTwP a b 1 c = 0`, first three
-- conjuncts), together with the evaluation of the cubic map `kleinTwR0` on the ruling line
-- `ℓ_c = {A(c) + S·B(c)}`, which is the sextic of the design's node `K5`.
theorem SdSextValues {R : Type*} [CommRing R] (a b S : R) :
    Work.MotK.kleinTwRuleA a b 1 ![a, 0, -a, -b, b]
        = ![0, a ^ 2 * b ^ 4, -(2 * a ^ 5 * b + b ^ 6), -(a * b ^ 5), 2 * a ^ 5 * b] ∧
    Work.MotK.kleinTwRuleB a b 1 ![a, 0, -a, -b, b]
        = ![0, 3 * a ^ 4 * b ^ 2, -(a ^ 2 * b ^ 4), -(3 * a ^ 3 * b ^ 3), -(2 * a ^ 2 * b ^ 4)] ∧
    Work.MotK.kleinTwP a b 1 ![a, 0, -a, -b, b] = 0 ∧
    Work.MotK.kleinTwR0 a b 1 (fun i => Work.MotK.kleinTwRuleA a b 1 ![a,0,-a,-b,b] i
        + S * Work.MotK.kleinTwRuleB a b 1 ![a,0,-a,-b,b] i)
      = -(a ^ 3 * b ^ 4) * (27 * S ^ 3 * a ^ 11 * b ^ 4 - 11 * S ^ 3 * a ^ 6 * b ^ 9
          + 57 * S ^ 2 * a ^ 9 * b ^ 6 - S ^ 2 * a ^ 4 * b ^ 11
          + 29 * S * a ^ 7 * b ^ 8 + 3 * S * a ^ 2 * b ^ 13
          + 8 * a ^ 15 + 8 * a ^ 10 * b ^ 5 + 7 * a ^ 5 * b ^ 10 + b ^ 15) := by
  have hA : Work.MotK.kleinTwRuleA a b 1 ![a, 0, -a, -b, b]
      = ![0, a ^ 2 * b ^ 4, -(2 * a ^ 5 * b + b ^ 6), -(a * b ^ 5), 2 * a ^ 5 * b] := by
    funext i
    fin_cases i <;>
      · unfold Work.MotK.kleinTwRuleA Work.MotK.kleinTwPolarP Work.MotK.kleinTwTan
          Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP
          Work.MotK.kleinTwP0 Work.MotK.kleinTwP1 Work.MotK.kleinTwP2 Work.MotK.kleinTwP3
          Work.MotK.kleinTwP4 Work.MotK.kleinE
        simp only [Pi.single_apply, Fin.isValue]
        norm_num
        first | refl_ring1 | ring
  have hB : Work.MotK.kleinTwRuleB a b 1 ![a, 0, -a, -b, b]
      = ![0, 3 * a ^ 4 * b ^ 2, -(a ^ 2 * b ^ 4), -(3 * a ^ 3 * b ^ 3),
          -(2 * a ^ 2 * b ^ 4)] := by
    funext i
    fin_cases i <;>
      · unfold Work.MotK.kleinTwRuleB Work.MotK.kleinTwPolarP Work.MotK.kleinTwTan
          Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP
          Work.MotK.kleinTwP0 Work.MotK.kleinTwP1 Work.MotK.kleinTwP2 Work.MotK.kleinTwP3
          Work.MotK.kleinTwP4 Work.MotK.kleinE
        simp only [Pi.single_apply, Fin.isValue]
        norm_num
        first | refl_ring1 | ring
  have hP : Work.MotK.kleinTwP a b 1 ![a, 0, -a, -b, b] = 0 := by
    funext i
    fin_cases i <;>
      · unfold Work.MotK.kleinTwP Work.MotK.kleinTwP0 Work.MotK.kleinTwP1 Work.MotK.kleinTwP2
          Work.MotK.kleinTwP3 Work.MotK.kleinTwP4
        simp only [Fin.isValue]
        norm_num
        first | refl_ring1 | ring
  refine ⟨hA, hB, hP, ?_⟩
  rw [hA, hB]
  unfold Work.MotK.kleinTwR0
  simp only [Fin.isValue]
  norm_num
  first | refl_ring1 | ring

end Work.MotK.TwRuling
