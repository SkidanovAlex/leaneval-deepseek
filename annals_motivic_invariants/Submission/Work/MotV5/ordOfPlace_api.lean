import Mathlib
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotV5.ordOfPlace_helpers

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

theorem ordOfPlace_api {N : Type*} [Field N] (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S) :
    (∀ f g : Work.MotC2.Func E, f ≠ 0 → g ≠ 0 →
      Work.MotV.ordOfPlace E S hS (f * g) =
        Work.MotV.ordOfPlace E S hS f + Work.MotV.ordOfPlace E S hS g) ∧
    (∀ f : Work.MotC2.Func E, f ≠ 0 →
      Work.MotV.ordOfPlace E S hS f⁻¹ = - Work.MotV.ordOfPlace E S hS f) ∧
    (∀ f : Work.MotC2.Func E, 0 ≤ Work.MotV.ordOfPlace E S hS f ↔ f ∈ S) ∧
    (∀ f g : Work.MotC2.Func E, f + g ≠ 0 →
      min (Work.MotV.ordOfPlace E S hS f) (Work.MotV.ordOfPlace E S hS g) ≤
        Work.MotV.ordOfPlace E S hS (f + g)) ∧
    (∀ f g : Work.MotC2.Func E, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      Work.MotV.ordOfPlace E S hS f < Work.MotV.ordOfPlace E S hS g →
      Work.MotV.ordOfPlace E S hS (f + g) = Work.MotV.ordOfPlace E S hS f) ∧
    (∀ c : N, c ≠ 0 →
      Work.MotV.ordOfPlace E S hS (algebraMap N (Work.MotC2.Func E) c) = 0) ∧
    (∀ f : Work.MotC2.Func E, 0 ≤ Work.MotV.ordOfPlace E S hS f →
      ∃ c : N, f = algebraMap N (Work.MotC2.Func E) c ∨
        1 ≤ Work.MotV.ordOfPlace E S hS (f - algebraMap N (Work.MotC2.Func E) c)) :=
  ⟨OrdAPI.ordOfPlace_mul E S hS, OrdAPI.ordOfPlace_inv E S hS,
    OrdAPI.ordOfPlace_nonneg_iff E S hS, OrdAPI.ordOfPlace_add E S hS,
    OrdAPI.ordOfPlace_add_eq_of_lt E S hS, OrdAPI.ordOfPlace_algebraMap E S hS,
    OrdAPI.ordOfPlace_residue E S hS⟩

end Work.MotV5
