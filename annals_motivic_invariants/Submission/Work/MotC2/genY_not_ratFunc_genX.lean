import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.Translation

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open Polynomial WeierstrassCurve.Affine
open scoped IntermediateField

theorem genY_not_ratFunc_genX (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic] :
    ¬ ∃ P Q : Polynomial L, Q ≠ 0 ∧
      algebraMap (Polynomial L) (Work.MotC2.Func E) P =
        Work.MotC2.genY E * algebraMap (Polynomial L) (Work.MotC2.Func E) Q := by
  classical
  rintro ⟨P, Q, hQ, hPQ⟩
  -- the `L`-algebra structure of `L[X]` on `L(E)` is evaluation at `genX`
  have haeval : ∀ p : Polynomial L,
      algebraMap (Polynomial L) (Func E) p = Polynomial.aeval (genX E) p := by
    have h : (algebraMap (Polynomial L) (Func E)) =
        ((Polynomial.aeval (genX E) : Polynomial L →ₐ[L] Func E) : Polynomial L →+* Func E) := by
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · show algebraMap (Polynomial L) (Func E) (Polynomial.C a)
            = Polynomial.aeval (genX E) (Polynomial.C a)
        rw [Polynomial.aeval_C]
        rfl
      · show algebraMap (Polynomial L) (Func E) Polynomial.X
            = Polynomial.aeval (genX E) Polynomial.X
        rw [Polynomial.aeval_X]
        rfl
    exact fun p => RingHom.congr_fun h p
  simp only [haeval] at hPQ
  -- `genX` is transcendental, so `Q ≠ 0` is not killed by evaluation
  have hQeval : Polynomial.aeval (genX E) Q ≠ 0 := fun h0 =>
    hQ ((transcendental_iff_injective.mp (transcendental_genX E)) (by simpa using h0))
  -- hence `genY` is a rational function of `genX`, contradicting `notMem_adjoin_of_equation`
  refine notMem_adjoin_of_equation E (equation_genX_genY E) (transcendental_genX E) ?_
  rw [IntermediateField.mem_adjoin_simple_iff]
  exact ⟨P, Q, by rw [eq_div_iff hQeval]; exact hPQ.symm⟩

end Work.MotC2
