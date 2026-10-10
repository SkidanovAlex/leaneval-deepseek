import Mathlib
import Submission.Work.MotK.TwRuling.TwFivetenDefs
import Submission.Work.MotK.TwRuling.SdWNdeg
import Submission.Work.MotK.TwRuling.TF5defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-!
# Every monomial `x^a y^b` of pole order `≤ 25` lies in the span of `sdTF5 E`

For a field `R` and a Weierstrass curve `E` over `R`, the 25 monomials of `L(25·O)` are
`sdTF5 E = (x^i)_{i<13} ⊕ (x^j y)_{j<12}`, where `x = genX E`, `y = genY E` in the function
field of `E`.

The proof is strong induction on the `y`-exponent `b`, using the Weierstrass relation solved
for `y²` to trade two powers of `y` against three powers of `x` (the pole weights are
`wt x = 2`, `wt y = 3`), so that the weight `2a + 3b` never increases.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK.TwRuling

noncomputable section

theorem monomial_mem_sdTF5 (R : Type) [Field R] (E : WeierstrassCurve R) (a b : ℕ)
    (h : 2 * a + 3 * b ≤ 25) :
    (Work.MotV.genX E) ^ a * (Work.MotV.genY E) ^ b ∈
      Submodule.span R (Set.range (Work.MotK.TwRuling.sdTF5 E)) := by
  have hrel := hrel' E
  have key : ∀ b a : ℕ, 2 * a + 3 * b ≤ 25 → (gx E) ^ a * (gy E) ^ b ∈ Ssp E := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro a h
      rcases lt_or_ge b 2 with hb | hb
      · interval_cases b
        · rw [pow_zero, mul_one]
          have ha : a < 13 := by omega
          exact Submodule.subset_span (Set.mem_range_self (f := sdTF5 E) (Sum.inl ⟨a, ha⟩))
        · rw [pow_one]
          have ha : a < 12 := by omega
          exact Submodule.subset_span (Set.mem_range_self (f := sdTF5 E) (Sum.inr ⟨a, ha⟩))
      · obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
        have hsplit : (gx E) ^ a * (gy E) ^ (c + 2) =
            (gx E) ^ (a + 3) * (gy E) ^ c
            + algebraMap R _ E.a₂ * ((gx E) ^ (a + 2) * (gy E) ^ c)
            + algebraMap R _ E.a₄ * ((gx E) ^ (a + 1) * (gy E) ^ c)
            + algebraMap R _ E.a₆ * ((gx E) ^ a * (gy E) ^ c)
            - algebraMap R _ E.a₁ * ((gx E) ^ (a + 1) * (gy E) ^ (c + 1))
            - algebraMap R _ E.a₃ * ((gx E) ^ a * (gy E) ^ (c + 1)) := by
          rw [show (gy E) ^ (c + 2) = (gy E) ^ c * (gy E) ^ 2 by rw [pow_add]]
          rw [hrel]
          first | refl_ring1 | ring
        rw [hsplit]
        refine Submodule.sub_mem _ (Submodule.sub_mem _
          (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_
        · exact ih c (by omega) (a + 3) (by omega)
        · exact hsmS E E.a₂ (ih c (by omega) (a + 2) (by omega))
        · exact hsmS E E.a₄ (ih c (by omega) (a + 1) (by omega))
        · exact hsmS E E.a₆ (ih c (by omega) a (by omega))
        · exact hsmS E E.a₁ (ih (c + 1) (by omega) (a + 1) (by omega))
        · exact hsmS E E.a₃ (ih (c + 1) (by omega) a (by omega))
  exact key b a h

end

end Work.MotK.TwRuling
