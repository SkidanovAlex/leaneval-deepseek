import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.EngineRoadmap
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.HB4_1
import Submission.Work.ZeroFreeTables.P9F.table9_top
import Submission.Work.ZeroFreeTables.P9F.L52HypOfBurgess
import Submission.Work.LinnikAreas.area1

namespace Work.ZeroFreeTables

/-- The analytic input of Table 9 (`P9F.L52Supply`): Heath-Brown's Lemma 3.1 with `φ = 1/3`
(Burgess), in the window form `L52Hyp` with the constant `1/6 + 10⁻⁶`, from the **hypothesis**
`LBound13` (`= Area1.1`); see `P9F/L52HypOfBurgess.lean`. -/
theorem L52Supply_of_burgess (hBurg : Work.LinnikContract.LBound13) : P9F.L52Supply := by
  obtain ⟨δ, hδ0, hδ1, q₀, hq₀⟩ := P9F.l52HypExplicit_of_LBound13 hBurg
  exact ⟨δ, hδ0, hδ1, q₀, fun q hq _inst χ _instc hχ ε hε => hq₀ q hq χ hχ ε hε⟩

/-- **HB Table 9** (p. 55): `λ_j` in the complex case, for `χ₁` of order at least `3` — from
`LBound13` (`Area1.1`). -/
theorem HBTable9_of_burgess (hBurg : Work.LinnikContract.LBound13) :
    Work.ZeroFreeTables.HBTable9 :=
  P9F.HBTable9_of_supply (L52Supply_of_burgess hBurg)

/-- **HB Table 9** (p. 55), unconditionally: `λ_j` in the complex case, for `χ₁` of order at least
`3`.  The only analytic input is `Area1.1 = LBound13` (HB Lemma 2.5 with `φ = 1/3`, i.e. the
Burgess input), which is `Work.LinnikAreas.LBound13_holds`; the whole Table 9 computation itself
is in `P9F/table9_top.lean` (the twenty row lemmas `row_*` and `HBTable9_of_supply`). -/
theorem HBTable9_proof : Work.ZeroFreeTables.HBTable9 :=
  HBTable9_of_burgess Work.LinnikAreas.LBound13_holds

end Work.ZeroFreeTables
