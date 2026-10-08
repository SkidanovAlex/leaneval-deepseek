import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.A7Bridge
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.CORE3.Case1aFrattini
import Submission.Work.CORE3.Case1aAbelian
import Submission.Work.CORE3.Case1aA7
import Submission.Work.CORE3.Case1aMData
import Submission.Work.CORE3.Case1aBleM
import Submission.Work.CORE3.Case1aBFitting
import Submission.Work.CORE3.Case1aBFpf
import Submission.Work.CORE3.Case1aBothInvert
import Submission.Work.CORE3.Case1aDirectV13
import Submission.Work.CORE3.Case1aThmCInputsDir
import Submission.Work.CORE3.Case1aFalse
import Submission.Work.CORE3.Case1bSetup
import Submission.Work.CORE3.Case1bSOrder
import Submission.Work.CORE3.Case1bCount
import Submission.Work.CORE3.Case1bFive
import Submission.Work.CORE3.Case1bThree
import Submission.Work.CORE3.Case1bOne
import Submission.Work.CORE3.Case1bArith
import Submission.Work.CORE3.Case1bDiv
import Submission.Work.CORE3.Case1bNumerics
import Submission.Work.CORE3.Case1bIndex
import Submission.Work.CORE3.Case1bFalse

/-!
# CORE3 assembly: `Case1FalseProp`

Bender 1981 §3, pp. 222–224.  `Thm26Prop` splits `Case1 B` into the two subcases of §3, and
each is eliminated by the corresponding chain of leaves of this area:

* `O₂(Ĥ) ≤ S₀` and `Ĥ = H` (`Case1aFalseProp`), through
  `Case1aSetup → Case1aFrattini → Case1aAbelian → Case1aA7 → Case1aMData → Case1aBleM →
  Case1aBFitting → Case1aBFpf → Case1aBothInvert → Case1aThmCInputs → Case1aFalse`;
* `O₂(Ĥ)` of type (2,2) (`Case1bFalseProp`), through
  `Case1bSetup → Case1bSOrder → Case1bCount → Case1bFive → Case1bEightNine → Case1bThree →
  Case1bOne → Case1bArith → Case1bDiv → Case1bNumerics → Case1bIndex → Case1bFalse`.

`case1False_of_leaves` is the pure-logic composition (only `Thm26Prop` and the two subcase
eliminations).  `case1False_of_leaves'` folds in every leaf that is proved without `sorryAx` and
keeps the Props of the *still-open* inputs as hypotheses, so that the remaining surface is
explicit:

* `Case1aA7Prop` — the `M`-step of the subcase `Ĥ = H` (a leaf of the design, in flight as the
  `A7V18/*` sub-tree);
* `Case1bEightNineProp` (Bender's (6)–(9)) and `Case1bDivProp` (`12 ∣ b₄`), both blocked on
  Bender's (7), `|U| = 3`, in the in-flight `J4/` sub-tree.

Everything else is proved: in particular `Case1aMDataProp` (the §3a `M`-analysis, through
`MData.LayerSurjA7` and `Core18BcLeM`) is now a theorem, `Work.CORE3.Case1aMData`, and
`Case1bThreeProp`, `Case1bOneProp`, `Case1bNumericsProp`, `Case1bIndexProp`, `Case1bFalseProp`
are used directly.
-/

namespace Work.CORE3

open Work.GW2

/-- The two subcase eliminations compose to `Case1FalseProp` via Bender's Theorem 2.6. -/
theorem case1False_of_leaves (h26 : Thm26Prop) (ha : Case1aFalseProp) (hb : Case1bFalseProp) :
    Case1FalseProp := by
  intro G hG hFin hFT hBc B h1
  obtain ⟨-, -, hdisj⟩ := h26 G hFT hBc B
  rcases hdisj with ⟨-, hH⟩ | ⟨hfour, -, -⟩
  · exact ha G hFT hBc B h1 hH
  · exact hb G hFT hBc B h1 hfour

/-- **The area's composition, hypothesis-free.**  `Case1FalseProp` from the six named inputs
alone: every leaf of the design is now a theorem of the area.

* `Case1aA7Prop` — `Work.CORE3.Case1aA7` (the `A7V18/*` sub-tree);
* `Case1aMDataProp` — `Work.CORE3.Case1aMData` (via `MData.LayerSurjA7`);
* `Case1bDivProp` — `Work.CORE3.Case1bDiv` (via Bender's step (7) first half
  `Work.CORE3.BenderSevenU3` and the fixed-point-free action `Work.CORE3.Case1bStabTrivial`);
* `Case1bEightNineProp` — `Work.CORE3.Case1bEightNine`, whose `n ≠ 6` input comes from the
  `sorry`-free `Work.CORE3.J4.cosetInvCountNeSixClean`. -/
theorem case1False_of_leaves' (T : LocalToolkit) (h22 : Lemma22Prop) (h26 : Thm26Prop)
    (h29 : Lemma29Prop) (hC : BGThmCProp) (hA7 : Work.A7REC.A7Rec2Prop) :
    Case1FalseProp := by
  let I : Case1Inputs := ⟨T, h22, h26, h29, hC, hA7⟩
  -- subcase `Ĥ = H`
  have hSetup := Case1aSetup I
  have hFrattini := Case1aFrattini I
  have hAb := Case1aAbelian I
  have hA7prop := Case1aA7 I hFrattini hAb
  have hMD := Case1aMData I hSetup hFrattini hAb hA7prop
  have hBleM := Case1aBleM I hSetup hFrattini hAb hA7prop hMD
  have hBFit := Case1aBFitting I hSetup hFrattini hAb hA7prop hMD
  have hBpf := Case1aBFpf I hSetup hFrattini hAb hA7prop hBleM hBFit hMD
  have hInv := Case1aBothInvert I hSetup hFrattini hAb hA7prop hBpf
  have hDir := Case1aDirectV13 I hFrattini hAb hA7prop hMD hInv
  have hThmC := Case1aThmCInputsDir I hFrattini hAb hA7prop hInv hBpf hMD hDir
  have ha := Case1aFalse I hSetup hFrattini hAb hA7prop hInv hThmC
  -- subcase `V = O₂(Ĥ)`
  have hSetupb := Case1bSetup I
  have hCount := Case1bCount I
  have hFive := Case1bFive I
  have h89 := Case1bEightNine I hCount
  have hThree := Case1bThree I hSetupb hCount hFive h89
  have hOne := Case1bOne I hSetupb hCount h89
  have hDiv := Case1bDiv I hSetupb hCount hFive h89
  have hNum := Case1bNumerics I hSetupb hCount h89 hThree hOne hDiv
  have hIndex := Case1bIndex I hCount h89 hNum
  have hb := Case1bFalse I hSetupb hCount hFive h89 hIndex
  exact case1False_of_leaves h26 ha hb

end Work.CORE3
