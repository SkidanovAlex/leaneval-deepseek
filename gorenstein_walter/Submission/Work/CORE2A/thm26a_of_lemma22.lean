import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.lemma24
import Submission.Work.CORE2A.thm26a_U_eq_Ohat
import Submission.Work.CORE2A.thm26a_CS_eq_O2
import Submission.Work.CORE2A.thm26a_dichotomy

namespace Work.CORE2A

set_option linter.unusedVariables false

/-- Bender 1981, Theorem 2.6, first paragraph (`O₂(Ĥ) ≠ 1`): with all the earlier leaves of §2
supplied, the whole conclusion `Thm26Concl` follows.

The proof is the paper's opening paragraph, decomposed into its three conjuncts:
* `thm26a_U_eq_Ohat` — `U = O(Ĥ)` ("U centralizes O₂(Ĥ) and hence equals O(Ĥ)");
* `thm26a_CS_eq_O2`  — `C_S(U) = O₂(Ĥ)`;
* `thm26a_dichotomy` — the final dichotomy (`O₂(Ĥ) ≤ S₀, Ĥ = H` or `O₂(Ĥ) = (2,2)`,
  `Ĥ/O₂(Ĥ)U ≅ D₃`). -/
theorem thm26a_of_lemma22 (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (h22 : Work.GW2.Lemma22Prop) (h23 : Work.GW2.Lemma23Prop) (h24 : Work.GW2.Lemma24Prop) (h25 : Work.GW2.Lemma25Prop) : Work.GW2.Thm26aProp := by
  intro G _ _ hFT hctx B hO2
  exact ⟨thm26a_U_eq_Ohat T h21 h22 G hFT hctx B hO2,
    thm26a_CS_eq_O2 T h21 h22 G hFT hctx B hO2,
    thm26a_dichotomy T h21 h22 G hFT hctx B hO2⟩

end Work.CORE2A
