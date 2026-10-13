/-
  annals_wilkies_conjecture, AREA E3 (`Submission.Work.WilE3`): `E3_identity`.

  The frozen hole `WilkiesDesign.E.E3_identity` (Gabrielov–Vorobjov survey Cor. 4.7 / Gabrielov,
  Selecta Math. 1 (1995)) follows from the corrected separable-chain Khovanskii bound
  `Work.WilE3.SepKhovanskiiET`.  That bound is the lead's `Work.WilE3K.SepKhovanskiiET`
  (`sources/wilkiesE3E9/wilkies_E3E9_gaps.md`, GAP 1), whose proof from the frozen `E2_khovanskii`
  lives in the subproject `WilE3K`; E3's own file carries it as a hypothesis, and the lead wires
  `WilE3K` in the final `Wire`.
-/
import Submission.Work.WilE3.Identity.E3_identity_proved_of_multiplicity
import Submission.Work.WilE3.Realify.MultiplicityBound_of_ET

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

namespace Work.WilE3

/-- **`E3_identity`** (GV Cor. 4.7), in the exact form of the frozen
`WilkiesDesign.E.E3_identity`, from the corrected separable-chain Khovanskii bound.

The two ingredients are `Work.WilE3.Realify.MultiplicityBound_of_ET` (the realification of the
complexified system plus `SepKhovanskiiET`) and
`Work.WilE3.Identity.E3_identity_proved_of_multiplicity` (the frame step: the ordered reduced
derivatives are the tangential derivatives of `f` along `{h = 0}`, and the order is bounded by the
number of nondegenerate zeros of the perturbed system `(h, L, f - ε)`, which
`Work.WilE3.Lib.exists_card_solutions_eq_analyticOrderAt` counts). -/
theorem E3_identity_proved (hK : ∀ F : ℕ, SepKhovanskiiET F) :
    ∀ F : ℕ, ∃ M : Polynomial ℕ, ∀ (k r j : ℕ) (c : EAChain k r)
    (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (f : EAPoly k r) (x : Fin k → ℝ),
    k + r ≤ F → (∀ a, eaEval c (h a) x = 0) →
    (Matrix.of fun a b => eaEval c (eaD c (ι b) (h a)) x).det ≠ 0 →
    (∀ m : Fin k → ℕ, (∀ a, m (ι a) = 0) →
      ∑ l, m l ≤ M.eval (∑ a, atomDeg (h a) + atomDeg f) → eaEval c (opMono c h ι m f) x = 0) →
    ∀ᶠ y in 𝓝 x, (∀ a, eaEval c (h a) y = 0) → eaEval c f y = 0 :=
  Identity.E3_identity_proved_of_multiplicity (Realify.MultiplicityBound_of_ET hK)

end Work.WilE3
