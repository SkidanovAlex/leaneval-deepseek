import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic

namespace Work.CORE3

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Bender 1981 §3, pp. 222–223, end of the subcase `Ĥ = H`.  Deliverable
`Work.GW2.Case1aFalseProp`.

From the earlier leaves: `Case1aSetupProp` gives `D : Case1aData B`; `Case1aFrattiniProp` gives
`N_G(P₁) ⊄ H` for `P₁ = P P₂` (`P₂ ∈ Syl_p(C_U(S))`); `Case1aAbelianProp` gives
`P ∩ P^g = ⊥` with `P P^g` abelian; `Case1aA7Prop` gives that a maximal `M ⊇ N_G(P₂)` satisfies
`E(M)/Z(E(M)) ≅ A₇`, `|S| = 8`, `|P₀| = 3`; `Case1aBothInvertProp` gives that both `t₁`, `t₂`
invert `F_{3'}(U)`; and `Case1aThmCInputsProp` assembles the inputs of Bender–Glauberman
Theorem C (`I.hC : BGThmCProp`) — a `BGData G` for `(S, S₀, t, t₁, t₂)`, the maximal inverted
subgroups `K₁ = I_U(t₁)`, `K₂ = I_U(t₂)`, the direct decomposition of `U`, the coprimality and
the Frobenius/non-abelian clauses.

Theorem C then gives `¬ IsSimpleGroup G`, contradicting `BenderCtx.simple`. -/
theorem Case1aFalse (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) (hInv : Case1aBothInvertProp)
    (hThmC : Case1aThmCInputsProp) : Case1aFalseProp := by
  intro G _ _ hFT hCtx B hCase1 hHhat
  obtain ⟨D⟩ := hSetup G hFT hCtx B hCase1 hHhat
  obtain ⟨BG, _ht, _ht1, _ht2, _hS, _hS0, K1, K2, hK1, hK2, hdir, hcop, hcomm, hfrob⟩ :=
    hThmC G hFT hCtx B hCase1 hHhat D
  exact (I.hC G BG K1 K2 hK1 hK2 hdir hcop hcomm hfrob) hCtx.simple

end Work.CORE3

open Work.GW2

/-- The same lemma, mirrored at the namespace of the file path, so that it can be cited both as
`Work.CORE3.Case1aFalse` (the name the area requests) and as
`Work.CORE3.Work.CORE3.Case1aFalse` (the skeleton's namespace layout). -/
theorem Case1aFalse (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) (hInv : Case1aBothInvertProp)
    (hThmC : Case1aThmCInputsProp) : Case1aFalseProp :=
  _root_.Work.CORE3.Work.CORE3.Case1aFalse I hSetup hFr hAb hA7 hInv hThmC

end Work.CORE3
