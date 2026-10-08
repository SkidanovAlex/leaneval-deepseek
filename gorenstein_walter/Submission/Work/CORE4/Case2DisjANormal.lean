/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — Bender §4 (8): `A ⊴ F(U)`

Bender 1981, §4 (8), p. 226 (the last conjunct of `Case2EightFacts`):

> `|U : B₀ K F(U)| ≤ p`, and *unless `I_U(s) ⊴ Ĥ`*, `u ≤ p` and `A ⊴ F(U)`,

for the odd prime `p` with `P ≤ F` of order `p` and `A` the unique subgroup of type `(p,p)` of
`F × K₁` containing `P` (here `Case2EightObj h.D p P A`).

The present file proves the `A ⊴ F(U)` clause at the `Case2Ctx` level, i.e. exactly the requested

    Work.CORE4.Case2DisjANormal.

## Route

Everything except one object-layer input is elementary:

* `A ≤ F(U)` — `EightAeqOmega` gives `A = Ω₁(F ⊔ K₀)`, and `F ⊔ K₀ ≤ F(U)` because
  `F = B₀ ⊓ F(U)` and `K₀ = F(U) ⊓ K` (`EightAeqOmega`, proved in
  `Submission.Work.CORE4.EightAeqOmega`);
* `A` is a `p`-group — `|A| = p²` (`Case2EightObj`);
* `A ≤ O_p(U)` — `A ≤ F(U)` and `A` a `p`-group, so for `x ∈ A` the cyclic subgroup `⟨x⟩` is a
  `p`-subgroup of the Fitting subgroup `F(U)`; by
  `Work.CORE4.EightANF_pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn`
  (`Submission.Work.CORE4.EightAnormalFitting_of_pcore`) such an `x` lies in `O_p(U)`;
* `A ⊴ O_p(U)` — Bender's §4 (8) case analysis (cases 1–2 of the trichotomy on
  `Q = Ω₁(Z₂(O_p(U)))`; case 3 is the exceptional clause `I_U(s) ⊴ Ĥ`, excluded by the
  hypothesis `¬ Case2InvNormal B h.D`).  This is the object-layer input, isolated as
  `Work.CORE4.APcoreCtx` (`Submission.Work.CORE4.APcoreCtx`);
* `A ⊴ O_p(U)` together with `A ≤ O_p(U)` gives `A ⊴ F(U)` — the nilpotency step: `O_p(U)` is the
  Sylow `p`-subgroup of the nilpotent `F(U)`, and the `p'`-part of `F(U)` centralizes it
  (`Work.CORE4.EightAnormalFitting_of_pcore`, proved).
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.Case2SixEmbed
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.EightAnormalFitting_of_pcore
import Submission.Work.CORE4.APcoreCtx
import Submission.Work.CORE4.Case2EightDisjOfCtx

namespace Work.CORE4

open Work.GW2 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The three elementary conjuncts of the object layer -/

/-- `Ω₁(X) ≤ X`, in the vocabulary of `EightIdxDefs`. -/
theorem omega1_le_self_c4 (p : ℕ) (X : Subgroup G) : omega1 p X ≤ X := by
  rw [omega1]
  exact (Subgroup.closure_le X).mpr fun _ hx => hx.1


/-- **`A` is a `p`-group** (`|A| = p ^ 2`). -/
theorem A_isPGroup_c4 (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hObj : Work.GW2.Case2EightObj h.D p P A) :
    IsPGroup p ↥A :=
  IsPGroup.of_card (n := 2) hObj.2.2.2.2.1

/-- **`A ≤ O_p(U)`.**  `A ≤ F(U)` and `A` is a `p`-group, so every `x ∈ A` generates a
`p`-subgroup of the Fitting subgroup `F(U)`; a `p`-element of `F(U)` lies in `O_p(U)`
(`EightANF_pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn`). -/
theorem A_le_pCoreIn_c4 (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A) :
    A ≤ Work.GW2.pCoreIn p B.U := by
  intro x hx
  exact EightANF_pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn B.U p hp
    (A_le_fittingIn_c4 I hbc B h p P A hp hPF hPcard hObj hx)
    ((A_isPGroup_c4 B h p P A hObj).to_le (Subgroup.zpowers_le.mpr hx))

/-! ## The target -/

theorem Case2DisjANormal (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj h.D p P A →
          (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal := by
  intro G _ _ hbc B h hInv p P A hp hPF hPcard hObj
  exact EightAnormalFitting_of_pcore p hp A
    (A_le_fittingIn_c4 I hbc B h p P A hp hPF hPcard hObj)
    (A_isPGroup_c4 B h p P A hObj)
    (A_le_pCoreIn_c4 I hbc B h p P A hp hPF hPcard hObj)
    (APcoreCtx I G hbc B h hInv p P A hp hPF hPcard hObj)

end Work.CORE4
