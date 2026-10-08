import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2SixThreeRaw
import Submission.Work.CORE4.Case2SixEmbed
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.EightAnormalPcore_of_Qpos
import Submission.Work.CORE4.EightAnormalFitting_of_pcore

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## Bender §4 (8), the clause "`A ⊴ F(U)`"

`EightANormalFitting` is the `A ⊴ F(U)` half of Bender's display (8), p. 226:

> `|U : B₀ K F(U)| ≤ p` and, **unless `I_U(s) ⊴ Ĥ`**, `u ≤ p` and `A ⊴ F(U)`,

for the odd prime `p` with `P ≤ F` of order `p` and `A` the unique `(p,p)`-subgroup `A ≤ F ⊔ K` of
exponent `p` containing `P` (`Case2EightObj`).

Bender's proof of (8) puts `Q := Ω₁(Z₂(O_p(U)))` and distinguishes three cases:

1. `A = Q`;
2. `Z(Q) < A < Q` with `|Q : A| = p`;
3. `s` inverts `Q` — the case whose conclusion is `I_U(s) ⊴ Ĥ`, i.e. `Case2InvNormal B D`, the
   hypothesis denied here.

In cases 1 and 2 `A ⊴ O_p(U)`, because `[Q, O_p(U)] ≤ Z(Q) ≤ A` (case 1: `A = Q ⊇ Z(Q)`;
case 2: `Z(Q) < A`); since `A ≤ O_p(U) ≤ F(U)` and the `p'`-part of the nilpotent `F(U)`
centralizes `O_p(U)`, this gives `A ⊴ F(U)`.  The steps of that chain are the companion leaves

* `Work.CORE4.EightANF_QsubPos` (Bender's trichotomy cases 1–2 at the `Case2Ctx` level):
  `A ≤ Ω₁(Z₂(O_p(U)))` and (`A = Q` or `Z(Q) < A`);
* `Work.CORE4.EightAnormalPcore_of_Qpos`, resp. the unconditional `Work.CORE4.EightAnormalPcore`:
  that position of `A` in `Q` gives `A ⊴ O_p(U)`;
* `Work.CORE4.EightAnormalFitting_of_pcore`: `A ≤ O_p(U)` and `A ⊴ O_p(U)` give `A ⊴ F(U)` (the
  Sylow/coprimality step, using no configuration input).

The present file assembles these with the object-level facts about `A` and `Q` that hold at the
`Case2Ctx` level: `A = Ω₁(F ⊔ K₀) ≤ F(U)` (hence `A` is a `p`-group and `A ≤ O_p(U)` follows from
`A ≤ Q`). -/

/-- `Ω₁(X) ≤ X`. -/
theorem omega1_le_self (p : ℕ) (X : Subgroup G) : omega1 p X ≤ X := by
  rw [omega1]
  exact (Subgroup.closure_le X).mpr fun _ hx => hx.1

/-- Bender's `Q = Ω₁(Z₂(O_p(U)))` lies in `O_p(U)` (the second centre of a subgroup is a
subgroup of it). -/
theorem Qsub_le_pCoreIn (p : ℕ) (B : Work.GW2.BenderSetup G) :
    Qsub p B ≤ Work.GW2.pCoreIn p B.U :=
  omega1_z2_le_self p _

/-- **The `(p,p)`-subgroup `A` of §4 (8) lies in `F(U)`** (Bender p. 225, "`A` is the subgroup of
type `(p,p)` in `F × K₁`" with `K₁ = F(U) ⊓ K`): `A = Ω₁(F ⊔ K₀) ≤ F ⊔ K₀ ≤ F(U)`. -/
theorem A_le_fittingIn (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card ↥P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A) :
    A ≤ Work.GW2.fittingIn B.U := by
  rw [(EightAeqOmega I G hbc B h p P A hp hPF hPcard hObj).2]
  exact le_trans (omega1_le_self p _)
    (sup_le (Work.GW2.Case2Data.F_le_fitting B h.D) inf_le_left)

/-- **`A` is a `p`-group** (`|A| = p ^ 2`). -/
theorem A_isPGroup (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card ↥P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A) :
    IsPGroup p ↥A := by
  obtain ⟨-, -, -, -, hAcard, -, -, -⟩ := hObj
  exact IsPGroup.of_card (n := 2) (by rw [hAcard])

/-- **`A ≤ O_p(U)`**: an element of `A ≤ F(U)` of `p`-power order lies in the `p`-core of `U`. -/
theorem A_le_pCoreIn (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
    (p : ℕ) (P A : Subgroup G) (hp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card ↥P = p)
    (hObj : Work.GW2.Case2EightObj h.D p P A) :
    A ≤ Work.GW2.pCoreIn p B.U := by
  have hAle : A ≤ Work.GW2.fittingIn B.U := A_le_fittingIn I hbc B h p P A hp hPF hPcard hObj
  have hAp : IsPGroup p ↥A := A_isPGroup I hbc B h p P A hp hPF hPcard hObj
  intro x hx
  exact EightANF_pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn (K := B.U) p hp (hAle hx)
    (hAp.to_le (Subgroup.zpowers_le.mpr hx))

/-- **THE GAP.** Bender's trichotomy (p. 226) at the level of the present `Case2Ctx`: either
`A = Ω₁(Z₂(O_p(U)))` itself, or `Z(Q) < A < Q` with `|Q : A| = p`.  This is the object-layer
input of §4 (8) that is **not derivable** from the recorded hypotheses (see the file header and
`Submission/Work/CORE4/EightExCase3.lean`, `Case2EightExcept.lean`): it needs Bender's
`|Q| ≤ p³` (`Q` elementary abelian of order `p²` or extraspecial of order `p³`) and the exclusion
of the third branch `s` inverts `Q`, which Bender derives from `I_U(s) ⊴ Ĥ` via
`C_U(Q) ⊓ C_U(s) = ⊥`. -/
theorem EightANormalFitting_gap (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
          Work.GW2.Case2EightObj h.D p P A →
          A ≤ Qsub p B ∧ (A = Qsub p B ∨ centerIn (Qsub p B) < A) := by
  sorry

/-- Bender §4 (8) (p. 226), the clause `A ⊴ F(U)`.

The proof is Bender's case analysis on `Q := Ω₁(Z₂(O_p(U)))`: with the exceptional case
`I_U(s) ⊴ Ĥ` excluded, `A = Q` or `Z(Q) < A < Q`, giving `A ⊴ O_p(U)`, and the `p'`-part of the
nilpotent `F(U)` centralizes `A`, giving `A ⊴ F(U)`.

The two steps of the case analysis are proved in the companion modules
`Work.CORE4.EightAnormalPcore_of_Qpos` (the position of `A` in `Q` gives `A ⊴ O_p(U)`) and
`Work.CORE4.EightAnormalFitting_of_pcore` (`A ⊴ O_p(U)` and `A ≤ O_p(U)` give `A ⊴ F(U)`); what
the recorded hypotheses do not carry is the position of `A` in `Q` itself, `EightANormalFitting_gap`
above. -/
theorem EightANormalFitting (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ¬ Work.GW2.Case2InvNormal B h.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
          Work.GW2.Case2EightObj h.D p P A →
          (A.subgroupOf (Work.GW2.fittingIn B.U)).Normal := by
  intro G _ _ hbc B h hInv p P A hp hPF hPcard hObj
  obtain ⟨hAQ, hpos⟩ := EightANormalFitting_gap I G hbc B h hInv p P A hp hPF hPcard hObj
  have hAle : A ≤ Work.GW2.fittingIn B.U := A_le_fittingIn I hbc B h p P A hp hPF hPcard hObj
  have hAp : IsPGroup p ↥A := A_isPGroup I hbc B h p P A hp hPF hPcard hObj
  have hAleOp : A ≤ Work.GW2.pCoreIn p B.U := le_trans hAQ (Qsub_le_pCoreIn p B)
  exact EightAnormalFitting_of_pcore (B := B) p hp A hAle hAp hAleOp
    (EightAnormalPcore_of_Qpos (B := B) p hp A hAQ hpos)

end Work.CORE4
