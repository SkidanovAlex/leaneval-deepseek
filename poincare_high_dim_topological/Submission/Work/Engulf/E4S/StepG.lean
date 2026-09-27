import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.DefsM
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.E4S.Step
import Submission.Work.Engulf.E4P.PiecesEngulfG

/-!
# `Work.Engulf.E4S.StepG` — `stepG`, the moving-map step, unconditional

`Work.Engulf.E4S.stepG` is `Work.Engulf.E4S.stepG_of_pieces` applied to the piece loop `E4c`
`Work.Engulf.E4P.piecesEngulfG` (the canonical proof of the piece loop, area E4P).  It is the statement of
`Submission/Work/lead_engulf/E4cIface.lean.txt` §A.5 with the §B universe facade applied
(`{M : Type*}`, `Work.Engulf.ToolsAllM M n`, `Work.Engulf.BM M n p q`).
-/

open Set Metric PL
open Work.Engulf.Alt

namespace Work.Engulf.E4S

/-- **`E4e` with a moving map** (`NOTES_LEAD_poincare_E4c.md` §A.5): one step of the shelling loop
of `AltInnerG`.  This is Newman's Lemma 7 Case 1 step with the map allowed to move off
`L ∪ coreSet` — the repair forced by the failure of the fixed-map invariant, see
`Submission/Work/Engulf/E4alt/NOTE_superseded.md`. -/
theorem stepG {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (T : Work.Engulf.ToolsAllM M n) (hB : Work.Engulf.BM M n p q)
    (hq : q + 1 ≤ p + 1) (A : Work.Engulf.Amb n p M V)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (SCh : Work.Engulf.SmoothChart p X Γ L f ψ)
    (hch : f '' PL.simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' PL.openCube (1 / 2 : ℝ)) (hε : 0 < ε)
    (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (hc11 : Work.Engulf.Alt.Core11 ND) (hcS : Work.Engulf.Alt.CarrierS ND)
    {μ : ℝ} (hmarg : ∀ x ∈ ND.Γ₁.space, x ∉ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ →
      ∀ z : M, dist z (ND.g₁ x) < μ → z ∉ ψ.toFun '' PL.closedCube (9 / 16 : ℝ))
    {β : ℝ} (hβ : 0 < β) (hβμ : (ND.ord.length : ℝ) * β < μ)
    {i : ℕ} (hi : i < ND.ord.length) {g : PL.E N → M} {h : M ≃ₜ M}
    (inv : Work.Engulf.Alt.AltInnerG V X K L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ND.Γ₁ ND.g₁
      ND.ord β i g h) :
    ∃ (g' : PL.E N → M) (h' : M ≃ₜ M),
      Work.Engulf.Alt.AltInnerG V X K L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ND.Γ₁ ND.g₁
        ND.ord β (i + 1) g' h' :=
  stepG_of_pieces T hB hq A H7 SCh hch hε ND hc11 hcS hmarg hβ hβμ hi inv
    (fun {G} hGsub hGdim {g} hgc hgfrz {h} hsupp heng {Φ} {F} {γ₀ γ₁}
        hFc hFconv hγ₀c hγ₁c hle {J} hJF hJd hJc hsmall {β₀} hβ₀ =>
      Work.Engulf.E4P.piecesEngulfG (β := β₀) T hB ND hc11 H7 A SCh hq hGsub hGdim hgc hgfrz
        hsupp heng hFc hFconv hγ₀c hγ₁c hle hJF hJd hJc hsmall hβ₀)

end Work.Engulf.E4S
