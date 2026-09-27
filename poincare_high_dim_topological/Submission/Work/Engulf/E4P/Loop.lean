import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.DefsM
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.E4alt.tameOfNormData
import Submission.Work.Engulf.Auxi.TameTransfer
import Submission.Work.Engulf.Chain.E1gAux
import Submission.Work.Engulf.E4P.Defs
import Submission.Work.Engulf.E4P.Basic
import Submission.Work.Engulf.E4P.Core

/-!
# `Work.Engulf.E4P.Loop` — the piece loop of `E4c`

* `baseSt` : the state of `PieceSt` at `r = 0` (no piece attached yet: `Γc = Γ₁`, `P = ∅`,
  `gc = g`, `hc = h`).  Its smoothing-chart field is `smoothChart_core`;
* `loopOfStep` : from the state at `0` and an abstract one-step function (the concrete one is
  `Work.Engulf.E4P.step`, see `Submission/Work/Engulf/E4P/Step.lean`), the state after all
  `pieces.length` pieces.

The concrete loop is proved by `Nat.rec` exactly as in `Submission/Work/Engulf/E1B/group.lean`.
-/

open Set Metric PL

namespace Work.Engulf.E4P

universe u

/-- The initial state of the piece loop. -/
theorem baseSt {n p q N : ℕ} {M : Type u} [MetricSpace M] {V X : Set M} {Γ : Cx N}
    {K L : Set (E N)} {f : E N → M} {τ₀ τ₁ : Finset (E N)} {ψ : CubeChart n M} {ε β : ℝ}
    (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : L7Hyp n p q V X Γ K L f τ₀ τ₁) (SCh : SmoothChart p X Γ L f ψ)
    (hLsub : IsSubSp Γ L) {G : Set (E N)} {g : E N → M}
    (hgc : ContinuousOn g ND.Γ₁.space)
    (hgfrz : EqOn g ND.g₁ (L ∪ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ))
    {h : M ≃ₜ M} (hsupp : CSupp h univ) (heng : X ∪ g '' G ⊆ h '' V)
    {pieces : List (Finset (E n))} :
    PieceSt n p V X ND.Γ₁ G L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ψ g pieces β
      0 ND.Γ₁ ∅ g h := by
  have hchart : SmoothChart p X ND.Γ₁ (L ∪ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) g ψ :=
    Work.Engulf.SmoothChart.congr hgfrz (smoothChart_core ND hLsub SCh)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hgc, ?_, ?_, ?_, ?_, ?_, ?_, hsupp⟩
  · exact Nat.zero_le _
  · exact Subset.rfl
  · exact ND.hΓ₁
  · exact dimLE_of_subdivides ND.sub H7.cfg.dimΓ
  · intro s hs
    exact Or.inl hs
  · exact isSubSp_empty ND.Γ₁
  · exact (by simp : Disjoint (∅ : Set (E N)) ND.Γ₁.space)
  · intro s _ hsP
    have hsempty : simp s = ∅ := Set.Subset.antisymm hsP (Set.empty_subset _)
    have hse : s = ∅ := Work.Engulf.simp_eq_empty_iff.mp hsempty
    simp [hse]
  · intro x _
    rfl
  · rw [Set.union_empty]
    exact hchart
  · rintro z ⟨x, hx, -⟩
    exact absurd hx (Set.notMem_empty x)
  · intro j hj
    exact absurd hj (Nat.not_lt_zero j)
  · intro x _
    simp
  · rintro z (hz | ⟨x, hx, rfl⟩)
    · exact heng (Or.inl hz)
    · exact heng (Or.inr ⟨x, by simpa using hx, rfl⟩)

/-- The loop: iterate the one-step function over the list of pieces.  `hstep` is instantiated by
`Work.Engulf.E4P.step`. -/
theorem loopOfStep {n p q N : ℕ} {M : Type u} [MetricSpace M] {V X : Set M} {Γ : Cx N}
    {K L : Set (E N)} {f : E N → M} {τ₀ τ₁ : Finset (E N)} {ψ : CubeChart n M} {ε β : ℝ}
    (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    {G : Set (E N)} {g : E N → M} {pieces : List (Finset (E n))} {h : M ≃ₜ M}
    (hstep : ∀ {r : ℕ} {Γc : Cx N} {P : Set (E N)} {gc : E N → M} {hc : M ≃ₜ M},
      r < pieces.length →
      PieceSt n p V X ND.Γ₁ G L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ψ g pieces β r Γc P gc hc →
      ∃ (Γc' : Cx N) (P' : Set (E N)) (gc' : E N → M) (hc' : M ≃ₜ M),
        PieceSt n p V X ND.Γ₁ G L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ψ g pieces β
          (r + 1) Γc' P' gc' hc')
    (h0 : PieceSt n p V X ND.Γ₁ G L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ψ g pieces β
      0 ND.Γ₁ ∅ g h) :
    ∃ (Γc : Cx N) (P : Set (E N)) (gc : E N → M) (hc : M ≃ₜ M),
      PieceSt n p V X ND.Γ₁ G L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ψ g pieces β
        pieces.length Γc P gc hc := by
  have hiter : ∀ r ≤ pieces.length,
      ∃ (Γc : Cx N) (P : Set (E N)) (gc : E N → M) (hc : M ≃ₜ M),
        PieceSt n p V X ND.Γ₁ G L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ψ g pieces β r Γc P gc hc := by
    intro r
    induction r with
    | zero => intro _; exact ⟨ND.Γ₁, ∅, g, h, h0⟩
    | succ r ih =>
        intro hr
        obtain ⟨Γc, P, gc, hc, S⟩ := ih (by omega)
        exact hstep (by omega) S
  exact hiter pieces.length le_rfl

end Work.Engulf.E4P
