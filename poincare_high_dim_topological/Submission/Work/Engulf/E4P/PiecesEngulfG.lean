import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.DefsM
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3
import Submission.Work.Engulf.E4P.Defs
import Submission.Work.Engulf.E4P.Basic
import Submission.Work.Engulf.E4P.Core
import Submission.Work.Engulf.E4P.Loop
import Submission.Work.Engulf.E4P.Step
import Submission.Work.Engulf.E4P.exists_pieces_list

open Set Metric PL

namespace Work.Engulf.E4P

universe u

/-!
# `Work.Engulf.E4P.PiecesEngulfG` — Newman `E4c` (`NOTES_LEAD_poincare_E4c.md` §A.3)

The theorem of the area: the `E4c` step in the corrected (moving map) form of
`Submission/Work/lead_engulf/E4cIface.lean.txt`.  Its proof is
`exists_pieces_list` (the pieces covering the region over `J`) + `baseSt` + the loop
`loopOfStep` with `Work.Engulf.E4P.step`.
-/

theorem piecesEngulfG {n p q N : ℕ} {M : Type u} [MetricSpace M] {V X : Set M} {Γ : Cx N}
    {K L : Set (E N)} {f : E N → M} {τ₀ τ₁ : Finset (E N)} {ψ : CubeChart n M} {ε β : ℝ}
    (T : Work.Engulf.ToolsAllM M n) (hB : Work.Engulf.BM M n p q)
    (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (hc11 : Work.Engulf.Alt.Core11 ND) (H7 : L7Hyp n p q V X Γ K L f τ₀ τ₁)
    (A : Amb n p M V) (SCh : SmoothChart p X Γ L f ψ) (hq : q + 1 ≤ p + 1)
    {G : Set (E N)} (hGsub : IsSubSp ND.Γ₁ G)
    (hGdim : ∀ s ∈ ND.Γ₁.faces, simp s ⊆ G → s.card ≤ p + 1)
    {g : E N → M} (hgc : ContinuousOn g ND.Γ₁.space)
    (hgfrz : EqOn g ND.g₁ (L ∪ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ))
    {h : M ≃ₜ M} (hsupp : CSupp h univ) (heng : X ∪ g '' G ⊆ h '' V)
    {Φ : E n ≃ᵃ[ℝ] Work.Engulf.Pr (n - q - 1) q} {F : Set (E q)} {γ₀ γ₁ : E q → ℝ}
    (hFc : IsCompact F) (hFconv : Convex ℝ F) (hγ₀c : Continuous γ₀) (hγ₁c : Continuous γ₁)
    (hle : ∀ z ∈ F, γ₀ z ≤ γ₁ z)
    {J : Set (E q)} (hJF : J ⊆ F) (hJd : DomDim J ((q : ℤ) - 2)) (hJc : IsClosed J)
    (hsmall : ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
      Φ.symm ((0 : E (n - q - 1)), z, t) ∈ openCube (n := n) (9 / 16 : ℝ))
    {β : ℝ} (hβ : 0 < β) :
    ∃ (g' : E N → M) (h' : M ≃ₜ M), ContinuousOn g' ND.Γ₁.space ∧
      EqOn g' g (L ∪ Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ∧
      (∀ x ∈ ND.Γ₁.space, dist (g' x) (g x) < β) ∧
      CSupp h' univ ∧ X ∪ g' '' G ⊆ h' '' V ∧
      ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
        ψ.toFun (Φ.symm ((0 : E (n - q - 1)), z, t)) ∈ h' '' V := by
  classical
  have hLsub : IsSubSp Γ L := H7.cfg.subL
  have hLsub₁ : IsSubSp ND.Γ₁ L := ND.subsp L hLsub
  have hn : q + 1 ≤ n := q_add_one_le_of_affineEquiv Φ
  obtain ⟨pieces, hpieces, hcover⟩ :=
    exists_pieces_list hn Φ hFc hFconv hγ₀c hγ₁c hle hJF hJd hJc hsmall
  have h0 : PieceSt n p V X ND.Γ₁ G L (Work.Engulf.Alt.coreSet ND.Γ₁ f ψ) ψ g pieces β
      0 ND.Γ₁ ∅ g h := baseSt ND H7 SCh hLsub hgc hgfrz hsupp heng
  obtain ⟨Γc, P, gc, hc, SF⟩ :=
    loopOfStep (β := β) ND
      (fun {r Γc P gc hc} hr S =>
        step T hB ND hc11 H7 A hq hLsub₁ hGsub hGdim hgfrz hβ hpieces hr S) h0
  refine ⟨gc, hc, SF.cont.mono (Work.Engulf.Chain.space_mono SF.sub), SF.frz, ?_, SF.supp, ?_, ?_⟩
  · intro x hx
    have h1 := SF.near x hx
    have h2 : (pieces.length : ℝ) * β / ((pieces.length : ℝ) + 1) < β := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (pieces.length : ℝ) + 1)]
      nlinarith [hβ, Nat.cast_nonneg (α := ℝ) pieces.length]
    linarith
  · rintro z (hz | ⟨x, hx, rfl⟩)
    · exact SF.eng (Or.inl hz)
    · exact SF.eng (Or.inr ⟨x, Or.inl hx, rfl⟩)
  · intro z hz t ht
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp (hcover z hz t ht)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs
    have hjL : j < pieces.length := by omega
    have hgaff := SF.gaff j (by omega) hjL
    have hmem : ψ.toFun (Φ.symm ((0 : E (n - q - 1)), z, t)) ∈ gc '' P :=
      hgaff ⟨Φ.symm ((0 : E (n - q - 1)), z, t), hxs, rfl⟩
    obtain ⟨y, hy, hyeq⟩ := hmem
    rw [← hyeq]
    exact SF.eng (Or.inr ⟨y, Or.inr hy, rfl⟩)

end Work.Engulf.E4P
