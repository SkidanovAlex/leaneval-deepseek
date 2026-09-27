import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic

/-!
# The E1 (Newman Lemma 5) invariants of the repaired proof

`E1Inv` of the design pass is replaced by two invariants, following
`Submission/Work/NOTES_LEAD_poincare_E1fix.md` §1: an *outer* invariant `E1GInv` running over the
finitely many smoothing charts covering `X ∖ V` (each group avoids the *current* frozen image),
and an *inner* invariant `E1PInv` running over the finitely many pieces of one chart group.
The statements are those of `Submission/Work/lead_engulf/E1fix.lean.txt` (typechecked by the lead),
moved into namespace `Work.Engulf`.
-/

open Set Metric PL

namespace Work.Engulf

universe u

variable {n : ℕ} {M : Type*} [MetricSpace M] {N : ℕ}

/-- Outer E1 invariant (replaces `E1Inv`): `k` chart groups done. -/
structure E1GInv (n p : ℕ) (V X : Set M) (Γ : Cx N) (H L : Set (E N)) (f : E N → M)
    (ψs : List (CubeChart n M)) (ε : ℝ) (k : ℕ)
    (Γk : Cx N) (F : Set (E N)) (Xk : Set M) (g : E N → M) (h : M ≃ₜ M) : Prop where
  le    : k ≤ ψs.length
  sub   : Γ.faces ⊆ Γk.faces
  fin   : Γk.faces.Finite
  dim   : DimLE Γk (p + 1)
  newF  : ∀ s ∈ Γk.faces, s ∈ Γ.faces ∨ simp s ⊆ F
  subF  : IsSubSp Γk F
  disjF : Disjoint F Γ.space
  dimF  : ∀ s ∈ Γk.faces, simp s ⊆ F → s.card ≤ p + 1
  cont  : ContinuousOn g Γk.space
  frz   : EqOn g f L
  near  : ∀ x ∈ Γ.space, dist (g x) (f x) < ε * (1 - (1 / 2 : ℝ) ^ (k + 1))
  tame  : Tame n p X Γk (L ∪ F) g
  supp  : CSupp h univ
  Xkc   : IsClosed Xk
  XkX   : Xk ⊆ X
  eng   : Xk ∪ g '' (H ∪ F) ⊆ h '' V
  cover : X ⊆ Xk ∪ g '' F ∪ ⋃ i ∈ Finset.Ico k ψs.length, ⋃ (hi : i < ψs.length),
            ψs[i].toFun '' closedCube (1 / 2 : ℝ)

/-- Inner E1 invariant, inside chart group `ψ` (state at group start: `Γ₀, F, g₀`;
`X₁` = the enlarged kept set of this group). -/
structure E1PInv (n p : ℕ) (V X : Set M) (H L : Set (E N)) (ψ : CubeChart n M)
    (Γ₀ : Cx N) (F : Set (E N)) (X₁ : Set M) (g₀ : E N → M)
    (pieces : List (Finset (E n))) (η : ℝ) (r : ℕ)
    (Γr : Cx N) (G : Set (E N)) (g : E N → M) (h : M ≃ₜ M) : Prop where
  le    : r ≤ pieces.length
  sub   : Γ₀.faces ⊆ Γr.faces
  fin   : Γr.faces.Finite
  dim   : DimLE Γr (p + 1)
  newG  : ∀ s ∈ Γr.faces, s ∈ Γ₀.faces ∨ simp s ⊆ G
  subG  : IsSubSp Γr G
  disjG : Disjoint G Γ₀.space
  dimG  : ∀ s ∈ Γr.faces, simp s ⊆ G → s.card ≤ p + 1
  cont  : ContinuousOn g Γr.space
  frz   : EqOn g g₀ (L ∪ F)
  near  : ∀ x ∈ Γ₀.space, dist (g x) (g₀ x) < r * η
  tame  : Tame n p X Γr (L ∪ F ∪ G) g
  chart : SmoothChart p X Γr (L ∪ G) g ψ
  Gim   : g '' G = ⋃ j ∈ Finset.range r, ⋃ (hj : j < pieces.length), ψ.toFun '' simp pieces[j]
  supp  : CSupp h univ
  eng   : X₁ ∪ g '' (H ∪ F ∪ G) ⊆ h '' V

end Work.Engulf
