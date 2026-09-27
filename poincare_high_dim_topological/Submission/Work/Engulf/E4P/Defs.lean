import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.DefsM
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.E4alt.Defs3

/-!
# `Work.Engulf.E4P` — the piece loop of `piecesEngulfG` (E4c of `NOTES_LEAD_poincare_E4c.md` §A.3)

This area proves Newman's `E4c` step in the corrected ("moving map") form of
`Submission/Work/lead_engulf/E4cIface.lean.txt`:

    `Work.Engulf.E4P.piecesEngulfG` :

given the current map `g` (frozen to `g₁` on `L ∪ coreSet`), a subcomplex `G` with
`X ∪ g '' G ⊆ h '' V`, and the prism data of a shelled simplex together with a closed
`(q-2)`-dominated `J` whose region lies in the `9/16` cube, produce `g'`, `h'` with `g' = g` on
`L ∪ coreSet`, `dist (g', g) < β`, `X ∪ g' '' G ⊆ h' '' V`, and the region over `J` inside `h' '' V`.

The pieces (chart simplices of at most `q` vertices covering the region over `J`, each inside the
closed `11/16` cube) are attached one at a time as *far* faces of the current complex; each is then
engulfed by one call of `B n p q` in which the already engulfed part is carried inside the `H` of
the call (Newman (13.2)–(13.4): the map moves, only `L ∪ coreSet` is frozen).

## Contents of this file

* `PieceSt` — the state of the loop over the pieces (`r` pieces added so far).
* `PiecesOk`, `CoversRegion` — the interface predicates for the list of pieces.
-/

open Set Metric PL

namespace Work.Engulf.E4P

/-- The pieces produced for the region over `J`: non-empty affinely independent vertex sets with at
most `q` vertices, whose simplices lie in the closed `11/16` cube of the chart of `ψ`. -/
def PiecesOk {n q : ℕ} (pieces : List (Finset (E n))) : Prop :=
  ∀ s ∈ pieces, s.Nonempty ∧ AffineIndependent ℝ (fun v : ↥s => (v : E n)) ∧ s.card ≤ q ∧
    simp s ⊆ closedCube (n := n) (11 / 16 : ℝ)

/-- The list of pieces covers the region over `J` in the prism decomposition `T`. -/
def CoversRegion {n q : ℕ} (T : E n ≃ᵃ[ℝ] Pr (n - q - 1) q) (γ₀ γ₁ : E q → ℝ) (J : Set (E q))
    (pieces : List (Finset (E n))) : Prop :=
  ∀ z ∈ J, ∀ t ∈ Set.Icc (γ₀ z) (γ₁ z),
    T.symm ((0 : E (n - q - 1)), z, t) ∈ ⋃ s ∈ pieces, simp s

/-- State of the loop of `piecesEngulfG` after the first `r` pieces have been attached as far faces
and engulfed.  `Γ₁` is the fine complex of the normalisation `ND`, `G` the subcomplex already
engulfed before the loop (fixed), `L ∪ Cr` the frozen set (`Cr = coreSet Γ₁ f ψ`), `ψ` the chart of
the shelled simplex, `g₀` the map the loop starts from, `pieces` the pieces still to be attached and
`β` the total budget of the loop (one piece costs `β / (pieces.length + 1)`).

The current data is `Γc` (the complex, `Γ₁ ⊆ Γc`), `P` (the union of the far faces attached so far),
`gc` (the moving map) and `hc` (the accumulated compactly supported homeomorphism). -/
structure PieceSt (n p : ℕ) {M : Type*} [MetricSpace M] {N : ℕ}
    (V X : Set M) (Γ₁ : Cx N) (G L Cr : Set (E N)) (ψ : CubeChart n M)
    (g₀ : E N → M) (pieces : List (Finset (E n))) (β : ℝ)
    (r : ℕ) (Γc : Cx N) (P : Set (E N)) (gc : E N → M) (hc : M ≃ₜ M) : Prop where
  /-- `r` does not exceed the number of pieces -/
  le : r ≤ pieces.length
  /-- the current complex contains the fine one -/
  sub : Γ₁.faces ⊆ Γc.faces
  fin : Γc.faces.Finite
  dim : DimLE Γc (p + 1)
  /-- every face of `Γc` is a face of `Γ₁` or lies in the union `P` of the new far faces -/
  newP : ∀ s ∈ Γc.faces, s ∈ Γ₁.faces ∨ simp s ⊆ P
  subP : IsSubSp Γc P
  /-- the new far faces are disjoint from the fine complex -/
  disjP : Disjoint P Γ₁.space
  dimP : ∀ s ∈ Γc.faces, simp s ⊆ P → s.card ≤ p + 1
  cont : ContinuousOn gc Γc.space
  /-- the map is frozen to `g₀` on `L ∪ Cr` -/
  frz : EqOn gc g₀ (L ∪ Cr)
  /-- `ψ` is a smoothing chart for the current map on the frozen set -/
  chart : SmoothChart p X Γc (L ∪ Cr ∪ P) gc ψ
  /-- the image of the new far faces lies in the closed `11/16` cube -/
  simP : gc '' P ⊆ ψ.toFun '' closedCube (11 / 16 : ℝ)
  /-- the image of every piece attached so far is already engulfed -/
  gaff : ∀ j (hj : j < r) (hj' : j < pieces.length),
    ψ.toFun '' simp pieces[j] ⊆ gc '' P
  /-- budget: the moving map is close to `g₀` on the fine complex -/
  near : ∀ x ∈ Γ₁.space, dist (gc x) (g₀ x) ≤ (r : ℝ) * β / ((pieces.length : ℝ) + 1)
  /-- the invariant of Newman (13.2): everything already dealt with is engulfed -/
  eng : X ∪ gc '' (G ∪ P) ⊆ hc '' V
  supp : CSupp hc univ

end Work.Engulf.E4P
