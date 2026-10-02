import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# Shared vocabulary for the spanning-linkage development

This module collects the definitions used by `Work.Deep.GKO.exists_spanningLinearForest`
and by the auxiliary lemmas proved for it.  Everything here is stated in terms of
`Finset`/`Set.ncard` so that no decidability instances are needed in the statements.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Deep.GKO

noncomputable section

variable {n : ℕ}

/-- The number of neighbours of `v` inside the vertex set `U`. -/
def nbrIn (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (v : Fin n) : ℕ :=
  (G.neighborSet v ∩ (U : Set (Fin n))).ncard

/-- `U` is `(p,ε)`-lower-regular inside `G`, with the thresholds measured relative
to the size of `U` rather than to the ambient vertex count. -/
def LowerRegOn (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (p ε : ℝ) : Prop :=
  ∀ A B : Finset (Fin n), A ⊆ U → B ⊆ U → Disjoint A B →
    ε * (U.card : ℝ) ≤ (A.card : ℝ) → ε * (U.card : ℝ) ≤ (B.card : ℝ) →
    (p - ε) * (A.card : ℝ) * (B.card : ℝ) ≤ (crossEdges G A B : ℝ)

/-- Every vertex of `U` has at least `α |U|` neighbours inside `U`. -/
def MinDegOn (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (α : ℝ) : Prop :=
  ∀ v ∈ U, α * (U.card : ℝ) ≤ (nbrIn G U v : ℝ)

/-- **A spanning path of `U` between `a` and `b`.**  There is a path in `G` from `a`
to `b` whose vertex set is exactly `U`. -/
def SpansPath (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (a b : Fin n) : Prop :=
  a ∈ U ∧ b ∈ U ∧ a ≠ b ∧
    ∃ w : G.Walk a b, w.IsPath ∧ ∀ v : Fin n, (v ∈ w.support ↔ v ∈ U)

lemma nbrIn_le (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (v : Fin n) :
    nbrIn G U v ≤ U.card := by
  classical
  have h : (G.neighborSet v ∩ (U : Set (Fin n))).ncard ≤ U.card := by
    rw [← Set.ncard_coe_finset (s := U)]
    exact Set.ncard_le_ncard (by intro x hx; exact hx.2) (Set.toFinite _)
  simpa [nbrIn] using h

lemma nbrIn_mono {G : SimpleGraph (Fin n)} {U V : Finset (Fin n)} (h : U ⊆ V) (v : Fin n) :
    nbrIn G U v ≤ nbrIn G V v := by
  classical
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro x hx
  exact ⟨hx.1, h hx.2⟩

end
end Work.Deep.GKO
