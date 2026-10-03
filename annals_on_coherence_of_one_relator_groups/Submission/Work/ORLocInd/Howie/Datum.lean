/-
# Data in a staggered groupoid presentation (Howie 2000, proof of Theorem 3.1)

Howie's proof of Theorem 3.1 is by contradiction, with a *datum* `∆` consisting of:

* `n` reduced closed paths `γ_1, …, γ_n` at a vertex `v` of the graph (the generators of the
  subgroup `H = ⟨γ_1, …, γ_n⟩` of the vertex group `π₁(⟨Γ | R⟩, v)`);
* `n` words `W_1, …, W_n` in the free group on `n` generators, presenting a group with finite
  abelianisation;
* for each `j` and each term `k` of the `j`-th word, a relator `α_{j,k}` (of `R` or its inverse) and
  a path `δ_{j,k}` from `v` to the base vertex of `α_{j,k}`, such that the identity
  `W_j(γ_1, …, γ_n) = ∏_k δ_{j,k} α_{j,k} δ_{j,k}⁻¹` holds in the free groupoid `F(Γ)`.

The measure on which the proof inducts is `L(∆) - M(∆)`, where `L(∆)` is the sum of the lengths of
all the paths `δ_{j,k}` and `α_{j,k}` and `M(∆)` is the number of distinct vertices visited by the
datum.  In the formalisation the induction is on the (manifestly decreasing) quantity
`2 * L(∆) - M(∆)`: the cyclic-cover step of Case 1 keeps `L` and strictly increases `M`.

The same data occur in the second induction (Case 2), where the *number of relators* of the
presentation decreases.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.PresentedGroup

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V] [DecidableEq V]

/-- A *term* of a datum: a relator (or its inverse) together with a path from the base vertex `v`
to the base vertex of the relator. -/
structure RelatorTerm (P : Presentation V) (v : V) where
  /-- the index of the relator -/
  i : P.ι
  /-- whether to use the relator or its inverse -/
  sign : Bool
  /-- the path from `v` to the base vertex of the relator -/
  δ : Quiver.Path v (P.base i)
  /-- the path is reduced -/
  reduced : δ.IsReduced

namespace RelatorTerm

variable {P : Presentation V} {v : V}

/-- The relator of a term, with its inverse if the sign is set. -/
noncomputable def signedPath (t : RelatorTerm P v) : Quiver.Path (P.base t.i) (P.base t.i) :=
  if t.sign then (P.path t.i).reverse else P.path t.i

theorem signedPath_isReduced (t : RelatorTerm P v) : (t.signedPath).IsReduced := by
  unfold signedPath
  split
  · exact (P.reduced t.i).reverse
  · exact P.reduced t.i

/-- The conjugate `δ · α^{±1} · δ⁻¹` of a term, as an element of the vertex group at `v`. -/
noncomputable def loop (t : RelatorTerm P v) : VertexGroup v :=
  ⟨pmul t.δ (pmul t.signedPath t.δ.reverse), pmul_isReduced _ _⟩

/-- The vertices visited by a term, as a list. -/
noncomputable def visitedList (t : RelatorTerm P v) : List V :=
  t.δ.vertices ++ (P.path t.i).vertices

/-- The length contribution of a term to `L(∆)`. -/
noncomputable def weight (t : RelatorTerm P v) : ℕ := t.δ.length + (P.path t.i).length

end RelatorTerm

/-- A *datum* in a groupoid presentation `⟨Γ | R⟩`, following Howie. -/
structure Datum (P : Presentation V) (v : V) (n : ℕ) where
  /-- the generators of `H` -/
  γ : Fin n → VertexGroup v
  /-- the words presenting a group with finite abelianisation -/
  W : Fin n → FreeGroup (Fin n)
  /-- the witnesses of the relations in the vertex group -/
  terms : (j : Fin n) → List (RelatorTerm P v)
  /-- the identities of the datum -/
  heq : ∀ j, FreeGroup.lift γ (W j) = ((terms j).map RelatorTerm.loop).prod

namespace Datum

variable {P : Presentation V} {v : V} {n : ℕ}

/-- `L(∆)`: the total length of the paths of the datum — the `γ_j`, and the `δ`'s and relator paths
of the terms.  (The `γ_j` are included so that `M(∆) ≤ L(∆) + 1`, which makes the truncated
subtraction in `measure` behave; the cyclic-cover step preserves `L` in either formulation.) -/
noncomputable def L (D : Datum P v n) : ℕ :=
  (∑ j, (D.γ j).1.length) + ∑ j, ((D.terms j).map RelatorTerm.weight).sum

/-- The vertices visited by the datum (including the base vertex), as a list. -/
noncomputable def visitedList (D : Datum P v n) : List V :=
  [v] ++ (List.finRange n).flatMap (fun j => (D.γ j).1.vertices) ++
    (List.finRange n).flatMap (fun j => (D.terms j).flatMap RelatorTerm.visitedList)

/-- `M(∆)`: the number of distinct vertices visited by the datum. -/
noncomputable def M (D : Datum P v n) : ℕ := D.visitedList.dedup.length

/-- The induction measure `2 * L(∆) + 2 - M(∆)`.  It strictly decreases in the cyclic-cover step,
where `L` is unchanged and `M` strictly increases, *without* any truncation: the (provable)
inequality `M(∆) ≤ L(∆) + 1` shows that both `2 * L + 2 - M` are genuine subtractions. -/
noncomputable def measure (D : Datum P v n) : ℕ := 2 * D.L + 2 - D.M

end Datum

end Work.ORLocInd.Howie
