/-
# `Work.SmallRank.Regular` : P. Hall's regular `p`-groups (Huppert, *Endliche Gruppen I*, III §9–§10)

Every `p`-group of `p`-rank `≤ 2` with `p ≥ 5` is regular (Huppert Satz 10.14), and regularity is
what turns the classification of `p`-groups of rank `≤ 2` (FT 3.4, in the form consumed by FT 26.1
and 26.2) into a short argument.  This file fixes the vocabulary; the theory is in the sibling
files of `Submission/Work/SmallRank/Regular/`.

## References

* B. Huppert, *Endliche Gruppen I*, Springer 1967: III §9 (Hall–Petrescu), §10 (regular groups),
  Satz 10.14 (a `p`-group with no normal subgroup of exponent `p` and order `p^{p-1}` is regular).
* P. Hall, *A contribution to the theory of groups of prime power order*, Proc. LMS 36 (1934).
-/
import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.SmallRank

variable {X : Type*} [Group X]

/-- P. Hall: `X` is *regular* (Huppert III.10.1) if for all `x y : X` there is
`d ∈ ℧¹(⟨x,y⟩')` with `x^p y^p = (x y)^p d`. -/
def IsRegular (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ x y : X, ∃ d ∈ Work.PGroup.agemo p 1
      (⁅Subgroup.closure ({x, y} : Set X), Subgroup.closure ({x, y} : Set X)⁆ : Subgroup X),
    x ^ p * y ^ p = (x * y) ^ p * d

/-- The set `{x | x^(p^k) = 1}`.  For a regular `p`-group this is the subgroup `Ω_k(X)`
(Huppert III.10.5); for `k = 1` it agrees with `Work.PGroup.omega p 1 ⊤` (as a set). -/
def powSet (p k : ℕ) (X : Type*) [Group X] : Set X := {x : X | x ^ (p ^ k) = 1}

/-- The commutator subgroup `[G,G] = ⁅⊤,⊤⁆` of a group (the notation the plan uses
in the type-level statements of the regularity theory). -/
def commutator (G : Type*) [Group G] : Subgroup G := ⁅(⊤ : Subgroup G), ⊤⁆

end Work.SmallRank
