import Mathlib
import Submission.Work.PSU3.BenderST
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Abstract.inf_conj_w
import Submission.Work.Models.Abstract.involutions_subset_U

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.BenderST.Defs` — the "standard clause" interface

`BenderSTProp` (`Submission/Work/PSU3/BenderST.lean`) asks, for a simple Bender group `Y`, a
split rank-one datum `(B,U,w)` and a distinguished involution `s ∈ U`, for one of three
clauses (PSL2 / Sz / PSU3).

`StdClause P` is that same three-way disjunction, but for the *standard* split rank-one datum
`(P.B, P.U, P.w)` of a fixed `BenderPair` `P` (in practice the standard datum of one of the
three models).  The three concrete model computations (`psl2_standard_clause`,
`sz_standard_clause`, `psu3_standard_clause`) are stated with it, and the abstract reduction
`datum_conj_standard` shows that every split rank-one datum of a group carrying `P` is
conjugate to the standard one, so that `StdClause P` transfers to an arbitrary datum.

`benderPair_isSplitRankOne` records that the standard datum of a `BenderPair` whose Weyl
element is an involution is itself a split rank-one datum (`benderST`'s reduction and the
three model computations both need it).
-/

open LeanEval.GroupTheory.Defs
open Submission.Blueprint (involutions twoPoint IsAbelianSubgroup IsSplitRankOne)

namespace Work.PSU3.BenderST

/-- The `BenderSTProp` disjunction for one fixed `BenderPair` `P`, read on the standard datum
`(P.B, P.U, P.w)`: for every `s, r ∈ P.U` with `orderOf s = 2` and `P.w * s * P.w = r⁻¹ * P.w * r`
one of the PSL2 / Sz / PSU3 clauses holds, with `q = #Inv(P.B) + 1`. -/
def StdClause {M : Type} [Group M] [Finite M] (P : Submission.BenderPair M) : Prop :=
  ∀ s r : M, s ∈ P.U → orderOf s = 2 → r ∈ P.U → P.w * s * P.w = r⁻¹ * P.w * r →
  let q := (involutions (P.B : Set M)).ncard + 1
  (orderOf (s * P.w) = 3 ∧ IsAbelianSubgroup P.U ∧ Nat.card P.U = q) ∨
  (orderOf (s * P.w) = 5 ∧ ¬ IsAbelianSubgroup P.U ∧ Nat.card P.U = q ^ 2 ∧
    ∀ x ∈ P.U, ∀ y ∈ P.U, x ^ 2 = y ^ 2 →
      x * y⁻¹ ∈ Subgroup.closure (involutions (P.U : Set M))) ∨
  (orderOf (s * P.w) = 3 ∧ Nat.card P.U = q ^ 3 ∧
    ∃ x ∈ twoPoint P.B P.w, x ≠ 1 ∧ ∀ u ∈ involutions (P.B : Set M), x * u = u * x)

/-- The standard datum of a `BenderPair` with involutive Weyl element is a split rank-one
datum: `Q = P.U`, `H = P.B`, `t = P.w`.  (`twoPoint P.B P.w = P.T` is
`Work.Models.Abstract.inf_conj_w`.) -/
theorem benderPair_isSplitRankOne {G : Type} [Group G] [Finite G]
    (P : Submission.BenderPair G) (hww : P.w * P.w = 1) :
    IsSplitRankOne P.B P.U P.w where
  stronglyEmbedded := P.hSemb
  twoTransitive := P.isMultiplyPretransitive_two
  invol := by
    have h2 : P.w ^ 2 = 1 := by rw [pow_two]; exact hww
    have hne : P.w ≠ 1 := by intro h1; exact P.hwB (h1 ▸ P.U_le_B (by simp))
    exact orderOf_eq_prime_iff.mpr ⟨h2, hne⟩
  not_mem := P.hwB
  le := P.U_le_B
  normal := P.le_normalizer_U
  inf_eq := by
    rw [Work.Models.twoPoint_def, Work.Models.Abstract.inf_conj_w P]; exact P.hUT
  sup_eq := by
    rw [Work.Models.twoPoint_def, Work.Models.Abstract.inf_conj_w P, ← P.hB]

end Work.PSU3.BenderST
