import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.ThreePoints.Omega
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThreePoints.P3Sub` — vocabulary for Ch. II §4 Prop. 3 with a subnormal `Y`

Peterfalvi I, Ch. II §4, **Proposition 3 (a), (b)** in the form where the hypothesis on `X` is
the source's: `X ≤ V = C_D(t)` has a subnormal subgroup `Y ≠ 1` with `N_K(Y) ≠ 1`.  Here
`D = H ⊓ H^t = twoPoint H t`, `V = C_D(t) = centD H t` and `K = J(D,t) = invertedBy D t`.

The main objects are

* `p3F X = O^{2'}(C_G(X))`, the group `F` of the proposition;
* `HasNonTrivialNK H t X`, the hypothesis `N_K(X) ≠ 1`;
* `P3Ab H t X`, the two conclusions (a) and (b) of the proposition;
* `P3Pkg H t X = P3Ab H t X ∧ (N_G(X) is 2-transitive on Ω_X)`, the statement proved by
  induction on `|X|` (the double transitivity is used inside the induction step but is not part
  of the final conclusion).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G]

/-- `F = O^{2'}(C_G(X))`, as a subgroup of the ambient group `G` (Peterfalvi I Ch. II §4,
Prop. 3: `F = O^{2'}(C_G(X))`). -/
noncomputable def p3F (X : Subgroup G) : Subgroup G :=
  (oddResidual (Subgroup.centralizer (X : Set G))).map
    (Subgroup.centralizer (X : Set G)).subtype

/-- Membership in `p3F X = O^{2'}(C_G(X))`. -/
theorem mem_p3F {X : Subgroup G} {g : G} :
    g ∈ p3F X ↔ ∃ c ∈ oddResidual (Subgroup.centralizer (X : Set G)), (c : G) = g := by
  rw [p3F, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, hcg⟩
    exact ⟨c, hc, hcg⟩
  · rintro ⟨c, hc, hcg⟩
    exact ⟨c, hc, hcg⟩

/-- `p3F X` is contained in `C_G(X)`. -/
theorem p3F_le_centralizer (X : Subgroup G) :
    p3F X ≤ Subgroup.centralizer (X : Set G) := by
  rintro g ⟨c, -, rfl⟩
  exact c.2

/-- The hypothesis `N_K(X) ≠ 1` of Peterfalvi I Ch. II §4, Prop. 3 (part 1): there is a
non-trivial `k ∈ K` normalising `X`. -/
def HasNonTrivialNK (H : Subgroup G) (t : G) (X : Subgroup G) : Prop :=
  ∃ k ∈ invertedBy (twoPoint H t) t, k ≠ 1 ∧ k ∈ Subgroup.normalizer (X : Set G)

/-- The conclusions (a) and (b) of Peterfalvi I Ch. II §4, Prop. 3. -/
def P3Ab (H : Subgroup G) (t : G) (X : Subgroup G) : Prop :=
  Subgroup.normalizer (X : Set G) = p3F X ⊔ (centD H t ⊓ Subgroup.normalizer (X : Set G)) ∧
  ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ p3F X ⊓ H ∧
    ¬ 2 ∣ (S.subgroupOf (p3F X ⊓ H)).index ∧
    H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
    S ⊓ twoPoint H t = ⊥ ∧
    S ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) = H ⊓ Subgroup.normalizer (X : Set G)

/-- The conclusion package of Peterfalvi I Ch. II §4 Prop. 3 for `X`: the clauses (a) and (b),
together with the `2`-transitivity of `N_G(X)` on `Ω_X` which is used inside the induction. -/
abbrev P3Pkg (H : Subgroup G) (t : G) (X : Subgroup G) : Prop :=
  P3Ab H t X ∧ Work.DoubleTransitivity.IsTwoTransitiveOnSub
    (Subgroup.normalizer (X : Set G)) (fixedPts H X)

end Work.ThreePoints
