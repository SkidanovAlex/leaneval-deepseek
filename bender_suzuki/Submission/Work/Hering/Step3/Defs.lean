import Mathlib
import Submission.Work.Hering.Perm.Defs
import Submission.Work.Hering.InvSubgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Vocabulary for Peterfalvi I §2 Step 3 (`C_G(U)` is a 2-group)

The reduction step of Chapter IV §2 of Peterfalvi I reduces a minimal group `G` of 2-rank `≥ 2`
acting doubly transitively on its involutions to a group with an elementary abelian normal
subgroup `V = Inv(G) ∪ {1}` of order `8`.  Step 3 of that reduction states that `C_G(U)` is a
`2`-group for every subgroup `U ≤ V` of order `4`.

This file fixes the vocabulary used by `Work.Hering.Step3.centralizer_isPGroup`:

* `instSMulInvolutions` / `instMulActionInvolutions` -- the conjugation action of `G` on its set
  `Inv(G)` of involutions, so that the double-transitivity hypothesis `DTInv G` becomes
  `IsTwoTransitiveAction G {x // x ∈ involutions G}` and Appendix II(5) applies;
* `involutionsFixedBy P` -- the set of involutions fixed by `P` in that action, which is the
  set on which `N_G(P)` is doubly transitive for `P` a Sylow `p`-subgroup (`p` odd) of a
  two-point stabiliser, `= (C_G(P) ∩ V)^#`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Hering.Step3

open LeanEval.GroupTheory.Defs
open Work.Hering

/-- The conjugation action `g • x = g x g⁻¹` of `G` on its set of involutions. -/
instance instSMulInvolutions {G : Type*} [Group G] : SMul G {x : G // x ∈ involutions G} where
  smul g x := ⟨g * (x : G) * g⁻¹, involutions_conj_mem x.2 g⟩

@[simp] theorem coe_smul_involutions {G : Type*} [Group G] (g : G)
    (x : {x : G // x ∈ involutions G}) :
    ((g • x : {x : G // x ∈ involutions G}) : G) = g * (x : G) * g⁻¹ := rfl

/-- **The conjugation action of `G` on its set of involutions** `Inv(G)`, `g • x = g x g⁻¹`. -/
instance instMulActionInvolutions {G : Type*} [Group G] :
    MulAction G {x : G // x ∈ involutions G} where
  one_smul x := Subtype.ext (by simp)
  mul_smul g h x := Subtype.ext (by simp [mul_assoc])

/-- The set of involutions fixed by the subgroup `P` under the conjugation action. -/
def involutionsFixedBy {G : Type*} [Group G] (P : Subgroup G) :
    Set {x : G // x ∈ involutions G} :=
  {x | ∀ p ∈ P, p • x = x}

/-- An involution is fixed by `P` exactly when it centralises `P`. -/
theorem mem_involutionsFixedBy_iff {G : Type*} [Group G] {P : Subgroup G}
    {x : {x : G // x ∈ involutions G}} :
    x ∈ involutionsFixedBy P ↔ (x : G) ∈ Subgroup.centralizer (P : Set G) := by
  change (∀ p ∈ P, p • x = x) ↔ (x : G) ∈ Subgroup.centralizer (P : Set G)
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : y * (x : G) * y⁻¹ = (x : G) := by
      have h2 := h y hy
      have h3 := congrArg (fun t : {x : G // x ∈ involutions G} => (t : G)) h2
      simpa using h3
    calc y * (x : G) = y * (x : G) * y⁻¹ * y := by group
      _ = (x : G) * y := by rw [h1]
  · intro h y hy
    apply Subtype.ext
    simp only [coe_smul_involutions]
    have hc := (Subgroup.mem_centralizer_iff.mp h) y hy
    rw [hc]
    group

/-- The centraliser of `P` is contained in its normaliser; a fixed involution therefore lies in
`N_G(P)`, so that it can be pushed to `N_G(P)/P`. -/
theorem mem_normalizer_of_mem_involutionsFixedBy {G : Type*} [Group G] {P : Subgroup G}
    {x : {x : G // x ∈ involutions G}} (hx : x ∈ involutionsFixedBy P) :
    (x : G) ∈ Subgroup.normalizer (P : Set G) :=
  Subgroup.centralizer_le_normalizer (P : Set G) (mem_involutionsFixedBy_iff.mp hx)

end Work.Hering.Step3
