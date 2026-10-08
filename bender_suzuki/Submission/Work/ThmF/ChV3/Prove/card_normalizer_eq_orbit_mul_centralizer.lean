import Mathlib
import Submission.Work.ThmF.ChV3.Prove.OrbitCountDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `card_normalizer_eq_orbit_mul_centralizer`

Orbit–stabilizer for the conjugation action of `N_G(R)` on the subgroups of `G`, in the special
situation of step (12) of Peterfalvi II Ch. V § 3:

* `C_G(P) ≤ N_G(R)` (`hRn`), and
* `N_G(P) = C_G(P)` (`hNG`).

Conjugation by the elements of `N_G(R)` is an action of the group `N_G(R)` on `Subgroup G`; the
orbit of `P` is exactly `orb P (NG R)`, and the stabilizer of `P` consists of the `g ∈ N_G(R)`
with `g P g⁻¹ = P`, i.e. of `N_G(R) ⊓ N_G(P) = N_G(R) ⊓ C_G(P) = C_G(P)` (using `hNG`, then
`hRn`).  The orbit–stabilizer theorem (`MulAction.orbitProdStabilizerEquivGroup`) then gives
`|N_G(R)| = |orb P (NG R)| * |C_G(P)|`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

section ConjAction

variable {G : Type} [Group G]

/-- The conjugation action of a subgroup `S` of `G` on the subgroups of `G`, given by
`g • A = g A g⁻¹`.  This is the restriction to `S` of the conjugation action of `G`. -/
@[instance_reducible] private def conjMulAction (S : Subgroup G) : MulAction ↥S (Subgroup G) where
  smul g A := cj (g : G) A
  one_smul A := by
    show cj ((1 : ↥S) : G) A = A
    simp
  mul_smul a b A := by
    show cj ((a * b : ↥S) : G) A = cj (a : G) (cj (b : G) A)
    rw [Subgroup.coe_mul, cj_mul]

end ConjAction

attribute [local instance] conjMulAction

theorem card_normalizer_eq_orbit_mul_centralizer {G : Type} [Group G] [Finite G]
    {P R : Subgroup G} (hRn : Work.ThmF.ChV3.CG P ≤ Work.ThmF.ChV3.NG R)
    (hNG : Work.ThmF.ChV3.NG P = Work.ThmF.ChV3.CG P) :
    Nat.card ↥(Work.ThmF.ChV3.NG R) =
      (Work.ThmF.ChV3.Prove.orb P (Work.ThmF.ChV3.NG R)).ncard *
        Nat.card ↥(Work.ThmF.ChV3.CG P) := by
  -- orbit–stabilizer for the conjugation action of `N_G(R)`
  have hcard := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥(NG R) P)
  rw [Nat.card_prod] at hcard
  -- the orbit of `P` is `orb P (NG R)`
  have horb : MulAction.orbit ↥(NG R) P = orb P (NG R) := by
    ext A
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(g : G), g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  -- the stabilizer of `P` is `N_G(R) ⊓ N_G(P) = C_G(P)`
  have hstab : MulAction.stabilizer ↥(NG R) P = (CG P).subgroupOf (NG R) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    show cj (g : G) P = P ↔ (g : G) ∈ CG P
    rw [cj_eq_self_iff, hNG]
  have h1 : (orb P (NG R)).ncard = Nat.card ↥(MulAction.orbit ↥(NG R) P) := by
    rw [← Nat.card_coe_set_eq, horb]
  have h2 : Nat.card ↥(MulAction.stabilizer ↥(NG R) P) = Nat.card ↥(CG P) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRn).toEquiv
  rw [h1, ← h2]
  exact hcard.symm

end Work.ThmF.ChV3.Prove
