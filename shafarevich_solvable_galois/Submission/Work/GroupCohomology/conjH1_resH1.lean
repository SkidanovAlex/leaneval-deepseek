/-
Copyright (c) 2025. All rights reserved.

# Restriction lands in the invariants of the conjugation action

For a normal subgroup `N ◁ G` and a `G`-module `A`, restriction `resH1 : H¹(G, A) → H¹(N, A)`
has image inside the invariants of the conjugation action of `G` on `H¹(N, A)` (see
`Submission/Work/GroupCohomology/Conjugation.lean`).  This is the standard observation that the
conjugation action of `G` on the cohomology of `G` itself is trivial: on cocycles, for a crossed
homomorphism `f` on `G` and any `g, x : G`,

`f (g⁻¹ * x * g) = (g⁻¹ * x) • f g + g⁻¹ • f x + f g⁻¹`,

so, applying `g` and using `g • f g⁻¹ = -f g`,

`g • f (g⁻¹ * x * g) = x • f g + f x - f g`,

i.e. the conjugate of `f` differs from `f` by the coboundary `d⁰ (f g)`.  Consequently, restricting
a class of `H¹(G, A)` to `N` gives a class fixed by `conjH1 N g` for every `g : G`.
-/
import Mathlib
import Submission.Work.GroupCohomology.Conjugation
import Submission.Work.GroupCohomology.Functoriality
import Submission.Work.GroupCohomology.H1pi_eq_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

section Aux

variable {G : Type*} {A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (N : Subgroup G) [N.Normal]

/-- Conjugating a `1`-cocycle of `N` that is the restriction of a `1`-cocycle `f` of `G` changes
it by the coboundary `d⁰ (f g)`: as functions on `N`,

`conjCocycle g (resZ1 f) - resZ1 f = d⁰ (f g)`.

This is the cocycle-level form of the triviality of the conjugation action of `G` on `H¹(G, A)`. -/
theorem conjCocycle_resZ1_sub_eq_d0 (g : G) (f : Z1 G A) :
    ((conjCocycle N g (resZ1 G N f) - resZ1 G N f : Z1 N A) : N → A) =
      d0 N A ((f : G → A) g) := by
  funext m
  rw [AddSubgroup.coe_sub, Pi.sub_apply, d0_apply, conjCocycle_apply, resZ1_coe, resCochain1_apply]
  have hcoe : (↑((conjAutN N g)⁻¹ m) : G) = g⁻¹ * (m : G) * g := by
    rw [conjAutN_symm_apply]
  rw [hcoe, resCochain1_apply, f.2 (g⁻¹ * (m : G)) g, f.2 g⁻¹ (m : G), smul_add, smul_add,
    Z1.map_inv G A f.2 g, ← mul_smul, ← mul_smul]
  have e1 : g * (g⁻¹ * (m : G)) = (m : G) := by group
  have e2 : g * g⁻¹ = (1 : G) := mul_inv_cancel g
  rw [e1, e2, one_smul]
  simp only [subgroup_smul_coe]
  abel

end Aux

/-- Restriction to a normal subgroup lands in the invariants of the conjugation action of `G` on
`H¹(N, A)`: conjugation by any `g : G` fixes the restriction of a class of `H¹(G, A)`. -/
theorem conjH1_resH1 {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (N : Subgroup G) [N.Normal] (g : G) (y : Work.GroupCohomology.H1 G A) :
    Work.GroupCohomology.conjH1 (A := A) N g
        (Work.GroupCohomology.resH1 (A := A) G N y) =
      Work.GroupCohomology.resH1 (A := A) G N y := by
  induction y using H1_induction_on with
  | h f =>
    rw [resH1_H1π, conjH1_H1π, H1pi_eq_iff]
    exact ⟨(f : G → A) g, (conjCocycle_resZ1_sub_eq_d0 N g f).symm⟩

end Work.GroupCohomology
