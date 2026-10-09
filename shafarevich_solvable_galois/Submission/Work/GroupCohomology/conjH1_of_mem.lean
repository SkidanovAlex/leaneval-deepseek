/-
Copyright (c) 2025. All rights reserved.

# Inner automorphisms act trivially on `H¹`

For a normal subgroup `N ◁ G` and a `G`-module `A`, conjugation by an element `n : N` acts on
`H¹(N, A)` through the automorphism `conjH1 (N := N) n : H¹(N, A) →+ H¹(N, A)`.  Since `n ∈ N`,
conjugation by `n` is an *inner* automorphism of `N`, and inner automorphisms act trivially on
group cohomology: on the level of cocycles,

`conjCocycle n f - f = d⁰(f n)`,

i.e. the difference of `f` and its conjugate is the coboundary of the value `f n ∈ A`.  Hence
`conjH1 (N := N) n = id` on `H¹(N, A)`.

The computation of the conjugate cocycle is the standard one: for a crossed homomorphism `f` on `N`
and `n, m : N`,

`f (n⁻¹ * m * n) = n⁻¹ • f (m * n) + f n⁻¹ = n⁻¹ • (m • f n + f m) + f n⁻¹`,

so applying `n`, and using `n • f n⁻¹ = -f n`,

`n • f (n⁻¹ * m * n) = m • f n + f m - f n`,

which is exactly `f m + d⁰(f n) m`.

This is the ingredient showing that the conjugation action of `G` on `H¹(N, A)` kills `N`, so that
it descends to the quotient `G ⧸ N` (see `Conjugation.lean`).
-/
import Mathlib
import Submission.Work.GroupCohomology.Conjugation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

section Aux

variable {G : Type*} {A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (N : Subgroup G) [N.Normal]

/-- Conjugation by `n : N` of a `1`-cocycle of `N`, evaluated at `m : N`, is
`n • f (n⁻¹ * m * n)`: conjugation by an element of `N` is conjugation *in* `N`. -/
lemma conjCocycle_of_mem_apply (n : N) (f : Z1 N A) (m : N) :
    (conjCocycle N (n : G) f : N → A) m = n • (f : N → A) (n⁻¹ * m * n) := by
  have hconj : (conjAutN N (n : G))⁻¹ m = n⁻¹ * m * n := by
    apply Subtype.ext
    rw [conjAutN_symm_apply]
    simp
  rw [conjCocycle_apply, hconj]
  exact (subgroup_smul_coe N n ((f : N → A) (n⁻¹ * m * n))).symm

/-- Pointwise form of `conjCocycle n f - f = d⁰(f n)`: conjugation by `n : N` differs from the
identity on the cocycle `f` by the coboundary of the value `f n`. -/
lemma conjCocycle_of_mem_sub_apply (n : N) (f : Z1 N A) (m : N) :
    (conjCocycle N (n : G) f : N → A) m - (f : N → A) m
      = m • (f : N → A) n - (f : N → A) n := by
  rw [conjCocycle_of_mem_apply N n f m]
  have h1 : (f : N → A) (n⁻¹ * m * n) = n⁻¹ • (f : N → A) (m * n) + (f : N → A) n⁻¹ := by
    rw [mul_assoc]
    exact f.2 n⁻¹ (m * n)
  have h2 : (f : N → A) (m * n) = m • (f : N → A) n + (f : N → A) m := f.2 m n
  have h3 : n • (f : N → A) n⁻¹ = -(f : N → A) n := Z1.map_inv N A f.2 n
  rw [h1, h2, smul_add, smul_add, smul_add, smul_inv_smul, smul_inv_smul, h3]
  abel

/-- Conjugation by `n : N` sends a `1`-cocycle of `N` to a cocycle differing from it by the
coboundary `d⁰(f n)`: as functions on `N`,
`conjCocycle n f - f = d⁰(f n)`. -/
lemma conjCocycle_of_mem_sub_eq_d0 (n : N) (f : Z1 N A) :
    ((conjCocycle N (n : G) f - f : Z1 N A) : N → A) = d0 N A ((f : N → A) n) := by
  funext m
  rw [AddSubgroup.coe_sub, Pi.sub_apply, d0_apply]
  exact conjCocycle_of_mem_sub_apply N n f m

end Aux

theorem conjH1_of_mem {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (N : Subgroup G) [N.Normal] (n : N)
    (x : Work.GroupCohomology.H1 N A) :
    Work.GroupCohomology.conjH1 (N := N) n x = x := by
  refine H1_induction_on (G := N) (A := A)
    (C := fun y => conjH1 (N := N) (n : G) y = y) x ?_
  intro f
  rw [conjH1_H1π]
  have hmem : ((conjCocycle N (n : G) f - f : Z1 N A) : N → A) ∈ B1 N A :=
    ⟨(f : N → A) n, (conjCocycle_of_mem_sub_eq_d0 N n f).symm⟩
  rw [H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_comap]
  exact hmem

end Work.GroupCohomology
