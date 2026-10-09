/-
Copyright (c) 2025. All rights reserved.

# The action of `G ⧸ N` on `H¹(N, A)`

This assembles the conjugation action of `G` on `H¹(N,A)`
(`Submission/Work/GroupCohomology/Conjugation.lean`) into an action of the quotient `G ⧸ N`:
conjugation by an element of `N` is an inner automorphism, and inner automorphisms act trivially
on `H¹`, so the monoid homomorphism `G →* AddMonoid.End (H¹(N,A))` descends along `G → G ⧸ N`.

The invariants of this action, `invariants (G ⧸ N) (H¹(N,A))`, are the third term of the
five-term exact sequence `0 → H¹(G/N, A^N) → H¹(G,A) → H¹(N,A)^{G/N} → H²(G/N, A^N) → H²(G,A)`.
-/
import Submission.Work.GroupCohomology.Conjugation
import Submission.Work.GroupCohomology.conjCocycle_one
import Submission.Work.GroupCohomology.conjCocycle_comp
import Submission.Work.GroupCohomology.conjCocycle_of_mem
import Submission.Work.GroupCohomology.conjH1_of_mem

universe u v

namespace Work.GroupCohomology

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (N : Subgroup G) [N.Normal]

theorem conjH1_one : conjH1 (A := A) N (1 : G) = AddMonoidHom.id (H1 N A) := by
  refine AddMonoidHom.ext ?_
  intro x
  induction x using H1_induction_on with
  | h f => rw [conjH1_H1π, conjCocycle_one, AddMonoidHom.id_apply]

theorem conjH1_comp (g h : G) :
    conjH1 (A := A) N (g * h) =
      (conjH1 (A := A) N g).comp (conjH1 (A := A) N h) := by
  refine AddMonoidHom.ext ?_
  intro x
  induction x using H1_induction_on with
  | h f =>
      rw [conjH1_H1π, conjCocycle_comp, AddMonoidHom.comp_apply, conjH1_H1π, conjH1_H1π]

/-- The conjugation action of `G` on `H¹(N, A)`, as a monoid homomorphism. -/
noncomputable def conjHom : G →* AddMonoid.End (H1 N A) where
  toFun g := conjH1 (A := A) N g
  map_one' := conjH1_one N
  map_mul' g h := conjH1_comp N g h

@[simp] theorem conjHom_apply (g : G) : conjHom (A := A) N g = conjH1 (A := A) N g := rfl

/-- The action of `G ⧸ N` on `H¹(N, A)` induced by conjugation.  It is well defined because
conjugation by an element of `N` acts trivially on `H¹(N, A)`. -/
noncomputable def quotientConjEnd : (G ⧸ N) →* AddMonoid.End (H1 N A) :=
  QuotientGroup.lift N (conjHom (A := A) N) (by
    intro n hn
    rw [MonoidHom.mem_ker]
    refine AddMonoidHom.ext ?_
    intro x
    exact conjH1_of_mem N ⟨n, hn⟩ x)

@[simp] theorem quotientConjEnd_mk' (g : G) :
    quotientConjEnd (A := A) N (QuotientGroup.mk' N g) = conjH1 (A := A) N g := by
  rw [quotientConjEnd, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
  rfl

/-- The action of `G ⧸ N` on `H¹(N, A)` induced by conjugation. -/
noncomputable instance quotientConjSMul : SMul (G ⧸ N) (H1 N A) where
  smul q x := quotientConjEnd (A := A) N q x

@[simp] theorem quotientConjSMul_mk' (g : G) (x : H1 N A) :
    (QuotientGroup.mk' N g) • x = conjH1 (A := A) N g x := by
  show quotientConjEnd (A := A) N (QuotientGroup.mk' N g) x = conjH1 (A := A) N g x
  rw [quotientConjEnd_mk']
  rfl

noncomputable instance quotientConjDistribMulAction : DistribMulAction (G ⧸ N) (H1 N A) where
  one_smul x := by
    show quotientConjEnd (A := A) N 1 x = x
    rw [map_one]
    rfl
  mul_smul q q' x := by
    show quotientConjEnd (A := A) N (q * q') x =
      quotientConjEnd (A := A) N q (quotientConjEnd (A := A) N q' x)
    rw [map_mul]
    rfl
  smul_zero q := map_zero (quotientConjEnd (A := A) N q)
  smul_add q x y := map_add (quotientConjEnd (A := A) N q) x y

end Work.GroupCohomology
