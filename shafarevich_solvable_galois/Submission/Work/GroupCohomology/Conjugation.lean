/-
Copyright (c) 2025. All rights reserved.

# The action of `G` (and of `G ⧸ N`) on the cohomology of a normal subgroup

For a normal subgroup `N ◁ G` and a `G`-module `A`, conjugation by `g : G` acts on `N`, hence on
the cochains, cocycles and cohomology of `N` with coefficients in `A`:

`conjCocycle g f (n) = g • f (g⁻¹ * n * g)`,  `conjH1 g : H¹(N,A) →+ H¹(N,A)`.

The resulting monoid homomorphism `G →* AddAut (H¹(N,A))` kills `N` (conjugation by an element of
`N` is an inner automorphism, and inner automorphisms act trivially on `H¹`), so it descends to an
action of `G ⧸ N`:

`quotientConjEnd : (G ⧸ N) →* AddAut (H¹(N,A))`,  `quotientConjDistribMulAction`.

This is the ingredient of the five-term exact sequence
`0 → H¹(G/N, A^N) → H¹(G,A) → H¹(N,A)^{G/N} → H²(G/N, A^N) → H²(G,A)`.
-/
import Submission.Work.GroupCohomology.Functoriality
import Submission.Work.GroupCohomology.Inflation
import Submission.Work.GroupCohomology.H1_induction_on
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (N : Subgroup G) [N.Normal]

/-- The automorphism of `N` given by conjugation by `g : G` (well defined for `N ◁ G`). -/
noncomputable def conjAutN (g : G) : MulAut N := MulAut.conjNormal (H := N) g

@[simp] theorem conjAutN_apply (g : G) (n : N) : conjAutN N g n = g * n * g⁻¹ :=
  MulAut.conjNormal_apply g n

theorem conjAutN_symm_apply (g : G) (n : N) :
    (conjAutN N g)⁻¹ n = g⁻¹ * n * g :=
  MulAut.conjNormal_symm_apply g n

/-- The action of a subgroup is the action of the ambient group (definitional). -/
theorem subgroup_smul_coe (m : N) (a : A) : (m : N) • a = (m : G) • a := rfl

/-- Conjugation of `1`-cocycles of `N` by `g : G`. -/
noncomputable def conjCocycle (g : G) : Z1 N A →+ Z1 N A where
  toFun f := ⟨fun n => g • (f : N → A) ((conjAutN N g)⁻¹ n), by
    rw [mem_Z1_iff]
    intro m n
    change g • (f : N → A) ((conjAutN N g)⁻¹ (m * n)) =
      m • (g • (f : N → A) ((conjAutN N g)⁻¹ n)) +
        g • (f : N → A) ((conjAutN N g)⁻¹ m)
    rw [map_mul, f.2, smul_add]
    congr 1
    rw [subgroup_smul_coe, subgroup_smul_coe]
    rw [← mul_smul, ← mul_smul]
    congr 1
    rw [conjAutN_symm_apply]
    group⟩
  map_zero' := by ext n; simp
  map_add' f f' := by ext n; simp [smul_add]

@[simp] theorem conjCocycle_apply (g : G) (f : Z1 N A) (n : N) :
    (conjCocycle N g f : N → A) n = g • (f : N → A) ((conjAutN N g)⁻¹ n) := rfl

theorem conjCocycle_mem_B1 (g : G) {f : Z1 N A} (hf : (f : N → A) ∈ B1 N A) :
    (conjCocycle N g f : N → A) ∈ B1 N A := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨g • a, ?_⟩
  funext n
  rw [conjCocycle_apply, ← ha]
  simp only [d0_apply, smul_sub]
  rw [subgroup_smul_coe, subgroup_smul_coe, ← mul_smul, ← mul_smul]
  congr 1
  rw [conjAutN_symm_apply]
  group

/-- The action of `G` on `H¹(N, A)` induced by conjugation. -/
noncomputable def conjH1 (g : G) : H1 N A →+ H1 N A :=
  QuotientAddGroup.lift ((B1 N A).comap (Z1 N A).subtype)
    ((H1π N A).comp (conjCocycle N g)) (by
      intro x hx
      have hx' : ((x : Z1 N A) : N → A) ∈ B1 N A := by
        simpa using (AddSubgroup.mem_comap.mp hx)
      have hy : ((conjCocycle N g x : Z1 N A) : N → A) ∈ B1 N A :=
        conjCocycle_mem_B1 N g hx'
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H1π, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      exact hy)

theorem conjH1_H1π (g : G) (f : Z1 N A) :
    conjH1 N g (H1π N A f) = H1π N A (conjCocycle N g f) :=
  QuotientAddGroup.lift_mk' _ _ f

end Work.GroupCohomology
