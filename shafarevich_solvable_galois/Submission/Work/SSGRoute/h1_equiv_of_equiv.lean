import Mathlib
import Submission.Work.SSGRoute.homCoindDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹` is functorial in the coefficients, up to isomorphism

If `Φ : M ≃+ N` is an isomorphism of `G`-modules (an additive equivalence commuting with the
action of `G`), then the induced maps `H¹(G,M) → H¹(G,N)` and `H¹(G,N) → H¹(G,M)` are mutually
inverse, so that `H¹(G,M) ≃+ H¹(G,N)`.

The induced map on `1`-cocycles is `Work.AbsoluteKummer.mapZ1` and the induced map on cohomology
is `Work.AbsoluteKummer.mapH1` (`Submission/Work/AbsoluteKummer/Basic.lean`).  The point is that
`mapZ1` is functorial also at the level of `Z¹` (and hence of `H¹`), so that the two composites
are the identity on cocycles; the quotient statement follows by induction on the quotient.
-/

namespace Work.SSGRoute

open Work.AbsoluteKummer

namespace H1Equiv

variable {G : Type} [Group G] [TopologicalSpace G]
variable {M : Type} [AddCommGroup M] [DistribMulAction G M]
variable {N : Type} [AddCommGroup N] [DistribMulAction G N]

/-- `mapZ1` for `Φ.symm` is a left inverse of `mapZ1` for `Φ`. -/
theorem mapZ1_symm_comp (Φ : M ≃+ N)
    (hΦ : Work.GroupCohomology.IsEquivariant G Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant G Φ.symm.toAddMonoidHom) (f : Z1 G M) :
    mapZ1 Φ.symm.toAddMonoidHom hΨ (mapZ1 Φ.toAddMonoidHom hΦ f) = f := by
  ext g
  simp

/-- `mapZ1` for `Φ.symm` is a right inverse of `mapZ1` for `Φ`. -/
theorem mapZ1_comp_symm (Φ : M ≃+ N)
    (hΦ : Work.GroupCohomology.IsEquivariant G Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant G Φ.symm.toAddMonoidHom) (f : Z1 G N) :
    mapZ1 Φ.toAddMonoidHom hΦ (mapZ1 Φ.symm.toAddMonoidHom hΨ f) = f := by
  ext g
  simp

/-- `mapH1` for `Φ.symm` is a left inverse of `mapH1` for `Φ`. -/
theorem mapH1_symm_comp (Φ : M ≃+ N)
    (hΦ : Work.GroupCohomology.IsEquivariant G Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant G Φ.symm.toAddMonoidHom) (x : H1 G M) :
    mapH1 Φ.symm.toAddMonoidHom hΨ (mapH1 Φ.toAddMonoidHom hΦ x) = x := by
  refine QuotientAddGroup.induction_on x ?_
  intro f
  change mapH1 Φ.symm.toAddMonoidHom hΨ (mapH1 Φ.toAddMonoidHom hΦ (H1π G M f)) = H1π G M f
  rw [mapH1_H1π, mapH1_H1π, mapZ1_symm_comp Φ hΦ hΨ f]

/-- `mapH1` for `Φ.symm` is a right inverse of `mapH1` for `Φ`. -/
theorem mapH1_comp_symm (Φ : M ≃+ N)
    (hΦ : Work.GroupCohomology.IsEquivariant G Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant G Φ.symm.toAddMonoidHom) (x : H1 G N) :
    mapH1 Φ.toAddMonoidHom hΦ (mapH1 Φ.symm.toAddMonoidHom hΨ x) = x := by
  refine QuotientAddGroup.induction_on x ?_
  intro f
  change mapH1 Φ.toAddMonoidHom hΦ (mapH1 Φ.symm.toAddMonoidHom hΨ (H1π G N f)) = H1π G N f
  rw [mapH1_H1π, mapH1_H1π, mapZ1_comp_symm Φ hΦ hΨ f]

/-- An equivariant additive isomorphism of coefficients induces an additive equivalence
`H¹(G,M) ≃+ H¹(G,N)` on continuous cohomology. -/
noncomputable def h1AddEquiv (Φ : M ≃+ N)
    (hΦ : Work.GroupCohomology.IsEquivariant G Φ.toAddMonoidHom)
    (hΨ : Work.GroupCohomology.IsEquivariant G Φ.symm.toAddMonoidHom) :
    H1 G M ≃+ H1 G N :=
  AddMonoidHom.toAddEquiv (mapH1 Φ.toAddMonoidHom hΦ) (mapH1 Φ.symm.toAddMonoidHom hΨ)
    (AddMonoidHom.ext fun x => mapH1_symm_comp Φ hΦ hΨ x)
    (AddMonoidHom.ext fun x => mapH1_comp_symm Φ hΦ hΨ x)

end H1Equiv

theorem h1_equiv_of_equiv {G : Type} [Group G] [TopologicalSpace G] {M N : Type} [AddCommGroup M] [AddCommGroup N] [DistribMulAction G M] [DistribMulAction G N] (Φ : M ≃+ N) (h : ∀ (g : G) (m : M), Φ (g • m) = g • Φ m) : Nonempty (Work.AbsoluteKummer.H1 G M ≃+ Work.AbsoluteKummer.H1 G N) := by
  have hΦ : Work.GroupCohomology.IsEquivariant G Φ.toAddMonoidHom := fun g m => h g m
  have hΨ : Work.GroupCohomology.IsEquivariant G Φ.symm.toAddMonoidHom := by
    intro g n
    change Φ.symm (g • n) = g • Φ.symm n
    rw [AddEquiv.symm_apply_eq, h g (Φ.symm n), Φ.apply_symm_apply]
  exact ⟨H1Equiv.h1AddEquiv Φ hΦ hΨ⟩

end Work.SSGRoute
