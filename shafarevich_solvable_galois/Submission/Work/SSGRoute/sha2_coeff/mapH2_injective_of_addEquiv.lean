import Mathlib
import Submission.Work.AbsoluteKummer.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.sha2_coeff

open Work.AbsoluteKummer

/-- The composite of the coefficient maps `φ : M →+ N` and `φ.symm : N →+ M` acts on `2`-cocycles
`Z²(G,M)` as the identity: `mapZ2 φ.symm ∘ mapZ2 φ = id`. -/
theorem mapZ2_symm_comp {G : Type} [TopologicalSpace G] [Group G]
    {M N : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup N] [DistribMulAction G N]
    (φ : M ≃+ N) (hφ : Work.GroupCohomology.IsEquivariant G (φ : M →+ N))
    (hφ' : Work.GroupCohomology.IsEquivariant G (φ.symm : N →+ M)) (c : Z2 G M) :
    mapZ2 (φ.symm : N →+ M) hφ' (mapZ2 (φ : M →+ N) hφ c) = c := by
  refine Subtype.ext (funext fun p => ?_)
  simp [mapZ2_apply]

/-- **A left inverse for `mapH2 φ`.**  If `φ : M ≃+ N` is an additive equivalence of discrete
`G`-modules whose inverse is again equivariant, then `mapH2 φ.symm` is a left inverse of
`mapH2 φ`. -/
theorem mapH2_symm_comp {G : Type} [TopologicalSpace G] [Group G]
    {M N : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup N] [DistribMulAction G N]
    (φ : M ≃+ N) (hφ : Work.GroupCohomology.IsEquivariant G (φ : M →+ N))
    (hφ' : Work.GroupCohomology.IsEquivariant G (φ.symm : N →+ M)) (x : H2 G M) :
    mapH2 (G := G) (φ.symm : N →+ M) hφ' (mapH2 (G := G) (φ : M →+ N) hφ x) = x := by
  obtain ⟨c, hc⟩ :=
    QuotientAddGroup.mk'_surjective ((B2 G M).comap (Z2 G M).subtype) x
  rw [← hc]
  show mapH2 (G := G) (φ.symm : N →+ M) hφ'
      (mapH2 (G := G) (φ : M →+ N) hφ (H2π G M c)) = H2π G M c
  rw [mapH2_H2π, mapH2_H2π, mapZ2_symm_comp φ hφ hφ' c]

theorem mapH2_injective_of_addEquiv {G : Type} [TopologicalSpace G] [Group G]
    {M N : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup N] [DistribMulAction G N]
    (φ : M ≃+ N) (hφ : Work.GroupCohomology.IsEquivariant G (φ : M →+ N))
    (hφ' : Work.GroupCohomology.IsEquivariant G (φ.symm : N →+ M)) :
    Function.Injective (Work.AbsoluteKummer.mapH2 (G := G) (φ : M →+ N) hφ) := by
  intro x y hxy
  have h := congrArg (mapH2 (G := G) (φ.symm : N →+ M) hφ') hxy
  rw [mapH2_symm_comp φ hφ hφ' x, mapH2_symm_comp φ hφ hφ' y] at h
  exact h

end Work.SSGRoute.sha2_coeff
