import Mathlib

namespace Work.ORBassSerre.Action.CoprodI

universe u

/-- The monoid homomorphism `CoprodI M →* CoprodI N` induced by a family of monoid isomorphisms
`M i ≃* N i`, constructed via the universal property of the coproduct. -/
noncomputable def coprodIMap {ι : Type u} {M N : ι → Type u} [∀ i, Group (M i)]
    [∀ i, Group (N i)] (e : ∀ i, M i ≃* N i) :
    Monoid.CoprodI M →* Monoid.CoprodI N :=
  Monoid.CoprodI.lift fun i =>
    (Monoid.CoprodI.of : N i →* Monoid.CoprodI N).comp (e i).toMonoidHom

theorem coprodIMap_of {ι : Type u} {M N : ι → Type u} [∀ i, Group (M i)] [∀ i, Group (N i)]
    (e : ∀ i, M i ≃* N i) (i : ι) (x : M i) :
    coprodIMap e (Monoid.CoprodI.of x) = Monoid.CoprodI.of (e i x) :=
  Monoid.CoprodI.lift_of (fun i =>
    (Monoid.CoprodI.of : N i →* Monoid.CoprodI N).comp (e i).toMonoidHom) x

theorem coprodIMap_comp {ι : Type u} {M N : ι → Type u} [∀ i, Group (M i)] [∀ i, Group (N i)]
    (e : ∀ i, M i ≃* N i) :
    (coprodIMap (fun i => (e i).symm)).comp (coprodIMap e) = MonoidHom.id (Monoid.CoprodI M) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  ext x
  simp [MonoidHom.comp_apply, coprodIMap_of]

theorem coprodIMap_comp' {ι : Type u} {M N : ι → Type u} [∀ i, Group (M i)] [∀ i, Group (N i)]
    (e : ∀ i, M i ≃* N i) :
    (coprodIMap e).comp (coprodIMap (fun i => (e i).symm)) = MonoidHom.id (Monoid.CoprodI N) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  ext x
  simp [MonoidHom.comp_apply, coprodIMap_of]

theorem coprodI_congr {ι : Type u} {M N : ι → Type u} [∀ i, Group (M i)] [∀ i, Group (N i)]
    (e : ∀ i, M i ≃* N i) :
    ∃ φ : Monoid.CoprodI M ≃* Monoid.CoprodI N,
      ∀ (i : ι) (x : M i), φ (Monoid.CoprodI.of x) = Monoid.CoprodI.of (e i x) := by
  refine ⟨MonoidHom.toMulEquiv (coprodIMap e) (coprodIMap fun i => (e i).symm)
    (coprodIMap_comp e) (coprodIMap_comp' e), ?_⟩
  intro i x
  exact coprodIMap_of e i x

end Work.ORBassSerre.Action.CoprodI
