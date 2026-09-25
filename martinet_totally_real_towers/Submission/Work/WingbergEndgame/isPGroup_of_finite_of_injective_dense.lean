import Mathlib
import Submission.Work.WingbergEndgame.Defs

/-!
# A finite group mapping injectively with dense image into `Gal(F_∞/F)` is a `2`-group

`Γ := Gal(F_∞/F)` is the wide maximal pro-`2` unramified extension of the number field `F`
(`Work.WingbergEndgame.UnramifiedProTwoExtension F`), topologised by the Krull topology
(`krullTopology`, an instance on `⇑E.K ≃ₐ[F] ⇑E.K`).

The Krull topology is Hausdorff (`krullTopology_t2`, available since a Galois extension of a field
is integral), so the image of a *finite* group `G` under a monoid hom `φ : G →* Γ` is a finite,
hence closed, subset of `Γ`.  If that image is moreover dense (`DenseRange φ`), it must be all of
`Γ`; injectivity then identifies `G` with `Γ`, so `Γ` is finite.

A Galois extension with finite Galois group is finite dimensional (`IsGalois.finiteDimensional_of_finite`),
so `E.K` is finite dimensional over `F` and we may apply the structure axiom

`UnramifiedProTwoExtension.proP : IsPGroup 2 (L ≃ₐ[F] L)`  for finite dimensional Galois
`L ⊆ E.K`,

at `L = ⊤`, and transport along `AlgEquiv.autCongr` (which identifies the automorphism group of
`↥⊤` with that of `E.K`) back to `Γ = E.K ≃ₐ[F] E.K`.  Finally `IsPGroup.of_injective` along `φ`
descends the `2`-group property to `G`.
-/

set_option linter.style.haveILetI false

namespace Work.WingbergEndgame

theorem isPGroup_of_finite_of_injective_dense {F : Type} [Field F] [NumberField F]
    (E : Work.WingbergEndgame.UnramifiedProTwoExtension F) {G : Type} [Group G]
    (φ : G →* Work.WingbergEndgame.galoisGroup E) (hinj : Function.Injective φ)
    (hdense : DenseRange φ) (hfin : Finite G) : IsPGroup 2 G := by
  haveI := hfin
  -- A finite subset of the Hausdorff space `Γ` is closed ...
  have hclosed : IsClosed (Set.range φ) := Set.Finite.isClosed (Set.finite_range φ)
  -- ... and a closed dense subset is everything, so `φ` is surjective.
  have hsurj : Function.Surjective φ := fun y => by
    have hy : y ∈ closure (Set.range φ) := hdense y
    rw [hclosed.closure_eq] at hy
    exact hy
  -- Hence `Γ` is finite, so `E.K/F` is a finite dimensional Galois extension.
  haveI : Finite (Work.WingbergEndgame.galoisGroup E) := Finite.of_surjective φ hsurj
  haveI : FiniteDimensional F E.K := IsGalois.finiteDimensional_of_finite F E.K
  -- The structure axiom at the top intermediate field.
  haveI : IsGalois F ↥(⊤ : IntermediateField F E.K) := isGalois_iff_isGalois_top.mpr E.galoisK
  haveI : NumberField E.K := NumberField.of_module_finite F E.K
  haveI : NumberField ↥(⊤ : IntermediateField F E.K) :=
    NumberField.of_subfield ((⊤ : IntermediateField F E.K).toSubfield)
  have htop : IsPGroup 2 (↥(⊤ : IntermediateField F E.K) ≃ₐ[F] ↥(⊤ : IntermediateField F E.K)) :=
    E.proP ⊤ inferInstance inferInstance
  -- Transport along `Gal(↥⊤/F) ≃* Gal(⇑E.K/F) = Γ`, then descend along `φ`.
  have hΓ : IsPGroup 2 (Work.WingbergEndgame.galoisGroup E) :=
    IsPGroup.of_equiv htop (AlgEquiv.autCongr (IntermediateField.topEquiv (F := F) (E := E.K)))
  exact IsPGroup.of_injective hΓ φ hinj

end Work.WingbergEndgame
