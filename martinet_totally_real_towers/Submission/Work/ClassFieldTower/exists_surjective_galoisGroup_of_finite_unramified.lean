import Mathlib
import Submission.Work.ClassFieldTower.Defs

set_option linter.style.haveILetI false

namespace Work.ClassFieldTower

/-- **Every finite unramified pro-`2` Galois extension of `F` is a quotient of `G_∅`.**

Let `F` be a number field and `M` the maximal unramified pro-`2` extension of `F`
(`Work.ClassFieldTower.MaximalUnramifiedProP F 2`).  If `L/F` is a finite Galois extension
which is unramified over `F` (`differentIdeal (𝓞 F) (𝓞 L) = ⊤`) and whose Galois group is a
`2`-group, then restriction of automorphisms along the embedding `L ↪ M.K` supplied by the
universal property of `M` exhibits `Gal(L/F)` as a quotient of `G_∅ = Gal(M.K/F)`.

Concretely, the universal property gives an `F`-embedding `ϕ : L →ₐ[F] M.K`; its image is a
normal (even Galois) subextension `E ⊆ M.K` isomorphic to `L`, and restriction
`Gal(M.K/F) →* Gal(E/F)` is surjective, while `Gal(E/F) ≃* Gal(L/F)` is induced by `ϕ`. -/
theorem exists_surjective_galoisGroup_of_finite_unramified {F : Type} [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) (L : Type) [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (hunr : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) = ⊤)
    (hpg : IsPGroup 2 (L ≃ₐ[F] L)) :
    ∃ φ : Work.ClassFieldTower.galoisGroup M →* (L ≃ₐ[F] L), Function.Surjective φ := by
  obtain ⟨ϕ, _⟩ := M.universal L hpg hunr
  let E : IntermediateField F M.K := ϕ.fieldRange
  haveI hNorE : Normal F ↥E := (IsGalois.of_algEquiv (ϕ.equivFieldRange)).to_normal
  haveI hNorK : Normal F M.K := (inferInstance : IsGalois F M.K).to_normal
  refine ⟨(AlgEquiv.autCongr (ϕ.equivFieldRange).symm).toMonoidHom.comp
      (AlgEquiv.restrictNormalHom ↥E), ?_⟩
  intro y
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := ↥E) (M.K)
    ((AlgEquiv.autCongr (ϕ.equivFieldRange).symm).symm y)
  refine ⟨σ, ?_⟩
  show (AlgEquiv.autCongr (ϕ.equivFieldRange).symm) ((AlgEquiv.restrictNormalHom ↥E) σ) = y
  rw [hσ]
  exact (AlgEquiv.autCongr (ϕ.equivFieldRange).symm).apply_symm_apply y

end Work.ClassFieldTower
