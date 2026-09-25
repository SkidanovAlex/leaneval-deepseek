import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.exists_surjective_galoisGroup_of_finite_unramified

set_option linter.style.haveILetI false

namespace Work.ClassFieldTower

/-- **The universal property of `F_∅` in quotient form**: every finite unramified pro-`2` Galois
extension `L/F` is a quotient of `G_∅ = Gal(F_∅/F)`.  This is the *provable* half of
`Work.ClassFieldTower.DescribesMaximalProTwo` for the genuine group `G_∅` (the other half, that
every finite `2`-quotient of the abstract model is realized, is a hypothesis of the arithmetic
interface).

Proof strategy: the universal property `M.universal` gives an `F`-embedding `φ : L →ₐ[F] M.K`
(the hypotheses `IsPGroup 2 (L ≃ₐ[F] L)` and `differentIdeal = ⊤` are stated for `L`; the image
`φ.fieldRange` is a finite dimensional Galois subfield of `M.K` and the corresponding data is
transported along `AlgEquiv.ofInjectiveField φ`); `AlgEquiv.restrictNormalHom` then exhibits
`Gal(φ.fieldRange/F) ≃* G_∅ ⧸ ker`, with `ker` normal, of finite index and with `2`-group
quotient.  Cf. `Work.ClassFieldTower.exists_quotient_equiv_finite_galois_subfield`, which does
the same for subfields of `F_∅` directly, and
`Work.ClassFieldTower.exists_surjective_galoisGroup_of_finite_unramified` for the surjection
form. -/
theorem describesMaximalProTwo_second_galoisGroup {F : Type} [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) :
    ∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L],
      differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers L) = ⊤ →
      IsPGroup 2 (L ≃ₐ[F] L) →
      ∃ (N : Subgroup (Work.ClassFieldTower.galoisGroup M)) (_ : N.Normal),
        Finite (Work.ClassFieldTower.galoisGroup M ⧸ N) ∧
        IsPGroup 2 (Work.ClassFieldTower.galoisGroup M ⧸ N) ∧
        Nonempty ((Work.ClassFieldTower.galoisGroup M ⧸ N) ≃* (L ≃ₐ[F] L)) := by
  intro L _ _ _ hfd _ hunr hpg
  classical
  -- the universal property of `F_∅` exhibits `Gal(L/F)` as a quotient of `G_∅`
  obtain ⟨φ, hφ⟩ := exists_surjective_galoisGroup_of_finite_unramified M L hunr hpg
  -- `L` is finite dimensional over `F`, so its automorphism group is finite
  haveI : Finite (L ≃ₐ[F] L) := Finite.of_fintype _
  refine ⟨φ.ker, MonoidHom.normal_ker φ, ?_, ?_,
    ⟨QuotientGroup.quotientKerEquivOfSurjective φ hφ⟩⟩
  · -- finiteness is transported along the quotient isomorphism
    exact Finite.of_equiv (L ≃ₐ[F] L)
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toEquiv
  · -- `2`-group-ness is transported along the quotient isomorphism
    exact IsPGroup.of_injective hpg
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toMonoidHom
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).injective

end Work.ClassFieldTower
