import Mathlib
import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_ncard

namespace Work.Tower.Unramified

open NumberField

/-- **Complete splitting at the zero ideal characterises the trivial extension.**

The zero ideal of `𝓞 F` is not a nonzero prime, so "splits completely at `⊥`" is a very strong
condition: the only prime of `𝓞 L` lying over `⊥` is `⊥` itself (a nonzero ideal of `𝓞 L`
contracts to a nonzero ideal of `𝓞 F` by integrality), so an injective listing of
`[L : F]` primes over `⊥` forces `[L : F] = 1`.  Conversely, if `[L : F] = 1` then
`algebraMap F L` is bijective, the induced map on rings of integers is a ring isomorphism, and
the single prime `⊥` of `𝓞 L` over `⊥` with residue ring `(𝓞 L) ⧸ ⊥ ≃ (𝓞 F) ⧸ ⊥` witnesses
complete splitting. -/
theorem splitsCompletelyIn_bot_iff_finrank {F L : Type*} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] :
    Work.Tower.SplitsCompletelyIn F L ⊥ ↔ Module.finrank F L = 1 := by
  constructor
  · -- The only prime of `𝓞 L` over `⊥` is `⊥`, so an injective listing of `[L : F]` such
    -- primes forces `[L : F] ≤ 1`.
    rintro ⟨𝔔, hprime, hlies, hinj, -⟩
    have hbot : ∀ P : Ideal (𝓞 L), P.IsPrime → P.LiesOver (⊥ : Ideal (𝓞 F)) → P = ⊥ :=
      fun P _ hlie => Ideal.eq_bot_of_under_eq_bot hlie.over.symm
    have h𝔔 : ∀ i, 𝔔 i = ⊥ := fun i => hbot _ (hprime i) (hlies i)
    have hle1 : Module.finrank F L ≤ 1 := by
      have hsub : Subsingleton (Fin (Module.finrank F L)) :=
        ⟨fun i j => hinj (by rw [h𝔔 i, h𝔔 j])⟩
      simpa using (Fintype.card_le_one_iff_subsingleton.mpr hsub)
    exact le_antisymm hle1 Module.finrank_pos
  · -- If `[L : F] = 1`, then `F ≃ L` as `F`-algebras, so `𝓞 F ≃ 𝓞 L` as rings and the unique
    -- prime `⊥` of `𝓞 L` witnesses complete splitting.
    intro hfinL
    have hinjalg : Function.Injective (Algebra.ofId F L) :=
      RingHom.injective (Algebra.ofId F L).toRingHom
    have hrange : LinearMap.range (Algebra.ofId F L).toLinearMap = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        rw [LinearMap.finrank_range_of_inj hinjalg, Module.finrank_self, hfinL])
    have hsurjalg : Function.Surjective (Algebra.ofId F L) :=
      LinearMap.range_eq_top.mp hrange
    let e : F ≃ₐ[F] L := AlgEquiv.ofBijective (Algebra.ofId F L) ⟨hinjalg, hsurjalg⟩
    have eR : (𝓞 F) ≃+* (𝓞 L) := RingOfIntegers.mapRingEquiv e.toRingEquiv
    refine ⟨fun _ => (⊥ : Ideal (𝓞 L)), fun _ => Ideal.isPrime_bot, fun _ => ?_, ?_, fun _ => ?_⟩
    · exact ⟨by rw [Ideal.under_bot]⟩
    · intro i j _
      exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
    · exact ⟨Ideal.quotientEquiv (⊥ : Ideal (𝓞 L)) (⊥ : Ideal (𝓞 F)) eR.symm
        (Ideal.map_bot (f := (eR.symm : 𝓞 L →+* 𝓞 F))).symm⟩

end Work.Tower.Unramified
