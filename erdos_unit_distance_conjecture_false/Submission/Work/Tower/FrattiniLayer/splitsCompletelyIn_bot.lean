import Mathlib
import Submission.Work.Tower.Defs

/-!
# Complete splitting at the zero ideal

The zero ideal of `𝓞 F` is not a maximal (or even nonzero) ideal, and complete splitting
at it is therefore a very strong condition: the only prime of `𝓞 L` lying over `⊥` is `⊥`
itself, so `SplitsCompletelyIn F L ⊥` forces `[L : F] = 1`.  Consequently complete
splitting at `⊥` is preserved by *any* injective `F`-algebra map, in particular by
`L' →ₐ[F] L`: both fields are then one-dimensional over `F`.
-/

namespace Work.Tower.FrattiniLayer

open NumberField

theorem splitsCompletelyIn_bot {F L L' : Type*} [Field F] [NumberField F] [Field L]
    [NumberField L] [Field L'] [NumberField L'] [Algebra F L] [Algebra F L']
    [FiniteDimensional F L] [FiniteDimensional F L'] (φ : L' →ₐ[F] L)
    (h : Work.Tower.SplitsCompletelyIn F L (⊥ : Ideal (NumberField.RingOfIntegers F))) :
    Work.Tower.SplitsCompletelyIn F L' (⊥ : Ideal (NumberField.RingOfIntegers F)) := by
  obtain ⟨𝔔, hprime, hlies, hinj, -⟩ := h
  -- The only prime of `𝓞 L` lying over the zero ideal of `𝓞 F` is `⊥`: `𝓞 L` is integral over
  -- `𝓞 F`, and a nonzero ideal never contracts to `⊥` under an integral extension.
  have hbot : ∀ P : Ideal (𝓞 L), P.IsPrime → P.LiesOver (⊥ : Ideal (𝓞 F)) → P = ⊥ :=
    fun P _ hlie => Ideal.eq_bot_of_under_eq_bot (Ideal.over_def P (⊥ : Ideal (𝓞 F))).symm
  have h𝔔 : ∀ i, 𝔔 i = ⊥ := fun i => hbot _ (hprime i) (hlies i)
  -- Injectivity of `𝔔` therefore forces `[L : F] ≤ 1`, hence `[L : F] = 1`.
  have hle1 : Module.finrank F L ≤ 1 := by
    have hsub : Subsingleton (Fin (Module.finrank F L)) :=
      ⟨fun i j => hinj (by rw [h𝔔 i, h𝔔 j])⟩
    simpa using (Fintype.card_le_one_iff_subsingleton.mpr hsub)
  have hfinL : Module.finrank F L = 1 := le_antisymm hle1 Module.finrank_pos
  -- An injective `F`-algebra map `L' → L` then forces `[L' : F] = 1` as well.
  have hinjφ : Function.Injective φ.toLinearMap :=
    fun a b hab => RingHom.injective φ.toRingHom hab
  have hle : Module.finrank F L' ≤ Module.finrank F L :=
    LinearMap.finrank_le_finrank_of_injective hinjφ
  have hfinL' : Module.finrank F L' = 1 := le_antisymm (hfinL ▸ hle) Module.finrank_pos
  -- Consequently `algebraMap F L'` is bijective, i.e. `F ≃ L'`.
  have hinjalg : Function.Injective (Algebra.ofId F L') :=
    RingHom.injective (Algebra.ofId F L').toRingHom
  have hrange : LinearMap.range (Algebra.ofId F L').toLinearMap = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by
      rw [LinearMap.finrank_range_of_inj hinjalg, Module.finrank_self, hfinL'])
  have hsurjalg : Function.Surjective (Algebra.ofId F L') :=
    LinearMap.range_eq_top.mp hrange
  let e : F ≃ₐ[F] L' := AlgEquiv.ofBijective (Algebra.ofId F L') ⟨hinjalg, hsurjalg⟩
  -- which induces a ring isomorphism of the rings of integers.
  have eR : (𝓞 F) ≃+* (𝓞 L') := RingOfIntegers.mapRingEquiv e.toRingEquiv
  -- Now exhibit the (unique) prime `⊥` of `𝓞 L'` over `⊥`.
  refine ⟨fun _ => (⊥ : Ideal (𝓞 L')), fun i => Ideal.isPrime_bot, fun i => ?_, ?_,
    fun i => ?_⟩
  · exact ⟨by rw [Ideal.under_bot]⟩
  · intro i j _
    exact Fin.ext (by have := i.isLt; have := j.isLt; omega)
  · exact ⟨Ideal.quotientEquiv (⊥ : Ideal (𝓞 L')) (⊥ : Ideal (𝓞 F)) eR.symm
      (Ideal.map_bot (f := (eR.symm : 𝓞 L' →+* 𝓞 F))).symm⟩

end Work.Tower.FrattiniLayer
