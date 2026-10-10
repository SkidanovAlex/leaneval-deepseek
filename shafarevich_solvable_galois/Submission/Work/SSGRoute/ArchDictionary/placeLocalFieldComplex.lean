import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.Work.SSGRoute.SSGStage.archimedeanLocalDictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The completion at a linked archimedean place with *nontrivial* decomposition group is `ℂ`

Companion of `Work.SSGRoute.ArchDictionary_aux.place_localField_equiv_real_of_decompK_eq_bot`
(the `decompK w = ⊥` case): here the decomposition group of the infinite place `w` is nontrivial,
which forces `w` to be a *complex* place, and the completion of `K` at `w` is `ℂ`, compatibly with
the embedding `φ` used to define the place.

This is the "spelling" input of the archimedean comparison square at the complex place: it
identifies the local field with `ℂ` through `φ`, so that the local `D_w`-action on `K_wˣ` is
complex conjugation (`E1aClean.ArchSeam.linkedLocalAction_eq_conj`).
-/

namespace Work.SSGRoute.ArchDictionary

open NumberField

/-- **The completion of `K` at a linked complex place is `ℂ`, compatibly with `φ`.**

Let `c ≠ 1` be an involution of `Gal(Ω/k)` which is the complex conjugation for the embedding
`φ : Ω →+* ℂ` (`hlink`), and let `w` be the infinite place of `K` induced by `φ ∘ (K ↪ Ω)`.  If
the decomposition group of `w` is nontrivial, then `w` is a complex place and there is a ring
isomorphism `K_w ≃+* ℂ` carrying the canonical embedding of `K` into `K_w` to `φ`. -/
theorem place_localField_equiv_complex_of_decompK_ne_bot (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    ∃ e : NK.GlobalCFT.Place.localField ↥K w ≃+* ℂ,
      ∀ x : ↥K, e (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K w) x) = φ (algebraMap ↥K Ω x) := by
  classical
  set ψ : ↥K →+* ℂ := φ.comp (algebraMap ↥K Ω) with hψ
  set v : NumberField.InfinitePlace ↥K := NumberField.InfinitePlace.mk ψ with hv
  have hwv : w = NK.GlobalCFT.Place.ofInfinite v := by rw [hw, hv]
  -- `w` is a complex place
  have hvC : v.IsComplex := by
    refine Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := ↥K) ?_
    rw [← hwv]
    exact hne
  -- the completion iso and its value on `K`
  have hcoe : ∀ x : ↥K,
      NumberField.InfinitePlace.Completion.extensionEmbedding v
        (algebraMap ↥K v.Completion x) = v.embedding x := by
    intro x
    simp [NumberField.InfinitePlace.Completion.algebraMap_apply,
      NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
  -- the chosen embedding of the place is `ψ` or its conjugate
  have hemb : v.embedding = ψ ∨ v.embedding = NumberField.ComplexEmbedding.conjugate ψ := by
    have := NumberField.InfinitePlace.embedding_mk_eq ψ
    rw [hv]
    exact this
  rw [hwv]
  rcases hemb with hemb | hemb
  · refine ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC, fun x => ?_⟩
    rw [NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply, hcoe x, hemb]
    rfl
  · refine ⟨(NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC).trans
      Complex.conjAe, fun x => ?_⟩
    rw [RingEquiv.trans_apply, NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
      hcoe x, hemb]
    simp [NumberField.ComplexEmbedding.conjugate, Complex.conjAe, hψ]

/-- **The units of `K` sit in `K_wˣ = ℂˣ` through `φ`.**

Units-level companion of `place_localField_equiv_complex_of_decompK_ne_bot`: the canonical map
`Kˣ → K_wˣ` (`NK.HassePrinciple.unitsToLocalUnitsHom`) composed with the spelling isomorphism is the
embedding `Kˣ → ℂˣ` induced by `φ`. -/
theorem unitsToLocalUnitsHom_eq_embedding (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    ∃ e : NK.GlobalCFT.Place.localField ↥K w ≃+* ℂ,
      ∀ x : (↥K)ˣ, e (Units.val (NK.HassePrinciple.unitsToLocalUnitsHom w x))
        = φ (algebraMap ↥K Ω (Units.val x)) := by
  obtain ⟨e, he⟩ := place_localField_equiv_complex_of_decompK_ne_bot p k Ω K c hc2 hc1 φ hlink
    w hw hne
  exact ⟨e, fun x => by
    show e (algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K w) (Units.val x))
      = φ (algebraMap ↥K Ω (Units.val x))
    exact he (Units.val x)⟩

end Work.SSGRoute.ArchDictionary
