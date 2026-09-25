import Mathlib
import Submission.NK.GlobalCFT.Galois.completionMap_isometry

/-!
# The completion map is surjective over a complex place

If `w` is an infinite place of a number field `L` lying over a *complex* infinite place `v` of a
number field `K`, then the completion map `K_v →+* L_w` induced by the inclusion `K → L` is
surjective.

Mathematically, a complex place `v` has completion `K_v ≃ ℂ` (via the extension embedding
`K_v →+* ℂ`, which is bijective because its image is a closed subfield of `ℂ` different from `ℝ`),
and `L_w` is either `ℝ` or `ℂ`; a field homomorphism `ℂ → ℝ` cannot exist.  Formally, the argument
is entirely carried by the *complex* extension embeddings: since `w` lies over `v`, the two
embeddings `extensionEmbedding w ∘ completionMap` and `extensionEmbedding v` are either equal or
conjugate (this is `LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq` together with the
density argument in `Completion.liesOver_extensionEmbedding` /
`Completion.liesOver_conjugate_extensionEmbedding`).  The composite `extensionEmbedding w ∘
completionMap`, being `id` or `star` after `extensionEmbedding v`, is surjective, and
`extensionEmbedding w` is injective, whence `completionMap` is surjective.
-/

open scoped NumberField.LiesOver
open NumberField

namespace NK.GlobalCFT.Galois

/-- If `φ ∘ f = θ ∘ ψ` with `θ` and `ψ` surjective and `φ` injective, then `f` is surjective.  (A
field homomorphism out of a field is injective.) -/
private lemma surjective_of_comp_eq {A B : Type*} [Field A] [Field B]
    (f : A →+* B) (φ : B →+* ℂ) (ψ : A →+* ℂ) (θ : ℂ →+* ℂ)
    (hθ : Function.Surjective θ) (hψ : Function.Surjective ψ)
    (h : φ.comp f = θ.comp ψ) : Function.Surjective f := by
  intro y
  obtain ⟨c, hc⟩ := hθ (φ y)
  obtain ⟨x, hx⟩ := hψ c
  refine ⟨x, φ.injective ?_⟩
  rw [← RingHom.comp_apply, h, RingHom.comp_apply, hx, hc]

theorem completionMap_surjective_of_isComplex_under {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {v : NumberField.InfinitePlace K}
    {w : NumberField.InfinitePlace L} [w.LiesOver v] (hv : v.IsComplex) :
    Function.Surjective (NumberField.LiesOver.completionMap (v := v) (w := w)) := by
  have hψ : Function.Surjective (NumberField.InfinitePlace.Completion.extensionEmbedding v) :=
    NumberField.InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hv
  rcases NumberField.InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v
    with h | h
  · -- `w.embedding` extends `v.embedding`: the completion map is compatible with the identity
    -- extension embedding of `ℂ`.
    have : NumberField.ComplexEmbedding.LiesOver w.embedding v.embedding := ⟨h⟩
    have : NumberField.ComplexEmbedding.LiesOver
        (NumberField.InfinitePlace.Completion.extensionEmbedding w)
        (NumberField.InfinitePlace.Completion.extensionEmbedding v) :=
      NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding w v
    refine surjective_of_comp_eq (NumberField.LiesOver.completionMap (v := v) (w := w))
      (NumberField.InfinitePlace.Completion.extensionEmbedding w)
      (NumberField.InfinitePlace.Completion.extensionEmbedding v)
      (RingHom.id ℂ) Function.surjective_id hψ ?_
    ext x
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.id_apply]
    have hov := NumberField.ComplexEmbedding.LiesOver.over_apply
      (NumberField.InfinitePlace.Completion.extensionEmbedding w)
      (NumberField.InfinitePlace.Completion.extensionEmbedding v) (x := x)
    simpa [RingHom.algebraMap_toAlgebra] using hov
  · -- `conjugate w.embedding` extends `v.embedding`: the completion map is compatible with
    -- complex conjugation composed with the extension embedding.
    have : NumberField.ComplexEmbedding.LiesOver
        (NumberField.ComplexEmbedding.conjugate w.embedding) v.embedding := ⟨h⟩
    have : NumberField.ComplexEmbedding.LiesOver
        (NumberField.ComplexEmbedding.conjugate
          (NumberField.InfinitePlace.Completion.extensionEmbedding w))
        (NumberField.InfinitePlace.Completion.extensionEmbedding v) :=
      NumberField.InfinitePlace.Completion.liesOver_conjugate_extensionEmbedding w v
    refine surjective_of_comp_eq (NumberField.LiesOver.completionMap (v := v) (w := w))
      (NumberField.InfinitePlace.Completion.extensionEmbedding w)
      (NumberField.InfinitePlace.Completion.extensionEmbedding v)
      (starRingEnd ℂ) (Function.Involutive.surjective fun z => Complex.conj_conj z) hψ ?_
    ext x
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have h2 : NumberField.InfinitePlace.Completion.extensionEmbedding w
        (algebraMap v.Completion w.Completion x) = (starRingEnd ℂ)
          (NumberField.InfinitePlace.Completion.extensionEmbedding v x) := by
      have hov := NumberField.ComplexEmbedding.LiesOver.over_apply
        (NumberField.ComplexEmbedding.conjugate
          (NumberField.InfinitePlace.Completion.extensionEmbedding w))
        (NumberField.InfinitePlace.Completion.extensionEmbedding v) (x := x)
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq] at hov
      have := congrArg (starRingEnd ℂ) hov
      simpa using this
    simpa [RingHom.algebraMap_toAlgebra] using h2

end NK.GlobalCFT.Galois
