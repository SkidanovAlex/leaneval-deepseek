import Mathlib

/-!
# A nontrivial element of the decomposition group acts by complex conjugation

Let `L / K` be a finite Galois extension of number fields, `w` a complex infinite place of `L`
lying over a real infinite place `v` of `K`.  Then `w` is *ramified* over `v` (this is precisely
the "complex place over a real place" situation), and the decomposition group of `w` contains a
nontrivial element: the complex conjugation with respect to the embedding `w.embedding`.

Concretely we construct `σ : Gal(L/K)` with `σ • w = w` and
`NumberField.ComplexEmbedding.IsConj w.embedding σ`, i.e. `w.embedding (σ x) = conj (w.embedding x)`
for all `x : L`; such a `σ` is necessarily nontrivial since `w` is complex.

The construction is the standard one: if `v` is real then the restriction of `w.embedding` to `K`
is fixed by complex conjugation, so `w.embedding` and `conjugate w.embedding` agree on `K`; by
Galois theory (`ComplexEmbedding.exists_comp_symm_eq_of_comp_eq`) there is `σ ∈ Gal(L/K)` with
`w.embedding.comp σ.symm = conjugate w.embedding`.  The corresponding place is unchanged because a
complex place remembers its defining embedding only up to conjugation.
-/

namespace NK.GlobalCFT.Galois

/-- The restriction of a complex embedding `w.embedding` to the base field is real, provided `w`
lies over a real place `v`. -/
theorem isReal_comp_algebraMap_of_isReal_liesOver {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K) [w.LiesOver v]
    (hv : v.IsReal) :
    NumberField.ComplexEmbedding.IsReal (w.embedding.comp (algebraMap K L)) := by
  have hmk : NumberField.InfinitePlace.mk (w.embedding.comp (algebraMap K L)) = v :=
    NumberField.InfinitePlace.LiesOver.mk_embedding_comp w v
  have h₁ : NumberField.ComplexEmbedding.IsReal
      (NumberField.InfinitePlace.embedding
        (NumberField.InfinitePlace.mk (w.embedding.comp (algebraMap K L)))) := by
    rw [hmk]
    exact NumberField.InfinitePlace.isReal_iff.mp hv
  rcases NumberField.InfinitePlace.embedding_mk_eq (w.embedding.comp (algebraMap K L)) with h | h
  · rwa [h] at h₁
  · rw [h] at h₁
    rwa [NumberField.ComplexEmbedding.isReal_conjugate_iff] at h₁

theorem exists_stabilizer_isConj_of_isReal_isComplex {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K) [w.LiesOver v]
    (hv : v.IsReal) (hw : w.IsComplex) :
    ∃ σ : L ≃ₐ[K] L, σ ≠ 1 ∧ σ • w = w ∧
      NumberField.ComplexEmbedding.IsConj w.embedding σ := by
  have hψreal := isReal_comp_algebraMap_of_isReal_liesOver w v hv
  have hreal : w.embedding.comp (algebraMap K L) =
      (NumberField.ComplexEmbedding.conjugate w.embedding).comp (algebraMap K L) := by
    rw [NumberField.ComplexEmbedding.conjugate_comp]
    exact (NumberField.ComplexEmbedding.isReal_iff.mp hψreal).symm
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := K) (K := L)
    w.embedding (NumberField.ComplexEmbedding.conjugate w.embedding) hreal
  have hconj : NumberField.ComplexEmbedding.IsConj w.embedding σ.symm := hσ.symm
  refine ⟨σ.symm, ?_, ?_, hconj⟩
  · exact (NumberField.ComplexEmbedding.isConj_ne_one_iff hconj).mpr
      (NumberField.InfinitePlace.isComplex_iff.mp hw)
  · have hkey : ∀ (f : L →+* L),
        w.comap f = NumberField.InfinitePlace.mk (w.embedding.comp f) := by
      intro f
      conv_lhs => rw [← NumberField.InfinitePlace.mk_embedding w]
      rw [NumberField.InfinitePlace.comap_mk]
    have hσconj : NumberField.ComplexEmbedding.IsConj w.embedding σ :=
      NumberField.ComplexEmbedding.IsConj.symm hconj
    rw [show σ.symm • w = w.comap σ from rfl, hkey σ, ← hσconj,
      NumberField.InfinitePlace.mk_conjugate_eq, NumberField.InfinitePlace.mk_embedding]

end NK.GlobalCFT.Galois
