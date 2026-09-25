import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.GaloisIdeles
import Submission.NK.GlobalCFT.LocalInputs

/-!
# The local fixed point lemma at an archimedean place

For a finite Galois extension of number fields `L / K` and an archimedean place `w` of `L` lying
over `v` of `K`, a unit `y` of the local field `L_w` which is fixed by the whole decomposition
group of `w` (acting through the canonical local isomorphisms `Place.localRingEquiv`) is the image
of a unit of the local field `K_v` under the canonical local embedding
`Place.localAlgebraMapUnits`.

This is the archimedean half of the fixed point computation for the idèle class group; the
nonarchimedean half is `NK.GlobalCFT.Galois.globalCFT_localFixed_finite`.

## The mathematics

The local field `L_w` is `ℝ` or `ℂ`, and `K_v` is `ℝ` or `ℂ`, with `K_v ⊆ L_w`.  There are three
cases:

* `w` is real: then `v` is real and the extension `L_w/K_v = ℝ/ℝ` is trivial, so the local
  embedding is bijective (`InfinitePlace.IsUnramified.finrank_eq_one`).
* `v` is complex: then `w` is complex and `L_w/K_v = ℂ/ℂ` is again trivial (same lemma), the place
  `w` being unramified because its restriction `v` is complex.
* `v` is real and `w` is complex: then `L_w = ℂ`, `K_v = ℝ` and the fixed units are the units of
  `ℝ`.  Here the mathematics is genuinely local-Galois: some `σ ∈ Gal(L/K)` fixes `w` and acts on
  `L_w = ℂ` by complex conjugation (`exists_conj_aut`, built from
  `InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq` and
  `ComplexEmbedding.exists_comp_symm_eq_of_comp_eq`), so the fixed field of the local action is
  the image of `K_v = ℝ`.  This is where the hypothesis `hy` is used.

## Main results

* `NK.GlobalCFT.Galois.globalCFT_localFixed_infinite`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open NK.GlobalCFT NumberField

open scoped NumberField.LiesOver

noncomputable section

namespace NK.GlobalCFT.Galois

/-! ### Transport along an equality of places

The local field `L_v` is defined by a `match` on the place `v`, so the transport of an element
along an equality of places has to be handled explicitly.  The following two elementary lemmas
record that this transport commutes with the canonical embeddings of `L` (via the extension
embeddings to `ℂ`) and with the underlying element of a unit. -/

section Transport

variable {L : Type*} [Field L] [NumberField L]

/-- Transporting a value of a local field along an equality of places, tested against an arbitrary
function of the local fields. -/
lemma localField_eqRec_apply (f : ∀ p : Place L, Place.localField L p → ℂ) {a b : Place L}
    (h : a = b) (x : Place.localField L a) : f b (h ▸ x) = f a x := by
  cases h; rfl

/-- Transporting a unit of a local field along an equality of places commutes with taking the
underlying element. -/
lemma localField_units_eqRec_val {a b : Place L} (h : a = b) (u : (Place.localField L a)ˣ) :
    ((h ▸ u : (Place.localField L b)ˣ) : Place.localField L b)
      = h ▸ (u : Place.localField L a) := by
  cases h; rfl

end Transport

/-! ### The extension embeddings evaluated on `L` -/

section Embeddings

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The extension embedding `L_w →+* ℂ` evaluated on the image of `L`. -/
lemma extensionEmbedding_algebraMap (w : InfinitePlace L) (x : L) :
    InfinitePlace.Completion.extensionEmbedding w (algebraMap L w.Completion x)
      = w.embedding x := by
  rw [InfinitePlace.Completion.algebraMap_apply,
    InfinitePlace.Completion.extensionEmbedding_coe]
  simp

/-- The real extension embedding `L_w →+* ℝ` evaluated on the image of `L`, for a real place. -/
lemma extensionEmbeddingOfIsReal_algebraMap {w : InfinitePlace L} (hw : w.IsReal) (x : L) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (algebraMap L w.Completion x)
      = InfinitePlace.embedding_of_isReal hw x := by
  rw [InfinitePlace.Completion.algebraMap_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  simp

/-- If `v` is a real place, the local algebra map `K_v →+* L_w` is compatible with the extension
embeddings into `ℂ`. -/
lemma completionMap_extensionEmbedding {w : InfinitePlace L} {v : InfinitePlace K}
    [w.LiesOver v] (hv : v.IsReal) (a : v.Completion) :
    InfinitePlace.Completion.extensionEmbedding w
        (NumberField.LiesOver.completionMap (v := v) (w := w) a)
      = InfinitePlace.Completion.extensionEmbedding v a := by
  have h := (NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv).over
  have h2 : ⇑(algebraMap v.Completion w.Completion)
      = ⇑(NumberField.LiesOver.completionMap (v := v) (w := w)) := by
    rw [RingHom.algebraMap_toAlgebra]
  simpa [RingHom.comp_apply, h2] using congrFun (congrArg DFunLike.coe h) a

/-- The local algebra map at an infinite place is the units map of the completion map. -/
lemma localAlgebraMapUnits_ofInfinite_eq {w : InfinitePlace L} {v : InfinitePlace K}
    (h : w.LiesOver v) :
    Place.localAlgebraMapUnits (Place.ofInfinite w) (Place.ofInfinite v)
        (Place.liesOver_ofInfinite h)
      = Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom := by
  haveI := h
  simp only [Place.localAlgebraMapUnits]
  rw [dif_pos (show w.LiesOver v from inferInstance)]

end Embeddings

/-! ### The unramified case: the local algebra map is surjective -/

section Unramified

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- At an unramified archimedean place the local algebra map is surjective: the local extension has
degree one. -/
lemma completionMap_surjective_of_isUnramified {w : InfinitePlace L} {v : InfinitePlace K}
    [w.LiesOver v] (hunram : w.IsUnramified K) :
    ∀ x : w.Completion, ∃ a : v.Completion,
      NumberField.LiesOver.completionMap (v := v) (w := w) a = x := by
  have hfr : Module.finrank v.Completion w.Completion = 1 :=
    NumberField.InfinitePlace.IsUnramified.finrank_eq_one v hunram
  have htop : (⊤ : IntermediateField v.Completion w.Completion) = ⊥ := by
    rw [← IntermediateField.finrank_eq_one_iff, IntermediateField.finrank_top']
    exact hfr
  intro x
  have hx : x ∈ (⊥ : IntermediateField v.Completion w.Completion) := by
    rw [← htop]; exact IntermediateField.mem_top
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hx
  refine ⟨a, ?_⟩
  rw [RingHom.algebraMap_toAlgebra] at ha
  exact ha

end Unramified

/-! ### The ramified case: an element of the decomposition group acting by conjugation -/

section Conjugation

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {w : InfinitePlace L} {v : InfinitePlace K} [w.LiesOver v]

/-- If `w` is a complex place of `L` above a real place `v` of `K`, then some `K`-automorphism
of `L` fixes `w` and acts on `L` by complex conjugation with respect to the embedding `w.embedding`
(equivalently, acts on the local field `L_w = ℂ` by complex conjugation). -/
lemma exists_conj_aut (hwC : w.IsComplex) (hvR : v.IsReal) :
    ∃ σ : L ≃ₐ[K] L, σ • w = w ∧ ∀ x : L, w.embedding (σ x) = (starRingEnd ℂ) (w.embedding x) := by
  have hconjv : ComplexEmbedding.conjugate v.embedding = v.embedding :=
    ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hvR)
  have H : (ComplexEmbedding.conjugate w.embedding).comp (algebraMap K L)
      = w.embedding.comp (algebraMap K L) := by
    rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with h | h
    · rw [ComplexEmbedding.conjugate_comp, h, hconjv, ← h]
    · rw [h]
      have hkey : w.embedding.comp (algebraMap K L)
          = ComplexEmbedding.conjugate
              ((ComplexEmbedding.conjugate w.embedding).comp (algebraMap K L)) := by
        rw [← ComplexEmbedding.conjugate_comp]
        ext x
        simp
      rw [hkey, h, hconjv]
  obtain ⟨ν, hν⟩ := InfinitePlace.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
      (ComplexEmbedding.conjugate w.embedding) w.embedding H
  have hemb' : ∀ x : L, w.embedding (ν x) = (starRingEnd ℂ) (w.embedding x) := by
    intro x
    have h := RingHom.congr_fun hν (ν x)
    rw [RingHom.comp_apply] at h
    rw [show (↑ν.symm : L →+* L) (ν x) = x from AlgEquiv.symm_apply_apply ν x] at h
    simpa [ComplexEmbedding.conjugate, RingHom.star_apply] using h.symm
  have hemb : ∀ x : L, w.embedding (ν.symm x) = (starRingEnd ℂ) (w.embedding x) := by
    intro x
    have hx := congrArg (starRingEnd ℂ) (hemb' (ν.symm x))
    simpa using hx.symm
  refine ⟨ν.symm, ?_, hemb⟩
  have hcomp : w.embedding.comp (↑ν : L →+* L)
      = ComplexEmbedding.conjugate w.embedding := by
    ext x
    simpa [ComplexEmbedding.conjugate, RingHom.star_apply] using hemb' x
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.smul_mk, AlgEquiv.symm_symm, hcomp]
  exact InfinitePlace.mk_conjugate_eq w.embedding

end Conjugation

/-! ### The fixed points of the local action in the ramified archimedean case -/

section Fixed

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {w : InfinitePlace L} {v : InfinitePlace K} [w.LiesOver v]

/-- **The local action is conjugation.**  If `σ` fixes the complex place `w` and acts on `L` by
complex conjugation with respect to `w.embedding`, then the canonical local isomorphism
`L_w ≃+* L_{σ w}` (identified with an automorphism of `L_w` through `σ • w = w`) intertwines the
extension embedding of `L_w` with complex conjugation. -/
lemma extensionEmbedding_infiniteCongrEquiv_conj (σ : L ≃ₐ[K] L) (hσw : σ • w = w)
    (hemb : ∀ x : L, w.embedding (σ x) = (starRingEnd ℂ) (w.embedding x)) :
    ∀ z : w.Completion,
      InfinitePlace.Completion.extensionEmbedding (σ • w)
          (globalCFT_infiniteCongrEquiv σ w z)
        = (starRingEnd ℂ) (InfinitePlace.Completion.extensionEmbedding w z) := by
  intro z
  have hd : DenseRange (⇑(algebraMap L w.Completion)) :=
    denseRange_algebraMap_localField (Place.ofInfinite w)
  have hcont1 : Continuous (fun y : w.Completion =>
      InfinitePlace.Completion.extensionEmbedding (σ • w)
        (globalCFT_infiniteCongrEquiv σ w y)) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding (σ • w)).continuous.comp
      (continuous_localRingEquiv σ (Place.ofInfinite w))
  have hcont2 : Continuous (fun y : w.Completion =>
      (starRingEnd ℂ) (InfinitePlace.Completion.extensionEmbedding w y)) :=
    Complex.continuous_conj.comp
      (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  have key : (fun y : w.Completion => InfinitePlace.Completion.extensionEmbedding (σ • w)
        (globalCFT_infiniteCongrEquiv σ w y))
      = (fun y : w.Completion => (starRingEnd ℂ)
        (InfinitePlace.Completion.extensionEmbedding w y)) := by
    apply DenseRange.equalizer (f := ⇑(algebraMap L w.Completion)) hd hcont1 hcont2
    funext x
    simp only [Function.comp_apply]
    rw [globalCFT_infiniteCongrEquiv_algebraMap]
    rw [show InfinitePlace.Completion.extensionEmbedding (σ • w)
          (algebraMap L (σ • w).Completion (σ x)) = (σ • w).embedding (σ x) from
        extensionEmbedding_algebraMap (σ • w) (σ x),
      show InfinitePlace.Completion.extensionEmbedding w
          (algebraMap L w.Completion x) = w.embedding x from
        extensionEmbedding_algebraMap w x,
      congrArg InfinitePlace.embedding hσw]
    exact hemb x
  exact congrFun key z

/-- **The fixed points are the units of `K_v` in the ramified archimedean case.**  If `w` is a
complex place above a real place `v` and the unit `y` of `L_w = ℂ` is fixed by the local action of
the decomposition group of `w`, then `y` is fixed by complex conjugation (through the extension
embedding). -/
lemma star_extensionEmbedding_eq_of_fixed (hwC : w.IsComplex) (hvR : v.IsReal)
    (y : w.Completionˣ)
    (hy : ∀ σ : L ≃ₐ[K] L, ∀ (hσ : σ • Place.ofInfinite w = Place.ofInfinite w),
      Units.map (Place.localRingEquiv σ (Place.ofInfinite w)).toMonoidHom y = hσ.symm ▸ y) :
    (starRingEnd ℂ) (InfinitePlace.Completion.extensionEmbedding w (y : w.Completion))
      = InfinitePlace.Completion.extensionEmbedding w (y : w.Completion) := by
  obtain ⟨σ, hσw, hemb⟩ := exists_conj_aut hwC hvR
  have hconj := extensionEmbedding_infiniteCongrEquiv_conj σ hσw hemb
  let f : ∀ p : Place L, Place.localField L p → ℂ := fun p => match p with
    | Sum.inl w' => InfinitePlace.Completion.extensionEmbedding w'
    | Sum.inr _ => fun _ => 0
  have htr := localField_eqRec_apply f (congrArg Place.ofInfinite hσw).symm (y : w.Completion)
  have h1 := congrArg Units.val (hy σ (congrArg Place.ofInfinite hσw))
  simp only [Units.coe_map, Place.localRingEquiv] at h1
  rw [localField_units_eqRec_val] at h1
  have key : InfinitePlace.Completion.extensionEmbedding (σ • w)
      ((globalCFT_infiniteCongrEquiv σ w).toMonoidHom (y : w.Completion))
      = InfinitePlace.Completion.extensionEmbedding w (y : w.Completion) := by
    rw [h1]
    exact htr
  exact (hconj (y : w.Completion)).symm.trans key

end Fixed

/-! ### The main lemma -/

theorem globalCFT_localFixed_infinite {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {w : NumberField.InfinitePlace L} {v : NumberField.InfinitePlace K} (h : w.LiesOver v)
    (y : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite w))ˣ)
    (hy : ∀ σ : L ≃ₐ[K] L,
      ∀ (hσ : σ • NK.GlobalCFT.Place.ofInfinite w = NK.GlobalCFT.Place.ofInfinite w),
      Units.map (NK.GlobalCFT.Place.localRingEquiv σ
        (NK.GlobalCFT.Place.ofInfinite w)).toMonoidHom y = hσ.symm ▸ y) :
    ∃ a : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite v))ˣ,
      NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite w)
        (NK.GlobalCFT.Place.ofInfinite v)
        (NK.GlobalCFT.Place.liesOver_ofInfinite h) a = y := by
  haveI hLies : w.LiesOver v := h
  rw [localAlgebraMapUnits_ofInfinite_eq h]
  rcases w.isReal_or_isComplex with hwR | hwC
  · -- `w` is real: the extension of completions is trivial
    have hunram : w.IsUnramified K := InfinitePlace.isUnramified_iff.mpr (Or.inl hwR)
    obtain ⟨a, ha⟩ := completionMap_surjective_of_isUnramified (w := w) (v := v) hunram (y : w.Completion)
    refine ⟨Units.mk0 a ?_, Units.ext ?_⟩
    · intro h0
      rw [h0, map_zero] at ha
      exact Units.ne_zero y ha.symm
    · simp only [Units.coe_map, Units.val_mk0]
      exact ha
  · rcases v.isReal_or_isComplex with hvR | hvC
    · -- `v` real and `w` complex: the genuinely local-Galois case
      have hconj := star_extensionEmbedding_eq_of_fixed hwC hvR y hy
      have hΦ : (starRingEnd ℂ)
          (InfinitePlace.Completion.extensionEmbedding w (y : w.Completion))
          = InfinitePlace.Completion.extensionEmbedding w (y : w.Completion) := hconj
      set r : ℝ := (InfinitePlace.Completion.extensionEmbedding w (y : w.Completion)).re with hr
      set a : v.Completion := (InfinitePlace.Completion.ringEquivRealOfIsReal hvR).symm r with ha
      have hstep : InfinitePlace.Completion.extensionEmbedding w
            (NumberField.LiesOver.completionMap (v := v) (w := w) a)
          = InfinitePlace.Completion.extensionEmbedding w (y : w.Completion) := by
        calc InfinitePlace.Completion.extensionEmbedding w
              (NumberField.LiesOver.completionMap (v := v) (w := w) a)
            = InfinitePlace.Completion.extensionEmbedding v a :=
              completionMap_extensionEmbedding (w := w) (v := v) hvR a
          _ = (InfinitePlace.Completion.extensionEmbeddingOfIsReal hvR a : ℂ) := by
              rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
          _ = ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR a : ℝ) : ℂ) := by
              rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
          _ = (r : ℂ) := by rw [ha, RingEquiv.apply_symm_apply]
          _ = InfinitePlace.Completion.extensionEmbedding w (y : w.Completion) := by
              rw [hr]; exact Complex.conj_eq_iff_re.mp hΦ
      refine ⟨Units.mk0 a ?_, Units.ext ?_⟩
      · intro h0
        rw [h0, map_zero] at hstep
        exact Units.ne_zero y
          ((InfinitePlace.Completion.extensionEmbedding w).injective hstep).symm
      · simp only [Units.coe_map, Units.val_mk0]
        exact (InfinitePlace.Completion.extensionEmbedding w).injective hstep
    · -- `v` complex: `w` is unramified, so the extension of completions is trivial
      have hunram : w.IsUnramified K := by
        refine InfinitePlace.isUnramified_iff.mpr (Or.inr ?_)
        rw [InfinitePlace.LiesOver.comap_eq w v]
        exact hvC
      obtain ⟨a, ha⟩ := completionMap_surjective_of_isUnramified (w := w) (v := v) hunram (y : w.Completion)
      refine ⟨Units.mk0 a ?_, Units.ext ?_⟩
      · intro h0
        rw [h0, map_zero] at ha
        exact Units.ne_zero y ha.symm
      · simp only [Units.coe_map, Units.val_mk0]
        exact ha

end NK.GlobalCFT.Galois
