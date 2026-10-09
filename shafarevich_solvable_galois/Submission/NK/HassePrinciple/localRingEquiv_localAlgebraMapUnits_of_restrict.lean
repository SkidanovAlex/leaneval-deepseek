import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.GlobalCFT.GaloisIdeles
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_comp
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_localAlgebraMapUnits
import Submission.NK.GlobalCFT.Galois.globalCFT_exists_localRingEquiv_smul
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective

/-!
# The local algebra maps over an intermediate field

Let `K ⊆ F ⊆ L` be a tower of number fields, `τ : L ≃ₐ[K] L` an automorphism of `L` over `K` and
`A : F ≃ₐ[K] F` the automorphism of the intermediate field `F` induced by `τ`
(`∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y)`).

For places `w` of `L` and `v` of `F` with `w` over `v`, the local field isomorphism
`Place.localRingEquiv τ w : L_w ≃+* L_{τ w}` intertwines the two ways of mapping the local units
`F_vˣ` into `L_{τ w}ˣ`: either first embed `F_v` into `L_w` and then apply `τ`, or first apply `A`
to obtain `F_{A v}` and then embed into `L_{τ w}`.

The proof reduces, by density of `F` in its completions, to the compatibility of the completions
of the field inclusions with the local isomorphisms; the latter is a computation at the level of
the `WithAbs`/`WithVal` copies of the fields.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField
open NumberField IsDedekindDomain
open NK.GlobalCFT

noncomputable section

namespace NK.HassePrinciple

/-- The completion map `F_v →+* L_w` at archimedean places is compatible with the embeddings of
the base field. -/
private lemma completionMap_algebraMap_infinite {F L : Type*} [Field F] [NumberField F] [Field L]
    [NumberField L] [Algebra F L] (v : NumberField.InfinitePlace F)
    (w : NumberField.InfinitePlace L) [w.LiesOver v] (f : F) :
    NumberField.LiesOver.completionMap (v := v) (w := w) (algebraMap F v.Completion f) =
      algebraMap L w.Completion (algebraMap F L f) := by
  rw [show (algebraMap F v.Completion f)
      = ((WithAbs.toAbs v.1 f : WithAbs v.1) : v.Completion) from rfl,
    show algebraMap L w.Completion (algebraMap F L f)
      = ((WithAbs.toAbs w.1 (algebraMap F L f) : WithAbs w.1) : w.Completion) from rfl]
  rw [NumberField.LiesOver.completionMap_coe]
  congr 1

/-- The completion map `F_Q →+* L_q` at nonarchimedean places is compatible with the embeddings
of the base field. -/
private lemma adicCompletionMap_algebraMap {F L : Type*} [Field F] [NumberField F] [Field L]
    [NumberField L] [Algebra F L] (Q : HeightOneSpectrum (𝓞 F)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (f : F) :
    Commons.RingTheory.Henselian.adicCompletionMap Q q hq (algebraMap F (Q.adicCompletion F) f) =
      algebraMap L (q.adicCompletion L) (algebraMap F L f) := by
  show Commons.RingTheory.Henselian.adicCompletionMap Q q hq (f : Q.adicCompletion F) =
    algebraMap L (q.adicCompletion L) (algebraMap F L f)
  rw [Commons.RingTheory.Henselian.adicCompletionMap_apply]
  rfl

section Tower

variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]

omit [IsScalarTower K F L] in
/-- The archimedean case of the naturality of the completion maps in the intermediate field: the
local isomorphism `L_w ≃+* L_{τ w}` induced by `τ` intertwines the completions of the inclusion
`F → L` at `v` and at `A v`. -/
private lemma infinite_naturality (τ : L ≃ₐ[K] L) (A : F ≃ₐ[K] F)
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    (v : NumberField.InfinitePlace F) (w : NumberField.InfinitePlace L) [w.LiesOver v]
    [(τ • w).LiesOver (A • v)] (x : v.Completion) :
    Galois.globalCFT_infiniteCongrEquiv τ w
        (NumberField.LiesOver.completionMap (v := v) (w := w) x) =
      NumberField.LiesOver.completionMap (v := A • v) (w := τ • w)
        (Galois.globalCFT_infiniteCongrEquiv A v x) := by
  have key : (fun y : v.Completion =>
        Galois.globalCFT_infiniteCongrEquiv τ w
          (NumberField.LiesOver.completionMap (v := v) (w := w) y)) =
      fun y => NumberField.LiesOver.completionMap (v := A • v) (w := τ • w)
        (Galois.globalCFT_infiniteCongrEquiv A v y) := by
    refine DenseRange.equalizer (f := algebraMap F v.Completion) ?_ ?_ ?_ ?_
    · exact Galois.denseRange_algebraMap_localField (Place.ofInfinite v)
    · exact (Galois.continuous_localRingEquiv τ (Place.ofInfinite w)).comp
        NumberField.LiesOver.continuous_completionMap
    · exact NumberField.LiesOver.continuous_completionMap.comp
        (Galois.continuous_localRingEquiv A (Place.ofInfinite v))
    · funext y
      simp only [Function.comp_apply]
      rw [completionMap_algebraMap_infinite v w y,
        Galois.globalCFT_infiniteCongrEquiv_algebraMap τ w (algebraMap F L y),
        Galois.globalCFT_infiniteCongrEquiv_algebraMap A v y,
        completionMap_algebraMap_infinite (A • v) (τ • w) (A y), hA y]
  exact congrFun key x

omit [IsScalarTower K F L] in
/-- The nonarchimedean case of the naturality of the completion maps in the intermediate field. -/
private lemma finite_naturality (τ : L ≃ₐ[K] L) (A : F ≃ₐ[K] F)
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    (Q : HeightOneSpectrum (𝓞 F)) (q : HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hq' : (Place.smulHeightOneSpectrum τ q).asIdeal.LiesOver
      (Place.smulHeightOneSpectrum A Q).asIdeal) (x : Q.adicCompletion F) :
    Galois.globalCFT_adicCongrEquiv τ q
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq x) =
      Commons.RingTheory.Henselian.adicCompletionMap (Place.smulHeightOneSpectrum A Q)
        (Place.smulHeightOneSpectrum τ q) hq'
        (Galois.globalCFT_adicCongrEquiv A Q x) := by
  have key : (fun y : Q.adicCompletion F =>
      Galois.globalCFT_adicCongrEquiv τ q
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq y)) =
      fun y => Commons.RingTheory.Henselian.adicCompletionMap (Place.smulHeightOneSpectrum A Q)
        (Place.smulHeightOneSpectrum τ q) hq'
        (Galois.globalCFT_adicCongrEquiv A Q y) := by
    refine DenseRange.equalizer (f := algebraMap F (Q.adicCompletion F)) ?_ ?_ ?_ ?_
    · exact Galois.denseRange_algebraMap_localField (Place.ofFinite Q)
    · exact (Galois.globalCFT_adicCongrEquiv_continuous τ q).comp
        (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq)
    · exact (Commons.RingTheory.Henselian.adicCompletionMap_continuous
        (Place.smulHeightOneSpectrum A Q) (Place.smulHeightOneSpectrum τ q) hq').comp
        (Galois.globalCFT_adicCongrEquiv_continuous A Q)
    · funext y
      simp only [Function.comp_apply]
      rw [adicCompletionMap_algebraMap Q q hq y,
        Galois.globalCFT_adicCongrEquiv_algebraMap τ q (algebraMap F L y),
        Galois.globalCFT_adicCongrEquiv_algebraMap A Q y]
      rw [show A.toRingEquiv y = A y from rfl,
        show τ.toRingEquiv (algebraMap F L y) = τ (algebraMap F L y) from rfl]
      rw [adicCompletionMap_algebraMap (Place.smulHeightOneSpectrum A Q)
          (Place.smulHeightOneSpectrum τ q) hq' (A y),
        hA y]
  exact congrFun key x

end Tower

theorem localRingEquiv_localAlgebraMapUnits_of_restrict {K F L : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Field L] [NumberField L] [Algebra K F] [Algebra F L] [Algebra K L]
    [IsScalarTower K F L]
    (τ : L ≃ₐ[K] L) (A : F ≃ₐ[K] F)
    (hA : ∀ y : F, algebraMap F L (A y) = τ (algebraMap F L y))
    {w : NK.GlobalCFT.Place L} {v : NK.GlobalCFT.Place F}
    (h : NK.GlobalCFT.Place.LiesOver w v)
    (h' : NK.GlobalCFT.Place.LiesOver (τ • w) (A • v))
    (a : (NK.GlobalCFT.Place.localField F v)ˣ) :
    Units.map (NK.GlobalCFT.Place.localRingEquiv τ w).toMonoidHom
        (NK.GlobalCFT.Place.localAlgebraMapUnits w v h a) =
      NK.GlobalCFT.Place.localAlgebraMapUnits (τ • w) (A • v) h'
        (Units.map (NK.GlobalCFT.Place.localRingEquiv A v).toMonoidHom a) := by
  rcases w with w | q <;> rcases v with v | Q
  · -- an archimedean place over an archimedean place
    simp only [Place.smul_ofInfinite] at h' ⊢
    haveI : w.LiesOver v := (Galois.globalCFT_liesOver_ofInfinite_iff w v).mp h
    haveI : (τ • w).LiesOver (A • v) :=
      (Galois.globalCFT_liesOver_ofInfinite_iff (τ • w) (A • v)).mp h'
    simp only [Place.localAlgebraMapUnits, Place.localRingEquiv]
    rw [dif_pos (show w.LiesOver v from inferInstance),
      dif_pos (show (τ • w).LiesOver (A • v) from inferInstance)]
    apply Units.ext
    simp only [Units.coe_map]
    exact infinite_naturality τ A hA v w (a : v.Completion)
  · -- an archimedean place over a nonarchimedean place: both sides are trivial
    simp [Place.smul_ofInfinite, Place.smul_ofFinite, Place.localAlgebraMapUnits,
      Place.localRingEquiv]
  · -- a nonarchimedean place over an archimedean place: both sides are trivial
    simp [Place.smul_ofInfinite, Place.smul_ofFinite, Place.localAlgebraMapUnits,
      Place.localRingEquiv]
  · -- a nonarchimedean place over a nonarchimedean place
    simp only [Place.smul_ofFinite] at h' ⊢
    haveI : q.asIdeal.LiesOver Q.asIdeal := (Galois.globalCFT_liesOver_ofFinite_iff q Q).mp h
    haveI : (Place.smulHeightOneSpectrum τ q).asIdeal.LiesOver
        (Place.smulHeightOneSpectrum A Q).asIdeal :=
      (Galois.globalCFT_liesOver_ofFinite_iff (Place.smulHeightOneSpectrum τ q)
        (Place.smulHeightOneSpectrum A Q)).mp h'
    simp only [Place.localAlgebraMapUnits, Place.localRingEquiv]
    rw [dif_pos (show q.asIdeal.LiesOver Q.asIdeal from inferInstance),
      dif_pos (show (Place.smulHeightOneSpectrum τ q).asIdeal.LiesOver
        (Place.smulHeightOneSpectrum A Q).asIdeal from inferInstance)]
    apply Units.ext
    simp only [Units.coe_map]
    exact finite_naturality τ A hA Q q _ _ (a : Q.adicCompletion F)

end NK.HassePrinciple
