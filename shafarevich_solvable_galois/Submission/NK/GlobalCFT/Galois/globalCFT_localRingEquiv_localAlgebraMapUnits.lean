import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.GaloisIdeles
import Submission.NK.GlobalCFT.GaloisIdelesAction
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### The local algebra maps are equivariant under the action of `Gal(L/K)`

For a finite extension `L / K` of number fields, a place `w` of `L` lying over a place `v` of `K`
and `σ : Gal(L/K)` there are two natural units maps `K_vˣ →* L_wˣ`, namely the one attached to the
place `w` and the one attached to `σ • w`; the canonical local isomorphism
`Place.localRingEquiv σ w : L_w ≃+* L_{σ w}` intertwines them.  This is the statement that the
local algebra maps are `Gal(L/K)`-equivariant.

The proof is by reduction to the archimedean and nonarchimedean cases, where the claim becomes a
computation with the explicit definitions of `globalCFT_infiniteCongrEquiv` (a completion of the
`WithAbs`-level isomorphism `globalCFT_withAbsCongrEquiv`) and `globalCFT_adicCongrEquiv` (a
completion of the `WithVal`-level isomorphism `WithVal.congr`). -/

/-- The archimedean local isomorphism, evaluated at an element of the archimedean completion
coming from the `WithAbs`-copy of `L`. -/
lemma globalCFT_infiniteCongrEquiv_coe (σ : L ≃ₐ[K] L) (w : InfinitePlace L)
    (y : WithAbs (w.1)) :
    globalCFT_infiniteCongrEquiv σ w (y : w.Completion) =
      (globalCFT_withAbsCongrEquiv σ w y : (σ • w).Completion) := by
  rw [globalCFT_infiniteCongrEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply,
    NumberField.InfinitePlace.Completion.equiv_apply,
    UniformSpace.Completion.mapRingEquiv_apply]
  rw [show ((y : w.Completion).toCompletion) = (y : w.1.Completion) from rfl]
  rw [UniformSpace.Completion.map_coe
    (globalCFT_isometry_withAbsCongrEquiv σ w).uniformContinuous]
  rfl

/-- At the level of the `WithAbs`-copies of `L`, the archimedean isomorphism attached to `σ`
intertwines the algebra maps `K → L`. -/
lemma globalCFT_withAbsCongrEquiv_algebraMap (σ : L ≃ₐ[K] L) (v : InfinitePlace K)
    (w : InfinitePlace L) [w.LiesOver v] [(σ • w).LiesOver v] (a : WithAbs (v.1)) :
    globalCFT_withAbsCongrEquiv σ w (algebraMap (WithAbs (v.1)) (WithAbs (w.1)) a) =
      algebraMap (WithAbs (v.1)) (WithAbs ((σ • w).1)) a := by
  rw [globalCFT_withAbsCongrEquiv, WithAbs.congr_apply, WithAbs.ofAbs_algebraMap,
    WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]
  congr 1
  exact AlgEquiv.commutes σ a.ofAbs

/-- The archimedean case of the equivariance: the local isomorphism `L_w ≃+* L_{σ w}` intertwines
the completion maps `K_v →+* L_w` and `K_v →+* L_{σ w}`. -/
lemma globalCFT_infiniteCongrEquiv_completionMap (σ : L ≃ₐ[K] L) (v : InfinitePlace K)
    (w : InfinitePlace L) [w.LiesOver v] [(σ • w).LiesOver v] (x : v.Completion) :
    globalCFT_infiniteCongrEquiv σ w (NumberField.LiesOver.completionMap (v := v) (w := w) x) =
      NumberField.LiesOver.completionMap (v := v) (w := σ • w) x := by
  induction x using NumberField.InfinitePlace.Completion.induction_on
  · exact isClosed_eq
      ((continuous_localRingEquiv σ (Place.ofInfinite w)).comp
        (NumberField.LiesOver.continuous_completionMap (v := v) (w := w)))
      (NumberField.LiesOver.continuous_completionMap (v := v) (w := σ • w))
  · rw [NumberField.LiesOver.completionMap_coe (v := v) (w := w),
      NumberField.LiesOver.completionMap_coe (v := v) (w := σ • w),
      globalCFT_infiniteCongrEquiv_coe, globalCFT_withAbsCongrEquiv_algebraMap]

/-- The nonarchimedean case of the equivariance, on elements of the base field `K`. -/
lemma globalCFT_adicCongrEquiv_adicCompletionMap_base (σ : L ≃ₐ[K] L)
    (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (h : q.asIdeal.LiesOver Q.asIdeal) (h' : (Place.smulHeightOneSpectrum σ q).asIdeal.LiesOver Q.asIdeal)
    (x : K) :
    globalCFT_adicCongrEquiv σ q
        (Commons.RingTheory.Henselian.adicCompletionMap Q q h (x : Q.adicCompletion K)) =
      Commons.RingTheory.Henselian.adicCompletionMap Q (Place.smulHeightOneSpectrum σ q) h'
        (x : Q.adicCompletion K) := by
  rw [Commons.RingTheory.Henselian.adicCompletionMap_apply Q q h,
    Commons.RingTheory.Henselian.adicCompletionMap_apply Q (Place.smulHeightOneSpectrum σ q) h',
    globalCFT_adicCongrEquiv_coe]
  congr 1
  congr 1
  exact congrArg (WithVal.toVal (HeightOneSpectrum.valuation L (Place.smulHeightOneSpectrum σ q)))
    (AlgEquiv.commutes σ x)

/-- The nonarchimedean case of the equivariance: the local isomorphism `L_q ≃+* L_{σ q}`
intertwines the adic completion maps `K_Q →+* L_q` and `K_Q →+* L_{σ q}`. -/
lemma globalCFT_adicCongrEquiv_adicCompletionMap (σ : L ≃ₐ[K] L)
    (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (h : q.asIdeal.LiesOver Q.asIdeal) (h' : (Place.smulHeightOneSpectrum σ q).asIdeal.LiesOver Q.asIdeal)
    (x : Q.adicCompletion K) :
    globalCFT_adicCongrEquiv σ q (Commons.RingTheory.Henselian.adicCompletionMap Q q h x) =
      Commons.RingTheory.Henselian.adicCompletionMap Q (Place.smulHeightOneSpectrum σ q) h' x := by
  have hfun := DenseRange.equalizer
    (f := algebraMap K (Q.adicCompletion K))
    (g := fun z => globalCFT_adicCongrEquiv σ q
      (Commons.RingTheory.Henselian.adicCompletionMap Q q h z))
    (h := fun z => Commons.RingTheory.Henselian.adicCompletionMap Q
      (Place.smulHeightOneSpectrum σ q) h' z)
    (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) K Q)
    ((globalCFT_adicCongrEquiv_continuous σ q).comp
      (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q h))
    (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q
      (Place.smulHeightOneSpectrum σ q) h')
    (by funext y; exact globalCFT_adicCongrEquiv_adicCompletionMap_base σ q Q h h' y)
  exact congrFun hfun x

/-- The canonical local isomorphism `Place.localRingEquiv σ w : L_w ≃+* L_{σ w}` intertwines the
local algebra maps `K_vˣ →* L_wˣ` and `K_vˣ →* L_{σ w}ˣ`: the local algebra maps are
`Gal(L/K)`-equivariant. -/
theorem globalCFT_localRingEquiv_localAlgebraMapUnits {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L) {w : Place L} {v : Place K}
    (h : Place.LiesOver w v) (h' : Place.LiesOver (σ • w) v)
    (a : (Place.localField K v)ˣ) :
    Units.map (Place.localRingEquiv σ w).toMonoidHom
        (Place.localAlgebraMapUnits w v h a) =
      Place.localAlgebraMapUnits (σ • w) v h' a := by
  rcases w with w | q
  · rcases v with v | Q
    · -- archimedean place over an archimedean place
      simp only [Place.smul_ofInfinite] at h' ⊢
      haveI : w.LiesOver v := (globalCFT_liesOver_ofInfinite_iff w v).mp h
      haveI : (σ • w).LiesOver v := (globalCFT_liesOver_ofInfinite_iff (σ • w) v).mp h'
      simp only [Place.localAlgebraMapUnits, Place.localRingEquiv]
      rw [dif_pos (show w.LiesOver v from inferInstance),
        dif_pos (show (σ • w).LiesOver v from inferInstance)]
      apply Units.ext
      simp only [Units.coe_map]
      exact globalCFT_infiniteCongrEquiv_completionMap σ v w (a : v.Completion)
    · -- archimedean place over a nonarchimedean place: both sides are trivial
      simp [Place.smul_ofInfinite, Place.localAlgebraMapUnits, Place.localRingEquiv]
      try exact map_one _
  · rcases v with v | Q
    · -- nonarchimedean place over an archimedean place: both sides are trivial
      simp [Place.smul_ofFinite, Place.localAlgebraMapUnits, Place.localRingEquiv]
      try exact map_one _
    · -- nonarchimedean place over a nonarchimedean place
      simp only [Place.smul_ofFinite] at h' ⊢
      haveI : q.asIdeal.LiesOver Q.asIdeal := (globalCFT_liesOver_ofFinite_iff q Q).mp h
      haveI : (Place.smulHeightOneSpectrum σ q).asIdeal.LiesOver Q.asIdeal :=
        (globalCFT_liesOver_ofFinite_iff (Place.smulHeightOneSpectrum σ q) Q).mp h'
      simp only [Place.localAlgebraMapUnits, Place.localRingEquiv]
      rw [dif_pos (show q.asIdeal.LiesOver Q.asIdeal from inferInstance),
        dif_pos (show (Place.smulHeightOneSpectrum σ q).asIdeal.LiesOver Q.asIdeal from
          inferInstance)]
      apply Units.ext
      simp only [Units.coe_map]
      exact globalCFT_adicCongrEquiv_adicCompletionMap σ q Q _ _ (a : Q.adicCompletion K)

end NK.GlobalCFT.Galois
