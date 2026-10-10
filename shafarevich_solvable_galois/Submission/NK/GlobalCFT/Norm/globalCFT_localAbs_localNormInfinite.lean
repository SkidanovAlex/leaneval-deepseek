import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.IdeleNorm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Norm compatibility of the normalized absolute value at an infinite place

Let `L / K` be a finite extension of number fields and let `w` be an infinite place of `L` lying
over the infinite place `v` of `K`.  The local norm `N_{L_w/K_v} : L_wˣ →* K_vˣ` of the local
fields satisfies the classical compatibility with the normalized absolute values

`‖N_{L_w/K_v} y‖_v ^ v.mult = ‖y‖_w ^ w.mult`   for all `y : L_wˣ`,

i.e. `|N y|_v = |y|_w` for the normalized absolute values.  Consequently the "local absolute
value" `Idele.localAbs` of the idèle groups commutes with the local norm at an infinite place:

`NK.GlobalCFT.Idele.localAbs K v (localNormInfinite w v y) = NK.GlobalCFT.Idele.localAbs L w y`.

The archimedean case is elementary because the local fields are `ℝ` and `ℂ`: either the extension
is trivial (unramified), so that `w.Completion ≅ v.Completion` isometrically and the norm is the
inverse of the algebra map, or `v` is real, `w` is complex and `N_{ℂ/ℝ} z = ‖z‖ ^ 2 = z · z̄`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField.LiesOver NumberField RestrictedProduct
open NumberField

noncomputable section

namespace NK.GlobalCFT.Norm

/-! ### The embeddings `v.Completion →+* ℝ` and `v.Completion →+* ℂ` are isometries -/

/-- At a real infinite place `v`, the embedding `v.Completion →+* ℝ` is norm preserving. -/
theorem norm_extensionEmbeddingOfIsReal {K : Type*} [Field K] {v : InfinitePlace K}
    (hv : v.IsReal) (z : v.Completion) :
    ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hv z‖ = ‖z‖ := by
  simpa using (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).dist_eq z 0

/-- At any infinite place `v`, the embedding `v.Completion →+* ℂ` is norm preserving. -/
theorem norm_extensionEmbedding {K : Type*} [Field K] {v : InfinitePlace K} (z : v.Completion) :
    ‖InfinitePlace.Completion.extensionEmbedding v z‖ = ‖z‖ := by
  simpa using (InfinitePlace.Completion.isometry_extensionEmbedding v).dist_eq z 0

/-! ### The three archimedean cases for the local norm

We prove the compatibility of `Algebra.norm v.Completion` with the local absolute values by
transporting the norm along the ring isomorphisms `v.Completion ≃+* ℝ`, `v.Completion ≃+* ℂ`
(which are isometries) using `Algebra.norm_eq_of_equiv_equiv`. -/

/-- Both places are real: the local extension is trivial and the local norm is the inverse of the
isometric isomorphism `v.Completion ≃+* ℝ ≅ w.Completion`, hence norm preserving. -/
theorem norm_localNorm_of_isReal_of_isReal {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : InfinitePlace K) (w : InfinitePlace L) [hwv : w.LiesOver v]
    (hv : v.IsReal) (hw : w.IsReal) (x : w.Completion) :
    ‖Algebra.norm v.Completion x‖ = ‖x‖ := by
  have he : (algebraMap ℝ ℝ).comp (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toRingHom =
      (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom.comp
        (algebraMap v.Completion w.Completion) := by
    haveI : ComplexEmbedding.LiesOver (InfinitePlace.Completion.extensionEmbedding w)
        (InfinitePlace.Completion.extensionEmbedding v) :=
      InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, ← Complex.ofReal_inj]
    change Complex.ofReal (algebraMap ℝ ℝ ((InfinitePlace.Completion.ringEquivRealOfIsReal hv) a)) =
      Complex.ofReal ((InfinitePlace.Completion.ringEquivRealOfIsReal hw)
        ((algebraMap v.Completion w.Completion) a))
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv,
        InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw]
    simp only [Algebra.algebraMap_self_apply]
    rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv,
        InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    exact (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
      (φ := InfinitePlace.Completion.extensionEmbedding w) (x := a)).symm
  have hnorm : Algebra.norm v.Completion x =
      (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw) x) := by
    have h := Algebra.norm_eq_of_equiv_equiv (InfinitePlace.Completion.ringEquivRealOfIsReal hv)
      (InfinitePlace.Completion.ringEquivRealOfIsReal hw) he x
    rwa [Algebra.norm_self] at h
  rw [hnorm]
  have hsymm : ‖(InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw) x)‖ =
      ‖(InfinitePlace.Completion.ringEquivRealOfIsReal hw) x‖ := by
    rw [← norm_extensionEmbeddingOfIsReal hv]
    rw [← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv]
    simp
  rw [hsymm, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  exact norm_extensionEmbeddingOfIsReal hw x

/-- `v` is real and `w` is complex: the local extension is `ℂ / ℝ` of degree two and the local
norm is the square of the complex absolute value. -/
theorem norm_localNorm_of_isReal_of_isComplex {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : InfinitePlace K) (w : InfinitePlace L) [hwv : w.LiesOver v]
    (hv : v.IsReal) (hw : w.IsComplex) (x : w.Completion) :
    ‖Algebra.norm v.Completion x‖ = ‖x‖ ^ 2 := by
  haveI : ComplexEmbedding.LiesOver (InfinitePlace.Completion.extensionEmbedding w)
      (InfinitePlace.Completion.extensionEmbedding v) :=
    InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv
  have he : (algebraMap ℝ ℂ).comp (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toRingHom =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toRingHom.comp
        (algebraMap v.Completion w.Completion) := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply]
    change (algebraMap ℝ ℂ) ((InfinitePlace.Completion.ringEquivRealOfIsReal hv) a) =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
        ((algebraMap v.Completion w.Completion) a)
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv,
        InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hw]
    change Complex.ofReal ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hv) a) = _
    rw [InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
    exact (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
      (φ := InfinitePlace.Completion.extensionEmbedding w) (x := a)).symm
  have hnormx := Algebra.norm_eq_of_equiv_equiv (InfinitePlace.Completion.ringEquivRealOfIsReal hv)
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) he x
  simp only [Algebra.norm_complex_apply] at hnormx
  rw [hnormx]
  have h1 : ‖(InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
      (Complex.normSq ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) x))‖ =
      ‖Complex.normSq ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) x)‖ := by
    rw [← norm_extensionEmbeddingOfIsReal hv]
    rw [← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv]
    simp
  rw [h1, Real.norm_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq,
      InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
  exact congrArg (· ^ 2) (norm_extensionEmbedding x)

/-- `v` is complex (hence so is `w`): the local extension is trivial and the local norm is the
inverse of an isometric isomorphism `v.Completion ≅ w.Completion`, hence norm preserving. -/
theorem norm_localNorm_of_isComplex {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : InfinitePlace K) (w : InfinitePlace L) [hwv : w.LiesOver v]
    (hv : v.IsComplex) (x : w.Completion) :
    ‖Algebra.norm v.Completion x‖ = ‖x‖ := by
  have hwc : w.IsComplex := InfinitePlace.LiesOver.isComplex_of_isComplex_under w hv
  rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with h | h
  · haveI : ComplexEmbedding.LiesOver w.embedding v.embedding := ⟨h⟩
    haveI : ComplexEmbedding.LiesOver (InfinitePlace.Completion.extensionEmbedding w)
        (InfinitePlace.Completion.extensionEmbedding v) :=
      InfinitePlace.Completion.liesOver_extensionEmbedding w v
    have he : (algebraMap ℂ ℂ).comp
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).toRingHom =
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).toRingHom.comp
          (algebraMap v.Completion w.Completion) := by
      ext a
      rw [RingHom.comp_apply, RingHom.comp_apply]
      change (algebraMap ℂ ℂ) ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hv) a) =
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc)
          ((algebraMap v.Completion w.Completion) a)
      simp only [Algebra.algebraMap_self_apply]
      rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hwc,
          InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv]
      exact (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
        (φ := InfinitePlace.Completion.extensionEmbedding w) (x := a)).symm
    have hnormx := Algebra.norm_eq_of_equiv_equiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv)
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc) he x
    simp only [Algebra.norm_self, MonoidHom.id_apply] at hnormx
    rw [hnormx]
    have h1 : ‖(InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc) x)‖ =
        ‖(InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc) x‖ := by
      rw [← norm_extensionEmbedding]
      rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv]
      simp
    rw [h1, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    exact norm_extensionEmbedding x
  · haveI : ComplexEmbedding.LiesOver (ComplexEmbedding.conjugate w.embedding) v.embedding := ⟨h⟩
    haveI : ComplexEmbedding.LiesOver
        (ComplexEmbedding.conjugate (InfinitePlace.Completion.extensionEmbedding w))
        (InfinitePlace.Completion.extensionEmbedding v) :=
      InfinitePlace.Completion.liesOver_conjugate_extensionEmbedding w v
    have he : (algebraMap ℂ ℂ).comp
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).toRingHom =
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).trans
          (starRingAut (R := ℂ))).toRingHom.comp (algebraMap v.Completion w.Completion) := by
      ext a
      rw [RingHom.comp_apply, RingHom.comp_apply]
      change (algebraMap ℂ ℂ) ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hv) a) =
        (starRingAut (R := ℂ)) ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc)
          ((algebraMap v.Completion w.Completion) a))
      simp only [Algebra.algebraMap_self_apply]
      rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hwc,
          InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv]
      exact (InfinitePlace.Completion.liesOver_extensionEmbedding_apply
        (φ := ComplexEmbedding.conjugate (InfinitePlace.Completion.extensionEmbedding w))
        (x := a)).symm
    have hnormx := Algebra.norm_eq_of_equiv_equiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv)
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).trans (starRingAut (R := ℂ))) he x
    simp only [Algebra.norm_self, MonoidHom.id_apply] at hnormx
    rw [hnormx]
    have h1 : ‖(InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
        (((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).trans
          (starRingAut (R := ℂ))) x)‖ =
        ‖((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).trans
          (starRingAut (R := ℂ))) x‖ := by
      rw [← norm_extensionEmbedding]
      rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv]
      simp
    rw [h1]
    simp only [RingEquiv.trans_apply]
    rw [show starRingAut (R := ℂ) ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc) x) =
      (starRingEnd ℂ) ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc) x) from rfl]
    rw [Complex.norm_conj, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    exact norm_extensionEmbedding x

/-! ### The compatibility of the local norm with the normalized absolute values -/

/-- **Local norm and normalized absolute values.**  For a finite extension `L / K` of number
fields, infinite places `w | v` and `x : L_w`, the normalized absolute value of the local norm
`N_{L_w/K_v} x` (raised to the multiplicity `v.mult`) equals the normalized absolute value of `x`
(raised to `w.mult`).  Equivalently `|N x|_v = |x|_w` for the normalized absolute values. -/
theorem norm_localNorm_pow_mult {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : InfinitePlace K) (w : InfinitePlace L) [hwv : w.LiesOver v] (x : w.Completion) :
    ‖Algebra.norm v.Completion x‖ ^ v.mult = ‖x‖ ^ w.mult := by
  rcases v.isReal_or_isComplex with hv | hv
  · rcases w.isReal_or_isComplex with hw | hw
    · rw [norm_localNorm_of_isReal_of_isReal v w hv hw x, hv.mult_eq_one, hw.mult_eq_one]
    · rw [norm_localNorm_of_isReal_of_isComplex v w hv hw x, hv.mult_eq_one, hw.mult_eq_two,
        pow_one]
  · have hw : w.IsComplex := InfinitePlace.LiesOver.isComplex_of_isComplex_under w hv
    rw [norm_localNorm_of_isComplex v w hv x, hv.mult_eq_two, hw.mult_eq_two]

/-- The normalized local absolute value of the idèle group commutes with the local norm at an
infinite place: for `w | v` and `y : L_wˣ` one has
`localAbs K v (localNormInfinite w v y) = localAbs L w y`. -/
theorem globalCFT_localAbs_localNormInfinite {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L)
    (hw : NumberField.InfinitePlace.LiesOver w v) (y : w.Completionˣ) :
    letI : NumberField.InfinitePlace.LiesOver w v := hw
    NK.GlobalCFT.Idele.localAbs K (NK.GlobalCFT.Place.ofInfinite v)
        (NK.GlobalCFT.Place.localNormInfinite w v y) =
      NK.GlobalCFT.Idele.localAbs L (NK.GlobalCFT.Place.ofInfinite w) y := by
  letI : NumberField.InfinitePlace.LiesOver w v := hw
  rw [NK.GlobalCFT.Idele.localAbs_ofInfinite, NK.GlobalCFT.Idele.localAbs_ofInfinite]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  simp only [Units.val_mk0]
  exact norm_localNorm_pow_mult v w (y : w.Completion)

end NK.GlobalCFT.Norm
