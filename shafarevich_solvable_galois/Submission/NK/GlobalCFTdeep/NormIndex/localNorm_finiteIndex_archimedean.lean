/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFTdeep.NormIndex.Defs
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_principalIdele
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local norm at an archimedean place has finite index image

For a finite extension `L / K` of number fields, an infinite place `w` of `L` lying over the
infinite place `v` of `K`, the local norm

`N_{L_w/K_v} : L_wˣ →* K_vˣ`

is `NK.GlobalCFT.Place.localNormInfinite w v`, the norm of the completion extension.  The main
result of this file is

* `NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean` : the range of this norm map has
  finite index in `K_vˣ`.

Since `K_v` and `L_w` are each either `ℝ` or `ℂ`, this is an elementary statement: the norm map is
either an isomorphism (so its range is everything) or, in the case `ℝ ⊂ ℂ`, the map `z ↦ z * z̄`
whose image is the subgroup of positive reals, of index `2` in `ℝˣ`.

The proof reduces the norm map to its classical description at the level of the archimedean
embeddings.  The three cases are the lemmas

* `localNormInfinite_norm_eq_real_real`, `localNormInfinite_norm_eq_real_complex`,
  `localNormInfinite_norm_eq_complex_complex` (`…_of_not` for the conjugate case),

which identify `N` after transporting `v.Completion` and `w.Completion` to `ℝ` or to `ℂ` along
`InfinitePlace.Completion.ringEquivRealOfIsReal` and
`InfinitePlace.Completion.ringEquivComplexOfIsComplex`.  They are immediate consequences of the
product formula for the norm over the archimedean places
(`NK.GlobalCFT.Norm.factor_real_real` and friends).

The archimedean place `w` is real exactly when `v` is real and the extension is unramified, and is
complex with `v` real in the ramified case; a complex place `v` is only covered by complex places
`w`.  Accordingly the three cases above exhaust all possibilities.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField Classical
open scoped NumberField.LiesOver

noncomputable section

namespace NK.GlobalCFTdeep.NormIndex

open NK.GlobalCFT

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-! ### The computation of the local norm -/

/-- The local norm at an infinite place, transported to `ℝ`, in the real/real case: it is the
identity, i.e. `N_{K_v/L_w}` identifies `w.Completion ≅ ℝ` with `v.Completion ≅ ℝ`. -/
theorem localNormInfinite_norm_eq_real_real {v : InfinitePlace K} {w : InfinitePlace L}
    [w.LiesOver v] (hvR : v.IsReal) (hwR : w.IsReal) (z : w.Completion) :
    (InfinitePlace.Completion.ringEquivRealOfIsReal hvR) (Algebra.norm v.Completion z)
      = (InfinitePlace.Completion.ringEquivRealOfIsReal hwR) z := by
  apply Complex.ofReal_injective
  simp only [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  exact NK.GlobalCFT.Norm.factor_real_real hvR hwR z

/-- The local norm at an infinite place, transported to `ℝ` and `ℂ`, in the real/complex case:
it is `z ↦ z * z̄`, i.e. the square of the complex absolute value. -/
theorem localNormInfinite_norm_eq_real_complex {v : InfinitePlace K} {w : InfinitePlace L}
    [w.LiesOver v] (hvR : v.IsReal) (hwC : w.IsComplex) (z : w.Completion) :
    (InfinitePlace.Completion.ringEquivRealOfIsReal hvR) (Algebra.norm v.Completion z)
      = Complex.normSq ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC) z) := by
  apply Complex.ofReal_injective
  simp only [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply,
    InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
  exact NK.GlobalCFT.Norm.factor_real_complex hvR hwC z

/-- The local norm at an infinite place, both places complex and the embeddings compatible: after
transport to `ℂ` it is the identity. -/
theorem localNormInfinite_norm_eq_complex_complex {v : InfinitePlace K} {w : InfinitePlace L}
    [w.LiesOver v] (hvC : v.IsComplex) (hwC : w.IsComplex)
    (hlies : ComplexEmbedding.LiesOver w.embedding v.embedding) (z : w.Completion) :
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC) (Algebra.norm v.Completion z)
      = (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC) z := by
  have h := NK.GlobalCFT.Norm.factor_complex_complex hvC hwC z
  rw [if_pos hlies] at h
  simpa only [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply] using h

/-- The local norm at an infinite place, both places complex and the embeddings conjugate: after
transport to `ℂ` it is complex conjugation. -/
theorem localNormInfinite_norm_eq_complex_complex_of_not {v : InfinitePlace K} {w : InfinitePlace L}
    [w.LiesOver v] (hvC : v.IsComplex) (hwC : w.IsComplex)
    (hlies : ¬ ComplexEmbedding.LiesOver w.embedding v.embedding) (z : w.Completion) :
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC) (Algebra.norm v.Completion z)
      = starRingEnd ℂ ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC) z) := by
  have h := NK.GlobalCFT.Norm.factor_complex_complex hvC hwC z
  rw [if_neg hlies] at h
  simpa only [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply] using h

/-! ### The three cases of the finiteness of the local norm index -/

section Main

variable {v : InfinitePlace K} {w : InfinitePlace L} [hw : w.LiesOver v]

/-- The real/real case: the local norm on units is surjective. -/
theorem localNormInfinite_range_eq_top_of_real_real (hvR : v.IsReal) (hwR : w.IsReal) :
    (Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion)).range = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro u
  set z : w.Completion := (InfinitePlace.Completion.ringEquivRealOfIsReal hwR).symm
    ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR) (u : v.Completion)) with hz
  have hzne : z ≠ 0 := by
    intro h0
    have h1 : (InfinitePlace.Completion.ringEquivRealOfIsReal hvR) (u : v.Completion) = 0 := by
      have := congrArg (InfinitePlace.Completion.ringEquivRealOfIsReal hwR) h0
      simp only [hz, map_zero, RingEquiv.apply_symm_apply] at this
      exact this
    exact u.ne_zero ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).injective
      (by rw [h1, map_zero]))
  refine ⟨Units.mk0 z hzne, ?_⟩
  apply Units.ext
  rw [Units.coe_map]
  show Algebra.norm v.Completion z = (u : v.Completion)
  refine (InfinitePlace.Completion.ringEquivRealOfIsReal hvR).injective ?_
  rw [localNormInfinite_norm_eq_real_real hvR hwR, hz, RingEquiv.apply_symm_apply]

/-- The complex/complex case: the local norm on units is surjective. -/
theorem localNormInfinite_range_eq_top_of_complex_complex (hvC : v.IsComplex) (hwC : w.IsComplex) :
    (Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion)).range = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro u
  by_cases hlies : ComplexEmbedding.LiesOver w.embedding v.embedding
  · set z : w.Completion := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).symm
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC) (u : v.Completion)) with hz
    have hzne : z ≠ 0 := by
      intro h0
      have h1 : (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC) (u : v.Completion)
          = 0 := by
        have := congrArg (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC) h0
        simp only [hz, map_zero, RingEquiv.apply_symm_apply] at this
        exact this
      exact u.ne_zero ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC).injective
        (by rw [h1, map_zero]))
    refine ⟨Units.mk0 z hzne, ?_⟩
    apply Units.ext
    rw [Units.coe_map]
    show Algebra.norm v.Completion z = (u : v.Completion)
    refine (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC).injective ?_
    rw [localNormInfinite_norm_eq_complex_complex hvC hwC hlies, hz,
      RingEquiv.apply_symm_apply]
  · set z : w.Completion := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).symm
      (starRingEnd ℂ ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC)
        (u : v.Completion))) with hz
    have hzne : z ≠ 0 := by
      intro h0
      have h1 : starRingEnd ℂ ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC)
          (u : v.Completion)) = 0 := by
        have := congrArg (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC) h0
        simp only [hz, map_zero, RingEquiv.apply_symm_apply] at this
        exact this
      have h2 : (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC) (u : v.Completion)
          = 0 := by
        have := congrArg (starRingEnd ℂ) h1
        rw [Complex.conj_conj, map_zero] at this
        exact this
      exact u.ne_zero ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC).injective
        (by rw [h2, map_zero]))
    refine ⟨Units.mk0 z hzne, ?_⟩
    apply Units.ext
    rw [Units.coe_map]
    show Algebra.norm v.Completion z = (u : v.Completion)
    refine (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC).injective ?_
    rw [localNormInfinite_norm_eq_complex_complex_of_not hvC hwC hlies, hz,
      RingEquiv.apply_symm_apply, Complex.conj_conj]

/-- The positive units of an archimedean completion have finite index in its unit group: they are
the image of `Units.posSubgroup ℝ` under the identification of `v.Completion` with `ℝ`, and the
positive units have index `2` in `ℝˣ`. -/
theorem localNormInfinite_posSubgroup_finiteIndex {v : InfinitePlace K} (hvR : v.IsReal) :
    ((Units.posSubgroup ℝ).comap
      (Units.map ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom)
        : v.Completionˣ →* ℝˣ)).FiniteIndex := by
  have hsurj : Function.Surjective (Units.map
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom)
        : v.Completionˣ →* ℝˣ) :=
    (Units.mapEquiv ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv)).surjective
  have hidx : ((Units.posSubgroup ℝ).comap
        (Units.map ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom)
          : v.Completionˣ →* ℝˣ)).index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ hsurj, Units.index_posSubgroup]
  exact Subgroup.finiteIndex_iff.mpr (by rw [hidx]; norm_num)

/-- The real/complex case: the local norm on units surjects onto the positive units. -/
theorem localNormInfinite_posSubgroup_le_range_of_real_complex (hvR : v.IsReal) (hwC : w.IsComplex) :
    (Units.posSubgroup ℝ).comap
      (Units.map ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom)
        : v.Completionˣ →* ℝˣ)
      ≤ (Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion)).range := by
  intro u hu
  rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map] at hu
  have htu : 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hvR) (u : v.Completion) := by
    simpa using hu
  have hst : 0 < Real.sqrt ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
      (u : v.Completion)) := Real.sqrt_pos.mpr htu
  set z : w.Completion := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC).symm
    ((Real.sqrt ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR) (u : v.Completion)) : ℝ) : ℂ)
    with hz
  have hzne : z ≠ 0 := by
    intro h0
    have h1 : ((Real.sqrt ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR)
        (u : v.Completion)) : ℝ) : ℂ) = 0 := by
      have := congrArg (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC) h0
      simp only [hz, map_zero, RingEquiv.apply_symm_apply] at this
      exact this
    exact (ne_of_gt hst) (Complex.ofReal_injective (by simpa using h1))
  refine ⟨Units.mk0 z hzne, ?_⟩
  apply Units.ext
  rw [Units.coe_map]
  show Algebra.norm v.Completion z = (u : v.Completion)
  refine (InfinitePlace.Completion.ringEquivRealOfIsReal hvR).injective ?_
  rw [localNormInfinite_norm_eq_real_complex hvR hwC, hz, RingEquiv.apply_symm_apply,
    Complex.normSq_ofReal, Real.mul_self_sqrt (le_of_lt htu)]

end Main

theorem localNorm_finiteIndex_archimedean {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K) [hw : w.LiesOver v] : (NK.GlobalCFT.Place.localNormInfinite w v).range.FiniteIndex := by
  rw [show NK.GlobalCFT.Place.localNormInfinite w v
      = Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl]
  rcases v.isReal_or_isComplex with hvR | hvC
  · rcases w.isReal_or_isComplex with hwR | hwC
    · rw [localNormInfinite_range_eq_top_of_real_real hvR hwR]
      exact inferInstance
    · haveI := localNormInfinite_posSubgroup_finiteIndex (v := v) hvR
      exact Subgroup.finiteIndex_of_le
        (localNormInfinite_posSubgroup_le_range_of_real_complex hvR hwC)
  · have hwC : w.IsComplex := InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
    rw [localNormInfinite_range_eq_top_of_complex_complex hvC hwC]
    exact inferInstance

end NK.GlobalCFTdeep.NormIndex
