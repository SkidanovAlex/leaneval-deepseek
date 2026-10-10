import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_principalIdele
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# An open subgroup of `K_vˣ` inside the image of the local norm (archimedean place)

Let `L / K` be a finite extension of number fields, `w` an archimedean place of `L` lying over the
archimedean place `v` of `K`.  The local norm `N_{L_w/K_v} : L_wˣ →* K_vˣ` has open image: since
`K_v` and `L_w` are each `ℝ` or `ℂ`, the norm map is either surjective (`ℝ/ℝ`, `ℂ/ℂ`) or else
`ℂˣ → ℝˣ`, `z ↦ z z̄ = |z|²`, whose image is the open subgroup `ℝ_{>0}` of `ℝˣ` (the real/complex
case).

This file proves the universe-polymorphic form of the archimedean computation (the version on disk
in `NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean` is restricted to `Type 0`), and
then produces the open subgroup.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField Classical
open scoped NumberField.LiesOver

noncomputable section

namespace NK.NUV2.ArtinBridge

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ### The computation of the archimedean local norm -/

section NormComputation

variable {v : InfinitePlace K} {w : InfinitePlace L} [hw : w.LiesOver v]

/-- The local norm at an infinite place, transported to `ℝ`, in the real/real case: it is the
identity. -/
theorem localNormInfinite_norm_eq_real_real (hvR : v.IsReal) (hwR : w.IsReal)
    (z : w.Completion) :
    (InfinitePlace.Completion.ringEquivRealOfIsReal hvR) (Algebra.norm v.Completion z)
      = (InfinitePlace.Completion.ringEquivRealOfIsReal hwR) z := by
  apply Complex.ofReal_injective
  simp only [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  exact NK.GlobalCFT.Norm.factor_real_real hvR hwR z

/-- The local norm at an infinite place, transported to `ℝ` and `ℂ`, in the real/complex case:
it is `z ↦ z z̄`. -/
theorem localNormInfinite_norm_eq_real_complex (hvR : v.IsReal) (hwC : w.IsComplex)
    (z : w.Completion) :
    (InfinitePlace.Completion.ringEquivRealOfIsReal hvR) (Algebra.norm v.Completion z)
      = Complex.normSq ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC) z) := by
  apply Complex.ofReal_injective
  simp only [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply,
    InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
  exact NK.GlobalCFT.Norm.factor_real_complex hvR hwC z

/-- The local norm at an infinite place, both places complex: after transport to `ℂ` it is the
identity if the embeddings are compatible, and complex conjugation otherwise. -/
theorem localNormInfinite_norm_eq_complex_complex (hvC : v.IsComplex) (hwC : w.IsComplex)
    (z : w.Completion) :
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC) (Algebra.norm v.Completion z)
      = if ComplexEmbedding.LiesOver w.embedding v.embedding
        then (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC) z
        else starRingEnd ℂ ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC) z) := by
  have h := NK.GlobalCFT.Norm.factor_complex_complex hvC hwC z
  by_cases hlies : ComplexEmbedding.LiesOver w.embedding v.embedding
  · rw [if_pos hlies] at h
    simpa only [if_pos hlies, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply] using h
  · rw [if_neg hlies] at h
    simpa only [if_neg hlies, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply] using h

/-! ### The three cases of surjectivity of the local norm on units -/

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

/-- The complex/complex case: the local norm on units is surjective (it is the identity or complex
conjugation after transport to `ℂ`). -/
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
    rw [localNormInfinite_norm_eq_complex_complex hvC hwC, if_pos hlies, hz,
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
    rw [localNormInfinite_norm_eq_complex_complex hvC hwC, if_neg hlies, hz,
      RingEquiv.apply_symm_apply, Complex.conj_conj]

/-- The real/complex case: the local norm on units surjects onto the positive units of `ℝˣ`,
i.e. onto the preimage of `ℝ_{>0}` under the identification `K_v ≅ ℝ`. -/
theorem localNormInfinite_posSubgroup_le_range_of_real_complex (hvR : v.IsReal)
    (hwC : w.IsComplex) :
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

end NormComputation

/-! ### The open subgroup -/

/-- The preimage of the positive units of `ℝˣ` under the identification `K_vˣ ≅ ℝˣ` is an open
subgroup of `K_vˣ`. -/
theorem isOpen_posSubgroup_comap (v : InfinitePlace K) (hvR : v.IsReal) :
    IsOpen (((Units.posSubgroup ℝ).comap
      (Units.map ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom)
        : v.Completionˣ →* ℝˣ)) : Set v.Completionˣ) := by
  have hcont : Continuous fun u : v.Completionˣ =>
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal hvR) (u : v.Completion) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hvR).continuous.comp
      Units.continuous_val
  have hset : (((Units.posSubgroup ℝ).comap
      (Units.map ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom)
        : v.Completionˣ →* ℝˣ)) : Set v.Completionˣ)
      = {u : v.Completionˣ |
          0 < (InfinitePlace.Completion.extensionEmbeddingOfIsReal hvR) (u : v.Completion)} := by
    ext u
    simp [Units.mem_posSubgroup]
  rw [hset]
  exact isOpen_Ioi.preimage hcont

/-- The preimage of the positive units of `ℝˣ` under `K_vˣ ≅ ℝˣ` lies in the norm group when
`v` is real and `w` is complex. -/
theorem posSubgroup_comap_le_localNormInfinite_range_of_real_complex {v : InfinitePlace K}
    {w : InfinitePlace L} [hw : w.LiesOver v] (hvR : v.IsReal) (hwC : w.IsComplex) :
    (Units.posSubgroup ℝ).comap
      (Units.map ((InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom)
        : v.Completionˣ →* ℝˣ)
      ≤ (NK.GlobalCFT.Place.localNormInfinite w v).range := by
  rw [show NK.GlobalCFT.Place.localNormInfinite w v
      = Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl]
  exact localNormInfinite_posSubgroup_le_range_of_real_complex hvR hwC

/-! ### The main statement -/

/-- **An open subgroup of `K_vˣ` inside the local norm group at an archimedean place.**

For a finite extension `L / K` of number fields and an infinite place `w` of `L` over the infinite
place `v` of `K`, the local norm `N_{L_w/K_v} : L_wˣ →* K_vˣ` has an open image, so it contains an
open subgroup. -/
theorem exists_isOpen_subgroup_le_localNormInfinite_range {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K) [w.LiesOver v] :
    ∃ A : Subgroup ((v.Completion)ˣ), IsOpen (A : Set ((v.Completion)ˣ)) ∧
      A ≤ (NK.GlobalCFT.Place.localNormInfinite w v).range := by
  rcases v.isReal_or_isComplex with hvR | hvC
  · rcases w.isReal_or_isComplex with hwR | hwC
    · refine ⟨⊤, isOpen_univ, ?_⟩
      rw [show NK.GlobalCFT.Place.localNormInfinite w v
          = Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl,
        localNormInfinite_range_eq_top_of_real_real hvR hwR]
    · exact ⟨_, isOpen_posSubgroup_comap v hvR,
        posSubgroup_comap_le_localNormInfinite_range_of_real_complex hvR hwC⟩
  · have hwC : w.IsComplex := InfinitePlace.LiesOver.isComplex_of_isComplex_under w hvC
    refine ⟨⊤, isOpen_univ, ?_⟩
    rw [show NK.GlobalCFT.Place.localNormInfinite w v
        = Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion) from rfl,
      localNormInfinite_range_eq_top_of_complex_complex hvC hwC]

end NK.NUV2.ArtinBridge
