import Mathlib
import Submission.NK.CFTLib.IdeleHasse.CyclRat.Defs
import Submission.NK.CFTLib.IdeleHasse.localFaithfulDefs
import Submission.NK.CFTLib.IdeleHasse.onePlace_localNorm
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists
import Submission.NK.GlobalCFTdeep.NormIndex.localNorm_finiteIndex_archimedean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.IdeleHasse

open NumberField

/-! ### Auxiliary lemmas -/

/-- The archimedean completion of a number field over `ℚ`, transported to `ℝ` along
`InfinitePlace.Completion.ringEquivRealOfIsReal`, sends the image of a rational number to that
rational number: the composite is the canonical embedding `ℚ →+* ℝ`. -/
theorem ratCast_ringEquivRealOfIsReal_algebraMap {K : Type} [Field K] [NumberField K]
    {v : InfinitePlace K} (hv : v.IsReal) (q : ℚ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hv (algebraMap ℚ v.Completion q) = (q : ℝ) := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  simp

/-- **A field containing a primitive `m`-th root of unity with `m ≥ 3` is totally complex.**

Indeed, if `w` were a real place of the number field `L`, then `w.embedding_of_isReal` would send
`ζ` to a real number `x` with `x ^ m = 1`; over `ℝ` that forces `x = 1` or `x = -1`
(`pow_eq_pow_iff_of_ne_zero`), hence `ζ ^ 2 = 1`, contradicting the primitivity of `ζ` and
`m ≥ 3`. -/
theorem isTotallyComplex_of_primitiveRoot {m : ℕ} (hm : 3 ≤ m) {L : Type} [Field L]
    [NumberField L] (ζ : L) (hζ : IsPrimitiveRoot ζ m) : IsTotallyComplex L := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hwR
  obtain ⟨x, hx⟩ : ∃ x : ℝ, w.embedding ζ = (x : ℂ) :=
    ⟨w.embedding_of_isReal hwR ζ, by simp⟩
  have hzm : (w.embedding ζ) ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hxm : x ^ m = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow, Complex.ofReal_one, ← hx]
    exact hzm
  have hx2 : x ^ 2 = 1 := by
    rcases (pow_eq_pow_iff_of_ne_zero (a := x) (b := 1) (n := m) (by omega)).mp
      (by rw [one_pow]; exact hxm) with h | ⟨h, -⟩
    · rw [h]; norm_num
    · rw [h]; norm_num
  have hz2 : (w.embedding ζ) ^ 2 = 1 := by
    rw [hx, ← Complex.ofReal_pow, hx2, Complex.ofReal_one]
  have hζ2 : ζ ^ 2 = 1 := w.embedding.injective (by rw [map_pow, map_one, hz2])
  have hdv : m ∣ 2 := (hζ.pow_eq_one_iff_dvd 2).mp hζ2
  have hle : m ≤ 2 := Nat.le_of_dvd (by norm_num) hdv
  omega

/-- **The local norm group of `ℚ(ζ_m)` at the archimedean place**, for `m ≥ 3`.

For `m ≥ 3` the field `ℚ(ζ_m)` is totally imaginary, so at the (unique) archimedean place of `ℚ`
the local extension is `ℂ/ℝ`, whose norm is `z ↦ z·z̄ = |z|²`, with image the positive reals.
Hence the one-place idèle at `∞` with value the image of `a ∈ ℚˣ` is an idèle norm exactly when
`a > 0`.

Available: `NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff` (the one-place dictionary) and the
archimedean local norm lemmas in
`Submission/Work/GlobalCFTdeep/NormIndex/localNorm_finiteIndex_archimedean.lean`
(`localNormInfinite_posSubgroup_le_range_of_real_complex`,
`localNormInfinite_norm_eq_real_complex`) plus
`NK.CFTLib.IdeleHasse.localNormSubgroup_eq_posSubgroup_comap`. -/
theorem cyclotomicLocalNorm_infinite
    (m : ℕ) (hm : 3 ≤ m) {L : Type} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L] [IsCyclotomicExtension {m} ℚ L]
    (w : NumberField.InfinitePlace ℚ) (a : ℚˣ) :
    NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofInfinite w)
        (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) a) ∈
      NK.GlobalCFT.Idele.normImage ℚ L ↔ 0 < (a : ℚ) := by
  -- `ℚ(ζ_m)` contains a primitive `m`-th root of unity, hence is totally complex for `m ≥ 3`.
  haveI : NeZero m := ⟨by omega⟩
  have hcyclo : IsCyclotomicExtension {m} ℚ L := by infer_instance
  obtain ⟨hroot, -⟩ := hcyclo
  obtain ⟨ζ, hζ⟩ := hroot (n := m) (by simp) (by omega)
  haveI hTC : IsTotallyComplex L := isTotallyComplex_of_primitiveRoot hm ζ hζ
  -- The unique archimedean place of `ℚ` is real, and the archimedean places of `L` are complex.
  obtain ⟨w₀, hw₀⟩ :=
    NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := ℚ) (L := L) w
  have hvR : w.IsReal := IsTotallyReal.isReal w
  have hw₀C : w₀.IsComplex := IsTotallyComplex.isComplex w₀
  -- The local norm subgroup at `∞` is the positive subgroup of `ℝˣ ≅ ℚ_∞ˣ`.
  rw [NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff]
  rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_posSubgroup_comap hw₀ hvR hw₀C]
  rw [Subgroup.mem_comap, Units.mem_posSubgroup]
  -- The value of `a` under the identification `ℚ_∞ ≅ ℝ` is the rational number `a` itself.
  have hval : ((Units.map
      (InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv.toMonoidHom)
      (NK.CFTLib.IdeleHasse.localImageAt (NK.GlobalCFT.Place.ofInfinite w) a) : ℝ)
      = (a : ℝ) := by
    rw [Units.coe_map, NK.CFTLib.IdeleHasse.localImageAt, Units.coe_map]
    exact ratCast_ringEquivRealOfIsReal_algebraMap hvR (a : ℚ)
  rw [hval, Rat.cast_pos]

end NK.CFTLib.IdeleHasse
