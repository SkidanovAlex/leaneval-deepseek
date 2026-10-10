import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.NUV2.ARL.unifUnit_pow_mem_localNormSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The infinite places of a cyclotomic extension `K(ζ_q)` are complex (`q > 2`)

For `q > 2` and `L = K(ζ_q)`, no place of `L` is real: a real place would give a ring homomorphism
`ψ : L →+* ℝ`, and `ψ(ζ_q)` would be a real `q`-th root of unity, i.e. `±1`; but `ζ_q ≠ ±1` for
`q > 2` (`ζ_q = -1` would force `q ∣ 2`).

Consequently, for `q > 2`, every place of `L` above a real place `v` of `K` is complex, so the
local norm `N_{L_w/K_v}` is the norm `ℂˣ → ℝˣ`, `z ↦ z z̄ = |z|²`, with image the positive reals.
This is the archimedean input of step L3 of `Submission/Work/CFTLib/HR/STATUS.md` (the case
`v₀` real) and of the archimedean places in L7 there; the companion statements
`NK.CFTLib.Arl.posAtReal_localNormInfinite` (a local norm is positive) and
`NK.NUV2.ArtinBridge.posSubgroup_comap_le_localNormInfinite_range_of_real_complex` (every positive
real is a local norm) are both on disk, so together they identify the local norm group at a real
place with `{x | x > 0}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField
open NumberField

noncomputable section

namespace NK.NUV2.ARL

/-- **Every infinite place of `K(ζ_q)` is complex, for `q > 2`.** -/
theorem isComplex_infinitePlace_of_isCyclotomic {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {q : ℕ} [NeZero q] (hq : 2 < q)
    [IsCyclotomicExtension {q} K L] (w : InfinitePlace L) : w.IsComplex := by
  rcases w.isReal_or_isComplex with hw | hw
  · exfalso
    have hφR : ComplexEmbedding.IsReal w.embedding := (InfinitePlace.isReal_iff).mp hw
    set ψ : L →+* ℝ := hφR.embedding with hψ
    have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta q K L) q :=
      IsCyclotomicExtension.zeta_spec q K L
    have h1 : ψ (IsCyclotomicExtension.zeta q K L) ^ q = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    have habs : |ψ (IsCyclotomicExtension.zeta q K L)| = 1 := by
      refine (pow_eq_one_iff_of_nonneg (abs_nonneg _) (by omega : q ≠ 0)).mp ?_
      rw [← abs_pow, h1, abs_one]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
    · have hz : IsCyclotomicExtension.zeta q K L = 1 := ψ.injective (by rw [h, map_one])
      exact hζ.ne_one (by omega) hz
    · have hz : IsCyclotomicExtension.zeta q K L = -1 :=
        ψ.injective (by rw [h, map_neg, map_one])
      have h2 : (IsCyclotomicExtension.zeta q K L) ^ 2 = 1 := by rw [hz]; ring
      have hdvd : q ∣ 2 := (hζ.pow_eq_one_iff_dvd 2).mp h2
      exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
  · exact hw

/-- **The local norm group at a real place of a cyclotomic prime level is the set of positive
elements.**

For `L = K(ζ_q)` with `q > 2` every place of `L` above a real place `w` of `K` is complex
(`isComplex_infinitePlace_of_isCyclotomic`), so the local norm at such a place is the norm
`ℂˣ → ℝˣ`, `z ↦ z z̄ = |z|²`; its image in `w.Completionˣ ≅ ℝˣ` is exactly the subgroup of positive
elements.  (`posAtReal_localNormInfinite` gives one inclusion,
`posSubgroup_comap_le_localNormInfinite_range_of_real_complex` the other.)

This is the archimedean companion of
`NK.NUV2.ARL.mem_localNormSubgroup_ofFinite_iff_inertiaDeg_dvd`, and is what step L3 of
`Submission/Work/CFTLib/HR/STATUS.md` needs at a real place `v₀`. -/
theorem mem_localNormSubgroup_ofInfinite_iff_pos {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {q : ℕ} [NeZero q] (hq : 2 < q)
    [IsCyclotomicExtension {q} K L] (w : InfinitePlace K) (hw : w.IsReal)
    (x : (w.Completion)ˣ) :
    x ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
        (NK.GlobalCFT.Place.ofInfinite w) ↔ NK.CFTLib.Arl.PosAtReal w x := by
  classical
  classical
  haveI : IsGalois K L := IsCyclotomicExtension.isGalois {q} K L
  obtain ⟨W, hW⟩ := InfinitePlace.comap_surjective (K := L) w
  have hlies : W.LiesOver w := (NK.GlobalCFT.Norm.liesOver_iff_comap_eq W w).mpr hW
  have hcompl : W.IsComplex := isComplex_infinitePlace_of_isCyclotomic (K := K) hq W
  -- the local norm subgroup is the range of the local norm at the single place `W`
  have hsup : NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofInfinite w) =
      (@NK.GlobalCFT.Place.localNormInfinite K _ L _ _ W w hlies).range := by
    rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofInfinite]
    refine le_antisymm (iSup_le fun (w' : {w' : InfinitePlace L // w'.LiesOver w}) => ?_)
      (le_iSup_of_le ⟨W, hlies⟩ le_rfl)
    haveI : w'.1.LiesOver w := w'.2
    rw [NK.CFTLib.IdeleHasse.range_localNormInfinite_of_real_complex (w := w) (w' := w'.1)
        hw (isComplex_infinitePlace_of_isCyclotomic (K := K) hq w'.1),
      NK.CFTLib.IdeleHasse.range_localNormInfinite_of_real_complex (w := w) (w' := W) hw hcompl]
  rw [hsup, NK.CFTLib.IdeleHasse.range_localNormInfinite_of_real_complex (w := w) (w' := W)
    hw hcompl]
  constructor
  · intro hx hw'
    rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map] at hx
    have h : hw' = hw := Subsingleton.elim _ _
    rw [h]
    change 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (x : w.Completion)
    exact hx
  · intro hx
    rw [Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
    change 0 < (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (x : w.Completion)
    exact hx hw

end NK.NUV2.ARL
