import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.Work.SSGRoute.phi1_level_naturality

/-!
# Plumbing: `IsScalarTower` and finiteness across a non-linear tower

Auxiliary facts about a tower of fields `k ⊆ k' ⊆ K` and the transfers of finiteness along it.
They are used in the proof of `Work.SSGRoute.exists_galoisClosure_level` below.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField

namespace Work.SSGRoute

/-- If `k → k' → K` is a compatible tower of algebras, then so is `k → K → ·`: the `k`-algebra
structure on `K` factors through `k'`. -/
private theorem isScalarTower_of_tower {k k' K L : Type} [Field k] [Field k'] [Field K] [Field L]
    [Algebra k k'] [Algebra k K] [Algebra k' K] [Algebra k L] [Algebra k' L] [Algebra K L]
    [IsScalarTower k k' K] [IsScalarTower k k' L] [IsScalarTower k' K L] :
    IsScalarTower k K L := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  calc algebraMap k L x = algebraMap k' L (algebraMap k k' x) :=
        IsScalarTower.algebraMap_apply k k' L x
    _ = algebraMap K L (algebraMap k' K (algebraMap k k' x)) :=
        IsScalarTower.algebraMap_apply k' K L _
    _ = algebraMap K L (algebraMap k K x) := by
        rw [IsScalarTower.algebraMap_apply k k' K x]

/-- `k'` is finite over `k` when `K` is finite over `k` and over `k'`, in the tower
`k ⊆ k' ⊆ K`. -/
private theorem finiteDimensional_of_isScalarTower {k k' K : Type} [Field k] [Field k'] [Field K]
    [Algebra k k'] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K]
    [FiniteDimensional k K] : FiniteDimensional k k' := by
  have h := Module.finrank_mul_finrank k k' K
  have hpos : 0 < Module.finrank k k' * Module.finrank k' K := by
    rw [h]; exact Module.finrank_pos
  exact FiniteDimensional.of_finrank_pos (Nat.pos_of_mul_pos_right hpos)

/-- **The Galois closure of a `k'`-level over `k`, with a place above the given place.**

For `k ⊆ k' ⊆ K` with `K/k` and `K/k'` finite Galois, and `L/k'` a finite Galois extension with
`K ⊆ L` (so `k ⊆ k' ⊆ K ⊆ L`), every place `w'` of `L` lying over a place `w` of `K` extends to a
finite **Galois** extension `Lc ⊇ L` of `k`, carrying compatible `k`, `k'`, `K`, `L`-algebra
structures and the corresponding `IsScalarTower`s, with `Lc/k` and `Lc/k'` finite Galois, together
with a place `wc` of `Lc` lying over `w'` (and hence, by transitivity, over `w`).

This closes the last gap in Z8's step 2 (the transport).  The level `L` of a `k'`-level datum need
not be Galois over `k`, whereas `Work.SSGRoute.levelPair_baseChange` (Y3) — relating the `k'`-level
pairing of the base-changed class to the `k`-level pairing of the original — *requires* both
`IsGalois k L` and `IsGalois k' L`.  Passing to this closure is what lets
`Work.SSGRoute.vanishesAbove_base` (the target's hypothesis, at `k`-levels) be applied;
`Work.SSGRoute.levelPair_comp_extHMap` (Z1) together with
`Work.SSGRoute.localUnits_infl_injective` (Z2) then push the vanishing back down from `Lc` to `L`.

The mathematical content is standard: `Lc` is the Galois closure of the compositum `K·L` over `k`
(inside a fixed algebraic closure), and `wc` exists by the lying-over principle for a valuation
extending `w'` (its nonarchimedean half is `Commons…exists_heightOneSpectrum_liesOver`).  The tooling
for the level-realisation half is
`Commons.NumberTheory.NumberField.Completion.exists_galois_realization` (Krasner) and
`Work.SSGRoute.PT.e3_exists_level_of_galois`.

Notes from the review.  (i) `[Algebra k L]` and `[IsScalarTower k k' L]` are *not* optional: without
them `SMul k L` is unavailable and the tower fields of the conclusion cannot be stated — the exact
cause of the `synthInstanceFailed` recorded in
`Submission/Work/SSGRoute/local_duality_ext_detect_levels.lean`.  (ii) The final conjunct
`LiesOver wc w` is *implied* by `LiesOver wc w'` together with `hw'` (transitivity of `LiesOver`,
available in the tree as `Work.SSGRoute.place_liesOver_trans`), and `IsGalois k' Lc` follows from
`IsGalois k Lc` by `IsGalois.tower_top_of_isGalois`; both are redundant but harmless, and a prover may
use those two results freely.  The conclusion returns only the *data* (the instance fields plus the
two place facts), in the same shape as `Work.SSGRoute.exists_level_quotientNorm_avoids`, whose
consumers re-`letI` the instance fields.  The statement was elaborated locally against
`Submission.Work.SSGRoute.PTDefs` and again in review. -/
theorem exists_galoisClosure_level (k k' K : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Algebra k K] [Algebra k' K] [Algebra k k']
    [IsScalarTower k k' K] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k' K]
    [IsGalois k' K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra k' L] [Algebra K L]
    [IsScalarTower k k' L] [IsScalarTower k' K L] [FiniteDimensional k' L] [IsGalois k' L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w) :
    ∃ (Lc : Type) (_ : Field Lc) (_ : NumberField Lc) (_ : Algebra k Lc) (_ : Algebra k' Lc)
      (_ : Algebra K Lc) (_ : Algebra L Lc) (_ : FiniteDimensional L Lc)
      (_ : IsScalarTower k k' Lc) (_ : IsScalarTower k K Lc) (_ : IsScalarTower k' K Lc)
      (_ : IsScalarTower k L Lc) (_ : IsScalarTower k' L Lc) (_ : IsScalarTower K L Lc)
      (_ : FiniteDimensional k Lc) (_ : FiniteDimensional k' Lc) (_ : IsGalois k Lc)
      (_ : IsGalois k' Lc)
      (wc : NK.GlobalCFT.Place Lc) (hc : NK.GlobalCFT.Place.LiesOver wc w'),
      NK.GlobalCFT.Place.LiesOver wc w := by
  classical
  -- ## Step 0: the tower `k ⊆ k' ⊆ K ⊆ L` in the `k`-direction, and finiteness of its pieces.
  haveI hSTkKL : IsScalarTower k K L :=
    isScalarTower_of_tower (k := k) (k' := k') (K := K) (L := L)
  haveI hfinkk' : FiniteDimensional k k' :=
    finiteDimensional_of_isScalarTower (k := k) (k' := k') (K := K)
  haveI hfinkL : FiniteDimensional k L := FiniteDimensional.trans k k' L
  haveI hfinKL : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite k' K L
  -- ## Step 1: work inside `Ω = AlgebraicClosure L`, the ambient algebraically closed field.
  let Ω := AlgebraicClosure L
  -- The image of `L` in `Ω` is the intermediate field `M`, and `N ≥ M` is its normal (Galois)
  -- closure over `k`; `N` contains the image of `K` because `K ⊆ L`.
  let e : L →ₐ[k] Ω := IsScalarTower.toAlgHom k L Ω
  let M : IntermediateField k Ω := e.fieldRange
  haveI hMfin : FiniteDimensional k ↥M :=
    Module.Finite.equiv (AlgHom.equivFieldRange e).toLinearEquiv
  let N : IntermediateField k Ω := IntermediateField.normalClosure k ↥M Ω
  haveI hNfin : FiniteDimensional k ↥N := normalClosure.is_finiteDimensional k ↥M Ω
  have hMN : M ≤ N := IntermediateField.le_normalClosure M
  haveI hMsalg : Algebra.IsAlgebraic k ↥M := Algebra.IsAlgebraic.of_finite k ↥M
  haveI hIN : IsNormalClosure k ↥M ↥N :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun _ => IsAlgClosed.splits _)
  haveI hNnorm : Normal k ↥N := hIN.normal
  haveI hNint : Algebra.IsIntegral k ↥N := Algebra.IsIntegral.of_finite k ↥N
  haveI hNsep : Algebra.IsSeparable k ↥N := Algebra.IsSeparable.of_integral k ↥N
  haveI hNgal : IsGalois k ↥N := isGalois_iff.mpr ⟨hNsep, hNnorm⟩
  -- The images of `L` and of `K` lie in `N`.
  have hLN : ∀ x : L, algebraMap L Ω x ∈ N := by
    intro x
    exact hMN (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  have hk'N : ∀ x : k', algebraMap k' Ω x ∈ N := by
    intro x
    rw [IsScalarTower.algebraMap_apply k' L Ω x]
    exact hLN _
  have hKN : ∀ x : K, algebraMap K Ω x ∈ N := by
    intro x
    rw [IsScalarTower.algebraMap_apply K L Ω x]
    exact hLN _
  -- ## Step 2: the `k'`-, `K`- and `L`-algebra structures on `↥N` (canonical maps through `Ω`).
  let fk' : k' →ₐ[k] ↥N :=
    { toFun := fun x => ⟨algebraMap k' Ω x, hk'N x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b)
      commutes' := fun a => Subtype.ext (IsScalarTower.algebraMap_apply k k' Ω a).symm }
  let fK : K →ₐ[k] ↥N :=
    { toFun := fun x => ⟨algebraMap K Ω x, hKN x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b)
      commutes' := fun a => Subtype.ext (IsScalarTower.algebraMap_apply k K Ω a).symm }
  let fL : L →ₐ[k] ↥N :=
    { toFun := fun x => ⟨algebraMap L Ω x, hLN x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ a b)
      commutes' := fun a => Subtype.ext (IsScalarTower.algebraMap_apply k L Ω a).symm }
  letI algk' : Algebra k' ↥N := RingHom.toAlgebra fk'.toRingHom
  letI algK : Algebra K ↥N := RingHom.toAlgebra fK.toRingHom
  letI algL : Algebra L ↥N := RingHom.toAlgebra fL.toRingHom
  -- ## Step 3: the six scalar towers.
  haveI tkk' : IsScalarTower k k' ↥N := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [RingHom.algebraMap_toAlgebra fk'.toRingHom]
    exact Subtype.ext (IsScalarTower.algebraMap_apply k k' Ω x)
  haveI tkK : IsScalarTower k K ↥N := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [RingHom.algebraMap_toAlgebra fK.toRingHom]
    exact Subtype.ext (IsScalarTower.algebraMap_apply k K Ω x)
  haveI tk'K : IsScalarTower k' K ↥N := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [RingHom.algebraMap_toAlgebra fk'.toRingHom, RingHom.algebraMap_toAlgebra fK.toRingHom]
    exact Subtype.ext (IsScalarTower.algebraMap_apply k' K Ω x)
  haveI tkL : IsScalarTower k L ↥N := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [RingHom.algebraMap_toAlgebra fL.toRingHom]
    exact Subtype.ext (IsScalarTower.algebraMap_apply k L Ω x)
  haveI tk'L : IsScalarTower k' L ↥N := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [RingHom.algebraMap_toAlgebra fk'.toRingHom, RingHom.algebraMap_toAlgebra fL.toRingHom]
    exact Subtype.ext (IsScalarTower.algebraMap_apply k' L Ω x)
  haveI tkL' : IsScalarTower K L ↥N := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [RingHom.algebraMap_toAlgebra fK.toRingHom, RingHom.algebraMap_toAlgebra fL.toRingHom]
    exact Subtype.ext (IsScalarTower.algebraMap_apply K L Ω x)
  -- ## Step 4: number field, finiteness and Galois properties of `↥N`.
  haveI : CharZero ↥N := inferInstance
  haveI hfinQ : FiniteDimensional ℚ ↥N := FiniteDimensional.trans ℚ k ↥N
  haveI hNF : NumberField ↥N := NumberField.mk
  haveI hfinL : FiniteDimensional L ↥N := by
    have h := Module.finrank_mul_finrank k L ↥N
    have hpos : 0 < Module.finrank k L * Module.finrank L ↥N := by
      rw [h]; exact Module.finrank_pos
    exact FiniteDimensional.of_finrank_pos (Nat.pos_of_mul_pos_left hpos)
  haveI hfin' : FiniteDimensional k' ↥N := Module.Finite.of_restrictScalars_finite k k' ↥N
  haveI hgal' : IsGalois k' ↥N := IsGalois.tower_top_of_isGalois k k' ↥N
  -- ## Step 5: a place `wc` of `↥N` above `w'`, hence (by transitivity through `L`) above `w`.
  obtain ⟨wc, hc⟩ := NK.GlobalCFTdeep.NormIndex.exists_place_liesOver (K := L) (L := ↥N) w'
  have htrans : NK.GlobalCFT.Place.LiesOver wc w :=
    place_liesOver_trans (K := K) (L := L) (M := ↥N) hc hw'
  exact ⟨↥N, inferInstance, hNF, inferInstance, algk', algK, algL, hfinL, tkk', tkK, tk'K,
    tkL, tk'L, tkL', hNfin, hfin', hNgal, hgal', wc, hc, htrans⟩

end Work.SSGRoute
