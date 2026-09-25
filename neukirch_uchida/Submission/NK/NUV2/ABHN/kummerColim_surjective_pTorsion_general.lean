/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Surjectivity of the Kummer map on the colimits onto the `p`-torsion, for an arbitrary subgroup

`Submission/Work/NUV2/ABHN/kummerColim_surjective_pTorsion.lean` proves
`NK.NUV2.ABHN.kummerColim_surjective_pTorsion`: the Kummer map on the colimits

`kummerColim p ⊤ : MuColim p ⊤ → H2Units ⊤`

is surjective onto the `p`-torsion, over a characteristic-zero field `K` with separable closure
`K'` and for a prime `p`.  Its proof is a pure cocycle computation on the finite Galois levels,
and *nothing* in it uses that the subgroup defining the level groups is the full group
`Gal(K'/K)`.  This file records that the statement therefore holds for an **arbitrary** subgroup
`V ≤ Gal(K'/K)`:

`kummerColim p V : MuColim p V → H2Units V` is surjective onto the `p`-torsion.

Concretely, the level-wise construction

**(★)** for `y : H²(LevelGroup V M, Mˣ)` with `p • y = 0` there are a finite Galois level
`L ≥ M` and a class `w : H²(LevelGroup V L, μ_p(L))` with `kummerLevel p V L w = (unitsLevelMap) y`

is `exists_muClass_kummerLevel_eq_of_subgroup` below, copied from `exists_muClass_kummerLevel_eq`
with `⊤` replaced by the arbitrary subgroup `V` (`V` may even be non-closed: the level groups
`V/(V ∩ Gal(K'/L))` are finite for every finite level, and no Galois-theoretic hypothesis on `V`
is used).  The colimit statement then follows from the normal form for the representatives
(`LevelSystem.ofLevel_eq_iff`) exactly as in the `⊤` case.

This is the form in which the ABHN development consumes the Kummer identification for a
*decomposition group* `V = D_A` (and its intersections), which is where the local Brauer group
`H²(D_A, K'ˣ)` enters.
-/

import Mathlib
import Submission.NK.NUV2.ABHN.kummerColim_surjective_pTorsion
import Submission.NK.HassePrinciple.MuColimit
import Submission.NK.HassePrinciple.KummerLevel
import Submission.NK.HassePrinciple.kummerColim_injective
import Submission.NK.NUV2.ABHN.LocalBrauerAux

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.NUV2.ABHN

open NK.HassePrinciple
open NK.BrauerHasse

variable {K K' : Type u} [Field K] [CharZero K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **Surjectivity of the level-wise Kummer map onto the `p`-torsion, after enlarging the level,
for an arbitrary subgroup `V`.**

Let `y` be a class of `H²(LevelGroup V M, Mˣ)` killed by `p`.  Then there are a finite Galois
level `L ≥ M` and a class `w` of `H²(LevelGroup V L, μ_p(L))` whose Kummer image is the inflation
of `y` to `L`. -/
lemma exists_muClass_kummerLevel_eq_of_subgroup (p : ℕ) (hp : p.Prime)
    (V : Subgroup Gal(K'/K))
    (M : FiniteGaloisIntermediateField K K')
    (y : UnitsLevelH2 V M) (hpy : p • y = 0) :
    ∃ (L : FiniteGaloisIntermediateField K K') (hML : M ≤ L)
      (w : (muLevelSystem p V).obj L),
      (kummerLevel p V L) w = (unitsLevelSystem V).map hML y := by
  classical
  -- ## Step 1: a cocycle `c` representing `y` and a cochain `βm` with `d₁₂ βm = p • c`
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective
      (groupCohomology.H2π (unitsLevelRep V M))).1 inferInstance y
  have hpc : (groupCohomology.H2π (unitsLevelRep V M)) (p • c) = 0 := by
    rw [map_nsmul, hc]
    exact hpy
  obtain ⟨βm, hβm⟩ :=
    exists_mul_cochain_of_H2π_eq_zero V M (p • c) hpc
  let cfun : LevelGroup V M × LevelGroup V M →
      Additive (↥M)ˣ := fun gh => c gh
  -- multiplicative form of the relation `d₁₂ βm = p • c`
  have hrel : ∀ g h : LevelGroup V M,
      (levelGroupRestrictHom V M g) • βm h / βm (g * h) * βm g
        = (cfun (g, h)).toMul ^ p := by
    intro g h
    have h2 : (groupCohomology.d₁₂ (unitsLevelRep V M)).hom
          (fun g => Additive.ofMul (βm g)) (g, h) = (p • c) (g, h) := congrFun hβm (g, h)
    have h3 : Additive.ofMul
        ((levelGroupRestrictHom V M g) • βm h / βm (g * h) * βm g)
        = (p • c) (g, h) := by
      rw [← h2]
      rfl
    have h4 : (p • c) (g, h) = Additive.ofMul ((cfun (g, h)).toMul ^ p) :=
      (show (p • c) (g, h) = p • cfun (g, h) from rfl).trans
        (ofMul_pow p ((cfun (g, h)).toMul)).symm
    exact Additive.ofMul.injective (h3.trans h4)
  -- ## Step 2: `p`-th roots of the values of `βm` in the separably closed `K'`
  haveI : IsSepClosed K' := IsSepClosure.sep_closed K
  haveI hNe : NeZero (p : K') := ⟨by
    intro h0
    have h1 : algebraMap K K' (p : K) = 0 := by rw [map_natCast, h0]
    have h2 : (p : K) = 0 := (algebraMap K K').injective (by simpa using h1)
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) h2⟩
  choose root hroot using fun g : LevelGroup V M =>
    IsSepClosed.exists_pow_nat_eq (k := K')
      (((βm g : (↥M)ˣ) : ↥M) : K') p
  have hroot_ne : ∀ g : LevelGroup V M, root g ≠ 0 := by
    intro g h0
    have h1 : (((βm g : (↥M)ˣ) : ↥M) : K') = 0 := by
      rw [← hroot g, h0, zero_pow hp.ne_zero]
    exact Units.ne_zero (βm g) (Subtype.ext h1)
  let uroot : LevelGroup V M → K'ˣ :=
    fun g => Units.mk0 (root g) (hroot_ne g)
  have huroot_pow : ∀ g, uroot g ^ p
      = Units.map (IntermediateField.val (K := K) (L := K') M).toMonoidHom (βm g) := by
    intro g
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hroot g
  -- ## Step 3: the level `L` generated by `M` and the chosen `p`-th roots
  let a' : LevelGroup V M → K' := fun g => ((uroot g : K'ˣ) : K')
  haveI hfin : Finite (Set.range a') := Set.finite_range a'
  let L : FiniteGaloisIntermediateField K K' :=
    FiniteGaloisIntermediateField.adjoin K (Set.range a') ⊔ M
  have hML : M ≤ L := le_sup_right
  have hmemL : ∀ g, a' g ∈ (L : IntermediateField K K') := by
    intro g
    have h1 : a' g ∈ (FiniteGaloisIntermediateField.adjoin K (Set.range a') :
        IntermediateField K K') :=
      FiniteGaloisIntermediateField.subset_adjoin K (Set.range a') ⟨g, rfl⟩
    exact (show (FiniteGaloisIntermediateField.adjoin K (Set.range a') :
        IntermediateField K K') ≤ (L : IntermediateField K K') from le_sup_left) h1
  -- ## Step 4: the cochain `g ↦ a_{π g}` on the bigger level
  let π : LevelGroup V L →* LevelGroup V M :=
    levelQuotHom (U := V) hML
  let aL : LevelGroup V L → (↥L)ˣ := fun g =>
    Units.mk0 ⟨a' (π g), hmemL (π g)⟩ (by
      intro h0
      exact hroot_ne (π g) (congrArg Subtype.val h0))
  let inclL : (↥L)ˣ →* K'ˣ :=
    Units.map (IntermediateField.val (K := K) (L := K') L).toMonoidHom
  have hvalL : ∀ g, inclL (aL g) = uroot (π g) := by
    intro g
    refine Units.ext ?_
    rfl
  have hinclL_inj : Function.Injective inclL := by
    intro u v huv
    refine Units.ext (Subtype.ext ?_)
    exact congrArg (fun w : K'ˣ => (w : K')) huv
  have haL_pow : ∀ g, aL g ^ p
      = Units.map (IntermediateField.inclusion hML).toMonoidHom (βm (π g)) := by
    intro g
    refine hinclL_inj ?_
    calc inclL (aL g ^ p) = inclL (aL g) ^ p := map_pow inclL (aL g) p
      _ = uroot (π g) ^ p := by rw [hvalL g]
      _ = Units.map (IntermediateField.val (K := K) (L := K') M).toMonoidHom (βm (π g)) :=
            huroot_pow (π g)
      _ = inclL (Units.map (IntermediateField.inclusion hML).toMonoidHom (βm (π g))) := by
            refine Units.ext ?_
            rfl
  have haL_smul_pow : ∀ g h : LevelGroup V L,
      (((levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L)) • aL h) ^ p
        = Units.map (IntermediateField.inclusion hML).toMonoidHom
            (((levelGroupRestrictHom V M (π g) : ↥M ≃ₐ[K] ↥M))
              • βm (π h)) := by
    intro g h
    have hcompat := unitsLevelRestrictCompat V hML g (βm (π h))
    rw [AlgEquiv.smul_units_def, AlgEquiv.smul_units_def] at hcompat
    rw [AlgEquiv.smul_units_def, ← map_pow, haL_pow h]
    exact hcompat.symm
  -- ## Step 5: the difference of the two cocycles
  let z₁ : ↥(groupCohomology.cocycles₂ (unitsLevelRep V L)) :=
    groupCohomology.mapCocycles₂ π (unitsLevelMapCoeff V hML) c
  let dβ : LevelGroup V L × LevelGroup V L →
      Additive (↥L)ˣ :=
    (groupCohomology.d₁₂ (unitsLevelRep V L)).hom
      (fun g => Additive.ofMul (aL g))
  have hdβ_mem : dβ ∈ groupCohomology.cocycles₂ (unitsLevelRep V L) :=
    groupCohomology.coboundaries₂_le_cocycles₂ _
      (show dβ ∈ groupCohomology.coboundaries₂ (unitsLevelRep V L) from
        ⟨(fun g => Additive.ofMul (aL g)), rfl⟩)
  let z₂ : ↥(groupCohomology.cocycles₂ (unitsLevelRep V L)) :=
    ⟨dβ, hdβ_mem⟩
  let zz : ↥(groupCohomology.cocycles₂ (unitsLevelRep V L)) := z₁ - z₂
  let z₁fun : LevelGroup V L × LevelGroup V L →
      Additive (↥L)ˣ := fun gh => z₁ gh
  let zzfun : LevelGroup V L × LevelGroup V L →
      Additive (↥L)ˣ := fun gh => zz gh
  have hz₁_val : ∀ g h, z₁ (g, h) = Additive.ofMul
      (Units.map (IntermediateField.inclusion hML).toMonoidHom ((cfun (π g, π h)).toMul)) := by
    intro g h
    show (unitsLevelMapCoeff V hML) (cfun (π g, π h))
      = Additive.ofMul (Units.map (IntermediateField.inclusion hML).toMonoidHom
          ((cfun (π g, π h)).toMul))
    rfl
  have hdβ_val : ∀ g h, dβ (g, h) = Additive.ofMul
      (((levelGroupRestrictHom V L g : ↥L ≃ₐ[K] ↥L)) • aL h
        / aL (g * h) * aL g) := fun g h => rfl
  have hzz_val : ∀ g h, zzfun (g, h) = z₁fun (g, h) - dβ (g, h) := by
    intro g h
    show (z₁ - z₂) (g, h) = z₁fun (g, h) - dβ (g, h)
    rfl
  have hzz_pow : ∀ g h, (zzfun (g, h)).toMul ^ p = 1 := by
    intro g h
    have h1 : (zzfun (g, h)).toMul = (z₁fun (g, h)).toMul / (dβ (g, h)).toMul := by
      rw [hzz_val]
      exact toMul_sub _ _
    have hz1p : (z₁fun (g, h)).toMul ^ p
        = Units.map (IntermediateField.inclusion hML).toMonoidHom
            ((cfun (π g, π h)).toMul ^ p) := by
      rw [show z₁fun (g, h) = z₁ (g, h) from rfl, hz₁_val g h, toMul_ofMul, map_pow]
    have hdβp : (dβ (g, h)).toMul ^ p
        = Units.map (IntermediateField.inclusion hML).toMonoidHom
            ((cfun (π g, π h)).toMul ^ p) := by
      rw [hdβ_val g h, toMul_ofMul, mul_pow, div_pow, haL_smul_pow g h, haL_pow (g * h),
        haL_pow g, ← map_div, ← map_mul, map_mul π g h, hrel (π g) (π h)]
    rw [h1, div_pow, hdβp, hz1p]
    simp
  -- ## Step 6: the `μ_p`-valued cocycle and its Kummer class
  have hzz_exists : ∀ gh : LevelGroup V L ×
      LevelGroup V L,
      ∃ u : (↥L)ˣ, zz gh = Additive.ofMul u ∧ u ^ p = 1 := by
    intro gh
    obtain ⟨g, h⟩ := gh
    exact ⟨(zzfun (g, h)).toMul, (ofMul_toMul (zzfun (g, h))).symm, hzz_pow g h⟩
  obtain ⟨w₀, hw⟩ := exists_muCocycle_of_unitsCocycle p V L zz hzz_exists
  refine ⟨L, hML, (groupCohomology.H2π (muLevelRep p V L)) w₀, ?_⟩
  have hz₂_zero : (groupCohomology.H2π (unitsLevelRep V L)) z₂ = 0 :=
    (groupCohomology.H2π_eq_zero_iff z₂).mpr ⟨(fun g => Additive.ofMul (aL g)), rfl⟩
  have hz₁_class : (groupCohomology.H2π (unitsLevelRep V L)) z₁
      = (unitsLevelMap V hML) y := by
    refine (groupCohomology.H2π_comp_map_apply π
      (unitsLevelMapCoeff V hML) c).symm.trans ?_
    rw [hc]
    rfl
  rw [show (kummerLevel p V L)
      = groupCohomology.map (MonoidHom.id (LevelGroup V L))
          (muToUnits p V L) 2 from rfl,
    groupCohomology.H2π_comp_map_apply, hw,
    show zz = z₁ - z₂ from rfl, map_sub, hz₁_class, hz₂_zero, sub_zero]
  rfl

/-- **The image of the Kummer map on the colimits is exactly the `p`-torsion of the units colimit,
for an arbitrary subgroup `V ≤ Gal(K'/K)`.**

Let `K` be a field of characteristic `0`, `K'` a separable closure of `K`, and `p` a prime.  An
element `x` of the units colimit `H2Units V = colim_L H²(LevelGroup V L, Lˣ)` (over the finite
Galois intermediate fields `L` of `K'/K`) that is killed by `p` is the image of a class of the
`μ_p`-colimit `MuColim p V = colim_L H²(LevelGroup V L, μ_p(L))` under the Kummer map
`kummerColim p V`.

This is the exactness of the Kummer sequence `1 → μ_p → K̄ˣ → K̄ˣ → 1` *in the limit* (the units
of the separably closed `K'` are `p`-divisible because `CharZero K'`), at the level of the
cohomology of the subgroup `V`. -/
theorem kummerColim_surjective_pTorsion_general {K K' : Type} [Field K] [CharZero K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (hp : p.Prime) (V : Subgroup Gal(K'/K))
    (x : NK.HassePrinciple.H2Units V) (hx : p • x = 0) :
    ∃ y : NK.HassePrinciple.MuColim p V, NK.HassePrinciple.kummerColim p V y = x := by
  obtain ⟨M, y, hyM, hpy⟩ :=
    exists_level_representative_nsmul_eq_zero V p x hx
  obtain ⟨L, hML, w, hw⟩ := exists_muClass_kummerLevel_eq_of_subgroup p hp V M y hpy
  refine ⟨MuColim.ofLevel p V L w, ?_⟩
  have hgoal : kummerColim p V (MuColim.ofLevel p V L w)
      = (unitsLevelSystem V).ofLevel L ((kummerLevel p V L) w) :=
    kummerColim_ofLevel p V L w
  rw [hgoal, hw]
  exact ((unitsLevelSystem V).ofLevel_map hML y).trans hyM

end NK.NUV2.ABHN
