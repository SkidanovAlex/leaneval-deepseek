/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFT.Norm.globalCFT_localNorm_mem_localUnits
import Submission.NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.GlobalCFT.Norm.NormTransAux
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Openness of the norm subgroup `N_{L/K} C_L` of the idèle class group: the general part

This file contains the class-field-theory-free part of the proof that the norm subgroup
`N_{L/K} C_L` of the idèle class group is *open*.

## The mathematical argument

Let `L / K` be a finite extension of number fields.  The preimage of `N_{L/K} C_L ≤ C_K` under the
quotient map `𝕀 K → C_K` is `Kˣ · N_{L/K} 𝕀 L` (a subgroup of `𝕀 K`, since `𝕀 K` is abelian).
Hence `N_{L/K} C_L` is open as soon as `N_{L/K} 𝕀 L` contains an *open* subgroup `E` of `𝕀 K`: a
subgroup of `𝕀 K` containing an open subgroup is a union of translates of that subgroup, hence
open, and the image of an open subgroup of `𝕀 K` under the (open) quotient map is an open
subgroup of `C_K`.

The open subgroup is produced with the vocabulary of this file:

* `NK.NUV2.ArtinBridge.constrainedLoc S A` is the subgroup of idèles which lie in `A v` at the
  places of a finite set `S` and are local units outside `S`;
* it is open when every `A v` (`v ∈ S`) is open in `K_vˣ` (`isOpen_constrainedLoc`);
* `NK.NUV2.ArtinBridge.constrainedLoc_le_normImage` shows that `constrainedLoc S A` is contained
  in `N_{L/K} 𝕀 L` when `S` contains all the places at which the local norm is not surjective on
  units, and each `A v` is contained in the range of the local norm at `v`.

The local inputs needed for the second item are, for a *Galois* extension `L / K`:

* nonarchimedean places: `NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormFinite_range`
  (a neighbourhood of `1` inside the local norm group), from the explicit norm-theoretic argument
  of `Commons.NumberTheory.NumberField.Completion.finite_quotient_units_range_norm_adicCompletion`;
* archimedean places: `NK.NUV2.ArtinBridge.exists_isOpen_subgroup_le_localNormInfinite_range`;
* unramified finite places: `NK.NUV2.ArtinBridge.localUnits_le_image_localNormFinite_of_ramificationIdx_eq_one`
  (the local norm is surjective on units).

## Main results

* `NK.NUV2.ArtinBridge.isOpen_constrainedLoc`;
* `NK.NUV2.ArtinBridge.isOpen_normClassSubgroup_of_isOpen_le`;
* `NK.NUV2.ArtinBridge.isOpen_normClassSubgroup_of_localData`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT

/-! ### The idèle concentrated at a single place -/

section Single

/-- The idèle of `L` concentrated at the place `w` with value `u`, i.e. `u` at `w` and `1` at
every other place. -/
noncomputable def singleIdeleL {L : Type*} [Field L] [NumberField L] (w : Place L)
    (u : (Place.localField L w)ˣ) : 𝕀[L] := by
  classical
  refine RestrictedProduct.mk (fun w' => if h : w' = w then h ▸ u else 1) ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_singleton w) ?_
  intro w' hw'
  simp only [Set.mem_ofPred_eq] at hw'
  by_contra hmem
  have hne : w' ≠ w := fun h => hmem (by simpa using h)
  rw [dif_neg hne] at hw'
  exact hw' (Subgroup.one_mem _)

theorem singleIdeleL_apply_self {L : Type*} [Field L] [NumberField L] (w : Place L)
    (u : (Place.localField L w)ˣ) : singleIdeleL w u w = u := by
  classical
  show (if h : w = w then h ▸ u else 1) = u
  rw [dif_pos rfl]

theorem singleIdeleL_apply_of_ne {L : Type*} [Field L] [NumberField L] {w w' : Place L}
    (h : w' ≠ w) (u : (Place.localField L w)ˣ) : singleIdeleL w u w' = 1 := by
  classical
  show (if h : w' = w then h ▸ u else 1) = 1
  rw [dif_neg h]

end Single

/-! ### The norm of a concentrated idèle -/

section Bridge

/-- **Finite places.**  The idèlic norm of the idèle concentrated at a finite place `q` of `L`
above `Q`, evaluated at `Q`, is the local norm `N_{L_q/K_Q} u`. -/
theorem normIdeleFun_singleIdeleL_ofFinite {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (q : HeightOneSpectrum (𝓞 L))
    (Q : HeightOneSpectrum (𝓞 K)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (u : (q.adicCompletion L)ˣ) :
    Idele.normIdeleFun K L (singleIdeleL (Place.ofFinite q) u) (Place.ofFinite Q) =
      Place.localNormFinite q Q hq u := by
  classical
  rw [Idele.normIdeleFun_ofFinite]
  have hmem : q ∈ Place.primesOverFinite (K := K) (L := L) Q :=
    Place.mem_primesOverFinite.mpr hq
  have hprod := Finset.prod_eq_single
    (s := (Place.primesOverFinite (K := K) (L := L) Q).attach)
    (f := fun q' : ↥(Place.primesOverFinite (K := K) (L := L) Q) =>
      Place.localNormFinite q'.1 Q
        ((Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q'.1)).mp q'.2)
        ((singleIdeleL (Place.ofFinite q) u) (Place.ofFinite q'.1)))
    (⟨q, hmem⟩ : ↥(Place.primesOverFinite (K := K) (L := L) Q))
    (fun b _ hb => by
      have hbq : b.1 ≠ q := fun h => hb (Subtype.ext h)
      have hne : Place.ofFinite b.1 ≠ Place.ofFinite q := fun h =>
        hbq (Place.ofFinite_inj.mp h)
      rw [singleIdeleL_apply_of_ne (L := L) hne, map_one])
    (fun hb => absurd (Finset.mem_attach _ _) hb)
  rw [hprod, singleIdeleL_apply_self]

/-- **Archimedean places.**  The idèlic norm of the idèle concentrated at an infinite place `w` of
`L` above `v`, evaluated at `v`, is the local norm `N_{L_w/K_v} u`. -/
theorem normIdeleFun_singleIdeleL_ofInfinite {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (w : InfinitePlace L)
    (v : InfinitePlace K) [hw : w.LiesOver v] (u : w.Completionˣ) :
    Idele.normIdeleFun K L (singleIdeleL (Place.ofInfinite w) u) (Place.ofInfinite v) =
      Place.localNormInfinite w v u := by
  classical
  rw [Idele.normIdeleFun_ofInfinite]
  have hmem : w ∈ Place.fiberInfinite (K := K) (L := L) v :=
    Place.mem_fiberInfinite.mpr hw
  have hprod := Finset.prod_eq_single
    (s := (Place.fiberInfinite (K := K) (L := L) v).attach)
    (f := fun w' : ↥(Place.fiberInfinite (K := K) (L := L) v) =>
      letI : (w'.1 : NumberField.InfinitePlace L).LiesOver v :=
        (Place.mem_fiberInfinite (K := K) (L := L) (v := v) (w := w'.1)).mp w'.2
      Place.localNormInfinite w'.1 v
        ((singleIdeleL (Place.ofInfinite w) u) (Place.ofInfinite w'.1)))
    (⟨w, hmem⟩ : ↥(Place.fiberInfinite (K := K) (L := L) v))
    (fun b _ hb => by
      have hbw : b.1 ≠ w := fun h => hb (Subtype.ext h)
      have hne : Place.ofInfinite b.1 ≠ Place.ofInfinite w := fun h =>
        hbw (Place.ofInfinite_inj.mp h)
      rw [singleIdeleL_apply_of_ne (L := L) hne, map_one])
    (fun hb => absurd (Finset.mem_attach _ _) hb)
  rw [hprod, singleIdeleL_apply_self]

/-- The idèlic norm depends only on the values of the idèle at the places above `v`. -/
theorem normIdeleFun_congr_of_liesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {x x' : Idele L} {v : Place K}
    (h : ∀ w : Place L, Place.LiesOver w v → x w = x' w) :
    Idele.normIdeleFun K L x v = Idele.normIdeleFun K L x' v := by
  rcases v with w | Q
  · rw [Idele.normIdeleFun_ofInfinite, Idele.normIdeleFun_ofInfinite]
    refine Finset.prod_congr rfl fun w' _ => ?_
    have hw : (w'.1 : NumberField.InfinitePlace L).LiesOver w :=
      (Place.mem_fiberInfinite (K := K) (L := L) (v := w) (w := w'.1)).mp w'.2
    rw [h (Place.ofInfinite w'.1) (Place.liesOver_ofInfinite hw)]
  · rw [Idele.normIdeleFun_ofFinite, Idele.normIdeleFun_ofFinite]
    refine Finset.prod_congr rfl fun q' _ => ?_
    have hq : q'.1.asIdeal.LiesOver Q.asIdeal :=
      (Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := q'.1)).mp q'.2
    rw [h (Place.ofFinite q'.1) (Place.liesOver_ofFinite hq)]

end Bridge

/-! ### The assembled idèle realising prescribed local norms -/

section Assemble

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- The place of `K` below a place of `L`. -/
theorem placeUnder_eq_of_liesOver {w : Place L} {v : Place K} (h : Place.LiesOver w v) :
    Norm.globalCFT_placeUnder w = v :=
  Inclusion.globalCFT_liesOver_unique (Norm.liesOver_globalCFT_placeUnder w) h

/-- The value at the place `w` of the single local contribution attached to `v`: it is `u v` at
`g v` and `1` elsewhere. -/
noncomputable def yValAt (g : Place K → Place L)
    (u : (v : Place K) → (Place.localField L (g v))ˣ) (v : Place K) (w : Place L) :
    (Place.localField L w)ˣ := by
  classical
  exact if h : w = g v then h.symm ▸ u v else 1

/-- The value at `w` of the idèle of `L` built from a choice of a place `g v` above each place
`v` of `K` and a local element `u v` at that place. -/
noncomputable def yVal (g : Place K → Place L)
    (u : (v : Place K) → (Place.localField L (g v))ˣ) (w : Place L) :
    (Place.localField L w)ˣ :=
  yValAt g u (Norm.globalCFT_placeUnder w) w

theorem yValAt_self (g : Place K → Place L)
    (u : (v : Place K) → (Place.localField L (g v))ˣ) (v : Place K) :
    yValAt g u v (g v) = u v := by
  classical
  simp only [yValAt]
  simp

theorem yValAt_of_ne {g : Place K → Place L}
    {u : (v : Place K) → (Place.localField L (g v))ˣ} {v : Place K} {w : Place L}
    (h : w ≠ g v) : yValAt g u v w = 1 := by
  classical
  simp only [yValAt, dif_neg h]

theorem yVal_pickW {g : Place K → Place L}
    {u : (v : Place K) → (Place.localField L (g v))ˣ}
    (hlies : ∀ v : Place K, Place.LiesOver (g v) v) (v : Place K) :
    yVal g u (g v) = u v := by
  rw [yVal, placeUnder_eq_of_liesOver (hlies v)]
  exact yValAt_self g u v

theorem yVal_eq_one_of_liesOver_ne {g : Place K → Place L}
    {u : (v : Place K) → (Place.localField L (g v))ˣ} {w : Place L} {v : Place K}
    (hw : Place.LiesOver w v) (hne : w ≠ g v) : yVal g u w = 1 := by
  rw [yVal, placeUnder_eq_of_liesOver hw]
  exact yValAt_of_ne hne

theorem yVal_mem_localUnits_pickW {g : Place K → Place L}
    {u : (v : Place K) → (Place.localField L (g v))ˣ} {S : Finset (Place K)}
    (hlies : ∀ v : Place K, Place.LiesOver (g v) v)
    (hunit : ∀ v : Place K, v ∉ S → u v ∈ Place.localUnits L (g v))
    {v : Place K} (hvS : v ∉ S) :
    yVal g u (g v) ∈ Place.localUnits L (g v) := by
  rw [yVal_pickW hlies v]
  exact hunit v hvS

/-- The assembled idèle of `L` is a local unit at all but finitely many places. -/
theorem finite_yVal_not_mem_localUnits {g : Place K → Place L}
    {u : (v : Place K) → (Place.localField L (g v))ˣ} {S : Finset (Place K)}
    (hlies : ∀ v : Place K, Place.LiesOver (g v) v)
    (hunit : ∀ v : Place K, v ∉ S → u v ∈ Place.localUnits L (g v)) :
    {w : Place L | yVal g u w ∉ Place.localUnits L w}.Finite := by
  classical
  refine Set.Finite.subset (S.finite_toSet.image g) ?_
  intro w hw
  simp only [Set.mem_ofPred_eq] at hw
  by_cases hex : ∃ v : Place K, g v = w
  · obtain ⟨v, hv⟩ := hex
    refine ⟨v, ?_, hv⟩
    by_contra hvnot
    have hvS : v ∉ S := hvnot
    have hmem := yVal_mem_localUnits_pickW hlies hunit hvS
    rw [hv] at hmem
    exact hw hmem
  · exfalso
    have h : w ≠ g (Norm.globalCFT_placeUnder w) := by
      intro hh
      exact hex ⟨Norm.globalCFT_placeUnder w, hh.symm⟩
    have h1 : yVal g u w = 1 := by
      rw [yVal]
      exact yValAt_of_ne h
    rw [h1] at hw
    exact hw (Subgroup.one_mem _)

end Assemble

/-! ### The local subgroup of idèles -/

section Constrained

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **The idèles with local conditions**: the subgroup of `𝕀 K` consisting of the idèles which
lie in `A v` at the places `v` of a finite set `S` and are local units outside `S`. -/
def constrainedLoc (S : Finset (Place K)) (A : (v : S) → Subgroup ((Place.localField K v)ˣ)) :
    Subgroup (Idele K) where
  carrier := {x : Idele K | (∀ v : S, x v ∈ A v) ∧
    ∀ v : Place K, v ∉ S → x v ∈ Place.localUnits K v}
  one_mem' := ⟨fun v => (A v).one_mem, fun v _ => (Place.localUnits K v).one_mem⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨fun v => by rw [Idele.mul_apply]; exact (A v).mul_mem (hx1 v) (hy1 v),
      fun v hv => by
        rw [Idele.mul_apply]; exact (Place.localUnits K v).mul_mem (hx2 v hv) (hy2 v hv)⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨fun v => by rw [Idele.inv_apply]; exact (A v).inv_mem (hx1 v),
      fun v hv => by rw [Idele.inv_apply]; exact (Place.localUnits K v).inv_mem (hx2 v hv)⟩

theorem mem_constrainedLoc {S : Finset (Place K)}
    {A : (v : S) → Subgroup ((Place.localField K v)ˣ)} {x : Idele K} :
    x ∈ constrainedLoc S A ↔ (∀ v : S, x v ∈ A v) ∧
      ∀ v : Place K, v ∉ S → x v ∈ Place.localUnits K v := Iff.rfl

/-- **`constrainedLoc S A` is open when each `A v` is open.**  The condition "`x v ∈ A v` for
`v ∈ S`" is a finite intersection of preimages of open sets under the (continuous) evaluations
`𝕀 K → K_vˣ`, and the condition "`x` is a local unit outside `S`" is a basic open subset of the
restricted product. -/
theorem isOpen_constrainedLoc (S : Finset (Place K))
    (A : (v : S) → Subgroup ((Place.localField K v)ˣ))
    (hA : ∀ v : S, IsOpen (A v : Set ((Place.localField K v)ˣ))) :
    IsOpen (constrainedLoc S A : Set (Idele K)) := by
  have hset : (constrainedLoc S A : Set (Idele K)) =
      ({x : Idele K | ∀ v : S, x v ∈ A v} ∩
       {x : Idele K | ∀ v : Place K, v ∉ S → x v ∈ Place.localUnits K v}) := by
    ext x
    exact mem_constrainedLoc
  rw [hset]
  refine IsOpen.inter ?_ ?_
  · rw [show {x : Idele K | ∀ v : S, x v ∈ A v} =
        ⋂ v : S, (Idele.eval v.1) ⁻¹' (A v : Set ((Place.localField K v.1)ˣ)) from
      Set.ext fun x => by simp [Set.mem_iInter]]
    exact isOpen_iInter_of_finite fun v =>
      (hA v).preimage (RestrictedProduct.continuous_eval v.1)
  · exact RestrictedProduct.isOpen_forall_imp_mem
      (R := fun v : Place K => (Place.localField K v)ˣ)
      (A := fun v => (Place.localUnits K v : Set _)) (p := fun v => v ∉ S)
      (fun v => Place.isOpen_localUnits v)

/-- **The local data bound the idèlic norm subgroup.** -/
theorem constrainedLoc_le_normImage (S : Finset (Place K))
    (A : (v : S) → Subgroup ((Place.localField K v)ˣ))
    (g : Place K → Place L) (hg : ∀ v, Place.LiesOver (g v) v)
    (Φ : (v : Place K) → (Place.localField L (g v))ˣ →* (Place.localField K v)ˣ)
    (hbridge : ∀ (v : Place K) (u : (Place.localField L (g v))ˣ),
      Idele.normIdeleFun K L (singleIdeleL (g v) u) v = Φ v u)
    (hA : ∀ v : S, A v ≤ (Φ v).range)
    (hunit : ∀ v : Place K, v ∉ S → ∀ a ∈ Place.localUnits K v,
      ∃ u ∈ Place.localUnits L (g v), Φ v u = a) :
    constrainedLoc S A ≤ Idele.normImage K L := by
  intro x hx
  rw [Idele.mem_normImage]
  obtain ⟨hxS, hxU⟩ := hx
  have hex : ∀ v : Place K, ∃ u : (Place.localField L (g v))ˣ,
      Φ v u = x v ∧ (v ∉ S → u ∈ Place.localUnits L (g v)) := by
    intro v
    by_cases hvS : v ∈ S
    · obtain ⟨u, hu⟩ := hA ⟨v, hvS⟩ (hxS ⟨v, hvS⟩)
      exact ⟨u, hu, fun h => absurd hvS h⟩
    · obtain ⟨u, hun, hu⟩ := hunit v hvS (x v) (hxU v hvS)
      exact ⟨u, hu, fun _ => hun⟩
  choose u hu huu using hex
  have hfin : {w : Place L | yVal g u w ∉ Place.localUnits L w}.Finite :=
    finite_yVal_not_mem_localUnits hg (fun v hvS => huu v hvS)
  let y : Idele L := RestrictedProduct.mk (yVal g u) (Filter.eventually_cofinite.mpr hfin)
  refine ⟨y, fun v => ?_⟩
  rw [← hu v, ← hbridge v (u v)]
  refine (normIdeleFun_congr_of_liesOver (x := y)
    (x' := singleIdeleL (g v) (u v)) ?_).symm
  intro w hw
  by_cases hwv : w = g v
  · subst hwv
    rw [show y (g v) = yVal g u (g v) from rfl, yVal_pickW hg v, singleIdeleL_apply_self]
  · rw [show y w = yVal g u w from rfl, yVal_eq_one_of_liesOver_ne hw hwv,
      singleIdeleL_apply_of_ne hwv]

end Constrained

/-! ### From an open subgroup of the idèles to the openness of the norm subgroup -/

section Final

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **An open subgroup of `𝕀 K` contained in the idèlic norm subgroup makes the norm subgroup of
the idèle class group open.**

Indeed `E.map (mk K)` is an open subgroup of `C_K` contained in `normClassSubgroup K L` (the image
of the quotient map `𝕀 K → C_K` is open because that map is open), and a subgroup containing an
open subgroup is open. -/
theorem isOpen_normClassSubgroup_of_isOpen_le (E : Subgroup (Idele K))
    (hE : IsOpen (E : Set (Idele K))) (hEle : E ≤ Idele.normImage K L) :
    IsOpen (Idele.normClassSubgroup K L : Set (IdeleClassGroup K)) := by
  have hopen : IsOpen ((E.map (IdeleClassGroup.mk K) : Subgroup (IdeleClassGroup K)) :
      Set (IdeleClassGroup K)) := by
    have h : IsOpen ((IdeleClassGroup.mk K) '' (E : Set (Idele K))) :=
      QuotientGroup.isOpenMap_coe (N := Idele.principalSubgroup K) _ hE
    simpa [Subgroup.coe_map] using h
  refine Subgroup.isOpen_mono ?_ hopen
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr ⟨y, hEle hy, rfl⟩

/-- **The norm subgroup of the idèle class group is open, from the per-place local data.**

Let `S` be a finite set of places of `K`, `g` a choice of a place of `L` above each place of `K`,
`Φ v` the local norm at `g v` computing the idèlic norm (`hbridge`), `A v` an open subgroup of
`K_vˣ` contained in the range of `Φ v` for `v ∈ S`, and assume that outside `S` the local norm is
surjective on local units (`hunit`).  Then `N_{L/K} C_L` is open in `C_K`. -/
theorem isOpen_normClassSubgroup_of_localData (S : Finset (Place K))
    (A : (v : S) → Subgroup ((Place.localField K v)ˣ))
    (g : Place K → Place L) (hg : ∀ v, Place.LiesOver (g v) v)
    (Φ : (v : Place K) → (Place.localField L (g v))ˣ →* (Place.localField K v)ˣ)
    (hbridge : ∀ (v : Place K) (u : (Place.localField L (g v))ˣ),
      Idele.normIdeleFun K L (singleIdeleL (g v) u) v = Φ v u)
    (hAopen : ∀ v : S, IsOpen (A v : Set ((Place.localField K v)ˣ)))
    (hA : ∀ v : S, A v ≤ (Φ v).range)
    (hunit : ∀ v : Place K, v ∉ S → ∀ a ∈ Place.localUnits K v,
      ∃ u ∈ Place.localUnits L (g v), Φ v u = a) :
    IsOpen (Idele.normClassSubgroup K L : Set (IdeleClassGroup K)) :=
  isOpen_normClassSubgroup_of_isOpen_le (constrainedLoc S A)
    (isOpen_constrainedLoc S A hAopen)
    (constrainedLoc_le_normImage S A g hg Φ hbridge hA hunit)

end Final


/-! ### Choosing the places -/

section Places

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **Every place of `K` has a place of `L` above it.** -/
theorem exists_place_liesOver (v : Place K) : ∃ w : Place L, Place.LiesOver w v := by
  rcases v with v' | Q
  · obtain ⟨w, hw⟩ := NumberField.InfinitePlace.comap_surjective (k := K) (K := L) v'
    exact ⟨Place.ofInfinite w,
      Place.liesOver_ofInfinite ((Norm.liesOver_iff_comap_eq w v').mpr hw)⟩
  · obtain ⟨q, hq⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
    exact ⟨Place.ofFinite q, Place.liesOver_ofFinite hq⟩

/-- **A finite set of places of `K` containing all the archimedean places and every finite place
below a ramified prime of `L`.**  This is the set `S` of the main argument: outside it the local
extension `L_q / K_Q` is unramified, so that the local norm is surjective on local units. -/
theorem exists_finset_places_good :
    ∃ S : Finset (Place K), (∀ v : NumberField.InfinitePlace K, Place.ofInfinite v ∈ S) ∧
      ∀ (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K)),
        q.asIdeal.LiesOver Q.asIdeal → Place.ofFinite Q ∉ S →
          q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  classical
  have hramfin : {q : HeightOneSpectrum (𝓞 L) | q.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite :=
    Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one (K := K) (L := L)
  let A : Finset (Place K) := Finset.univ.image Place.ofInfinite
  let D : Finset (Place K) := hramfin.toFinset.image
    (fun q => Norm.globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite q))
  refine ⟨A ∪ D, ?_, ?_⟩
  · intro v
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  · intro q Q hLie hQnot
    by_contra hram
    have hq : q ∈ hramfin.toFinset := hramfin.mem_toFinset.mpr hram
    have hDmem : Norm.globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite q) ∈ D :=
      Finset.mem_image_of_mem _ hq
    have heq : Norm.globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite q) = Place.ofFinite Q :=
      Inclusion.globalCFT_liesOver_unique
        (Norm.liesOver_globalCFT_placeUnder (K := K) (L := L) (Place.ofFinite q))
        (Place.liesOver_ofFinite hLie)
    exact hQnot (by rw [← heq]; exact Finset.mem_union_right _ hDmem)

end Places


/-! ### The local norm is surjective on units at an unramified place -/

section Unramified

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **At an unramified finite place the local norm is surjective on the local units.**

If `q` lies over `Q` with ramification index one, then every unit of `K_Q` is the norm of a unit of
`L_q`.  The proof is the valuation computation `v (N x) = v x ^ f` (`f` the inertia degree, here
the degree): a preimage of a unit has valuation one, hence is a unit. -/
theorem localUnits_le_image_localNormFinite_of_unramified
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    ∀ a ∈ Place.localUnits K (Place.ofFinite Q), ∃ u ∈ Place.localUnits L (Place.ofFinite q),
      Place.localNormFinite q Q hq u = a := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfd : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  intro a ha
  have hval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (a : Q.adicCompletion K) = 1 :=
    (Place.mem_localUnits_ofFinite_iff_valued_eq_one (K := K) (q := Q)).mp ha
  obtain ⟨x, hx⟩ :=
    Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
      Q q hq hunr (a : Q.adicCompletion K) hval
  have hxne : x ≠ 0 := by
    intro h0
    have h1 : Algebra.norm (Q.adicCompletion K) x = (0 : Q.adicCompletion K) := by
      rw [h0, Algebra.norm_zero]
    rw [h1] at hx
    exact Units.ne_zero a hx.symm
  have hvx : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x = 1 := by
    have h1 := Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow Q q hq x
    have h2 := Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq
      (Algebra.norm (Q.adicCompletion K) x)
    have halg : (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) x)) =
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
          (Algebra.norm (Q.adicCompletion K) x) := rfl
    have hfin : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) =
        q.asIdeal.inertiaDeg (𝓞 K) := by
      have h := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        (K := K) (L := L) Q q hq
      rw [hunr, one_mul] at h
      exact h.symm
    have hvpow : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x ^
        (q.asIdeal.inertiaDeg (𝓞 K)) = 1 := by
      rw [← hfin, ← h1, halg, h2, hx, hval, hunr]
      simp
    have hvne : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hxne
    have hlog : (q.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        WithZero.log (Valued.v (R := q.adicCompletion L)
          (Γ₀ := WithZero (Multiplicative ℤ)) x) = 0 := by
      have h := WithZero.log_pow (Valued.v (R := q.adicCompletion L)
        (Γ₀ := WithZero (Multiplicative ℤ)) x) (q.asIdeal.inertiaDeg (𝓞 K))
      rw [hvpow, WithZero.log_one] at h
      simpa [nsmul_eq_mul] using h.symm
    have hfne : (q.asIdeal.inertiaDeg (𝓞 K) : ℤ) ≠ 0 := by
      haveI : q.asIdeal.IsPrime := q.isPrime
      haveI : Module.Finite (𝓞 K) (𝓞 L) := inferInstance
      exact_mod_cast (Ideal.inertiaDeg_pos q.asIdeal (𝓞 K)).ne'
    have hlog0 : WithZero.log (Valued.v (R := q.adicCompletion L)
        (Γ₀ := WithZero (Multiplicative ℤ)) x) = 0 :=
      (mul_eq_zero.mp hlog).resolve_left hfne
    rw [← WithZero.exp_log hvne, hlog0, WithZero.exp_zero]
  refine ⟨Units.mk0 x hxne, ?_, ?_⟩
  · rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one]
    exact hvx
  · rw [Place.localNormFinite]
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_mk0]
    exact hx

end Unramified

end NK.NUV2.ArtinBridge
