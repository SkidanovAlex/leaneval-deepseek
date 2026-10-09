import Mathlib
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFTdeep.Herbrand.top_eq_principal_sup_TIdeles
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.kummerE_le_normImage
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt
import Submission.Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local–global principle for norms of idèles

For a finite Galois extension `L / K` of number fields, the group of norms of idèles
`N_{L/K} 𝕀_L ≤ 𝕀_K` is the subgroup of those idèles all of whose components are local norms:

`x ∈ N_{L/K} 𝕀_L ↔ ∀ v, ∃ y : 𝕀_L, x v = N_{L/K}(y) v`.

The non-trivial direction is the construction of a *single* idèle of `L` realising all the local
conditions at once.  Let `S` be the finite set of places of `K` consisting of

* the archimedean places (where the local norm is not surjective on the local units),
* the places below a ramified prime of `L`, and
* the places at which `x` is not a local unit.

At the finitely many places `v ∈ S` one uses the given local preimage on the whole fibre of `L`
above `v`; at all other places `v` the extension is unramified and `x v` is a local unit, so `x v`
is the norm of a *local unit* at a single place above `v`
(`localNormFinite_units_surjective_of_ramificationIdx_eq_one`) and the idèle is `1` at all other
places above `v`.  The resulting idèle of `L` is a local unit at all but finitely many places.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.IdeleHasse

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## A choice of a place of `L` above each place of `K` -/

/-- A place of `L` above a given place of `K`, chosen so that at a finite place it is (the place
attached to) a prime of `𝓞 L` above the corresponding prime of `𝓞 K`. -/
noncomputable def placeAbove (v : Place K) : Place L :=
  match v with
  | Sum.inl w =>
      Place.ofInfinite (Classical.choose (InfinitePlace.comap_surjective (k := K) (K := L) w))
  | Sum.inr Q =>
      Place.ofFinite (Classical.choose
        (Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q))

theorem liesOver_placeAbove (v : Place K) : Place.LiesOver (placeAbove (K := K) (L := L) v) v := by
  cases v with
  | inl w =>
      refine Place.liesOver_ofInfinite ?_
      rw [Norm.liesOver_iff_comap_eq]
      exact Classical.choose_spec (InfinitePlace.comap_surjective (k := K) (K := L) w)
  | inr Q =>
      exact Place.liesOver_ofFinite (Classical.choose_spec
        (Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q))

theorem placeUnder_placeAbove (v : Place K) :
    NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L
      (placeAbove (K := K) (L := L) v) = v :=
  NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_eq_of_liesOver (liesOver_placeAbove v)

/-! ## The exceptional set of places -/

/-- The finite set of places of `K` at which the norm computation is special: the archimedean
places, the places at which the given idèle is not a local unit, and the places below a prime of
`L` which is ramified over `K`. -/
noncomputable def badSet (x : Idele K) : Finset (Place K) := by
  classical
  exact (Finset.univ.image (Place.ofInfinite (K := K))) ∪
    (Filter.eventually_cofinite.mp x.2).toFinset ∪
    ((Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
        (K := K) (L := L)).toFinset.image
      (fun q => Place.ofFinite (HeightOneSpectrum.under (𝓞 K) q)))

theorem mem_badSet_of_isInfinite {x : Idele K} {v : Place K} (h : Place.IsInfinite v) :
    v ∈ badSet (K := K) (L := L) x := by
  classical
  obtain ⟨w, rfl⟩ := Place.isInfinite_iff.mp h
  exact Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image_of_mem _ (Finset.mem_univ w)))

theorem mem_badSet_of_not_mem_localUnits {x : Idele K} {v : Place K}
    (h : x v ∉ Place.localUnits K v) : v ∈ badSet (K := K) (L := L) x := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    ((Set.Finite.mem_toFinset _).mpr h))

theorem mem_badSet_of_ramificationIdx_ne_one {x : Idele K} {Q : HeightOneSpectrum (𝓞 K)}
    {q : HeightOneSpectrum (𝓞 L)} (hq : q.asIdeal.LiesOver Q.asIdeal)
    (h : q.asIdeal.ramificationIdx (𝓞 K) ≠ 1) :
    Place.ofFinite Q ∈ badSet (K := K) (L := L) x := by
  classical
  have hQ : HeightOneSpectrum.under (𝓞 K) q = Q :=
    HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal, hq.over])
  have hmem : q ∈ (Commons.NumberTheory.NumberField.finite_setOf_ramificationIdx_ne_one
        (K := K) (L := L)).toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact h
  have h2 := Finset.mem_image_of_mem
    (fun q => Place.ofFinite (HeightOneSpectrum.under (𝓞 K) q)) hmem
  rw [hQ] at h2
  exact Finset.mem_union_right _ h2

/-- The places of `L` lying over a fixed place of `K` are finite. -/
theorem finite_placeUnder_eq (v : Place K) :
    {w : Place L | NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w = v}.Finite := by
  classical
  cases v with
  | inl v' =>
      refine Set.Finite.subset
        ((Place.fiberInfinite (K := K) (L := L) v').finite_toSet.image Place.ofInfinite) ?_
      rintro w hw
      simp only [Set.mem_ofPred_eq] at hw
      cases w with
      | inl w' =>
          refine ⟨w', ?_, rfl⟩
          rw [Finset.mem_coe, Place.mem_fiberInfinite]
          rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_ofInfinite] at hw
          exact (Norm.liesOver_iff_comap_eq w' v').mpr (Place.ofInfinite_inj.mp hw)
      | inr q =>
          rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_ofFinite] at hw
          exact absurd hw (by simp)
  | inr Q =>
      refine Set.Finite.subset
        ((Place.primesOverFinite (K := K) (L := L) Q).finite_toSet.image Place.ofFinite) ?_
      rintro w hw
      simp only [Set.mem_ofPred_eq] at hw
      cases w with
      | inl w' =>
          rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_ofInfinite] at hw
          exact absurd hw (by simp)
      | inr q =>
          refine ⟨q, ?_, rfl⟩
          rw [Finset.mem_coe, Place.mem_primesOverFinite]
          rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_ofFinite] at hw
          have hQ : HeightOneSpectrum.under (𝓞 K) q = Q := Place.ofFinite_inj.mp hw
          exact Ideal.LiesOver.mk (by rw [← HeightOneSpectrum.under_asIdeal, hQ])

/-- The set of places of `L` lying over a finite set of places of `K` is finite. -/
theorem finite_placeUnder_mem_of_finset (s : Finset (Place K)) :
    {w : Place L | NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w ∈
      (s : Set (Place K))}.Finite := by
  classical
  have h : {w : Place L | NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w ∈
        (s : Set (Place K))}
      = ⋃ v ∈ (s : Set (Place K)),
          {w : Place L | NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w = v} := by
    ext w
    simp
  rw [h]
  exact s.finite_toSet.biUnion (fun v _ => finite_placeUnder_eq v)

/-! ## The local units realising the components of `x` -/

variable [IsGalois K L]

/-- At a finite place `Q` of `K` outside `badSet x`, the component `x Q` is the norm of a local
*unit* at the single place `placeAbove Q` of `L`: the extension is unramified there and `x Q` is a
local unit. -/
theorem exists_unit_of_not_mem_badSet (x : Idele K) {Q : HeightOneSpectrum (𝓞 K)}
    (hQ : Place.ofFinite Q ∉ badSet (K := K) (L := L) x) :
    ∃ u : (Place.localField L (placeAbove (K := K) (L := L) (Place.ofFinite Q)))ˣ,
      u ∈ Place.localUnits L (placeAbove (K := K) (L := L) (Place.ofFinite Q)) ∧
      Idele.normIdeleFun K L
        (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
          (placeAbove (K := K) (L := L) (Place.ofFinite Q)) u) (Place.ofFinite Q) =
        x (Place.ofFinite Q) := by
  classical
  set q : HeightOneSpectrum (𝓞 L) := Classical.choose
    (Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q)
    with hqdef
  have hq : q.asIdeal.LiesOver Q.asIdeal := Classical.choose_spec
    (Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q)
  have hram : q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    by_contra h
    exact hQ (mem_badSet_of_ramificationIdx_ne_one hq h)
  have hxmem : x (Place.ofFinite Q) ∈ Place.localUnits K (Place.ofFinite Q) := by
    by_contra h
    exact hQ (mem_badSet_of_not_mem_localUnits h)
  obtain ⟨u, hu, hnorm⟩ :=
    NK.GlobalCFTdeep.SecondInequality.KummerCase.localNormFinite_units_surjective_of_ramificationIdx_eq_one
      Q q hq hram (x (Place.ofFinite Q)) hxmem
  refine ⟨u, hu, ?_⟩
  show Idele.normIdeleFun K L
    (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele (Place.ofFinite q) u)
      (Place.ofFinite Q) = x (Place.ofFinite Q)
  rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_singleIdele_ofFinite Q q hq u]
  exact hnorm

/-- The local unit at `placeAbove v` realising the component `x v` of `x` at a place `v` outside
`badSet x`; the value at a place of `badSet x` is irrelevant. -/
noncomputable def unitAt (x : Idele K) (v : Place K) :
    (Place.localField L (placeAbove (K := K) (L := L) v))ˣ := by
  classical
  exact match v with
  | Sum.inl _ => 1
  | Sum.inr Q => if hv : Place.ofFinite Q ∈ badSet (K := K) (L := L) x then 1
      else Classical.choose (exists_unit_of_not_mem_badSet (K := K) (L := L) x hv)

theorem unitAt_mem_localUnits (x : Idele K) {v : Place K}
    (hv : v ∉ badSet (K := K) (L := L) x) :
    unitAt (K := K) (L := L) x v ∈ Place.localUnits L (placeAbove (K := K) (L := L) v) := by
  classical
  cases v with
  | inl w => exact Subgroup.mem_top _
  | inr Q =>
      rw [unitAt, dif_neg hv]
      exact (Classical.choose_spec (exists_unit_of_not_mem_badSet (K := K) (L := L) x hv)).1

theorem unitAt_norm (x : Idele K) {Q : HeightOneSpectrum (𝓞 K)}
    (hQ : Place.ofFinite Q ∉ badSet (K := K) (L := L) x) :
    Idele.normIdeleFun K L
        (NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
          (placeAbove (K := K) (L := L) (Place.ofFinite Q))
          (unitAt (K := K) (L := L) x (Place.ofFinite Q))) (Place.ofFinite Q) =
      x (Place.ofFinite Q) := by
  classical
  rw [unitAt, dif_neg hQ]
  exact (Classical.choose_spec (exists_unit_of_not_mem_badSet (K := K) (L := L) x hQ)).2

/-- The idèle of `L` which is `1` at all places above a place of `K` outside `badSet x` except at
the chosen place above it, where it is the local unit realising `x`; at the places above a place of
`badSet x` it is the chosen local preimage of `x`. -/
noncomputable def yValueOf (x : Idele K)
    (h : ∀ v : Place K, ∃ y : Idele L, x v = Idele.normIdeleFun K L y v)
    (w : Place L) : (Place.localField L w)ˣ := by
  classical
  exact if hbad : NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w ∈
        badSet (K := K) (L := L) x then
      (h (NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w)).choose w
    else
      NK.GlobalCFTdeep.SecondInequality.KummerCase.yValueAt placeAbove
        (unitAt (K := K) (L := L) x)
        (NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w) w

theorem yValueOf_eq_of_mem {x : Idele K}
    {h : ∀ v : Place K, ∃ y : Idele L, x v = Idele.normIdeleFun K L y v} {w : Place L}
    (hbad : NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w ∈
      badSet (K := K) (L := L) x) :
    yValueOf (K := K) (L := L) x h w =
      (h (NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w)).choose w := by
  classical
  rw [yValueOf, dif_pos hbad]

theorem yValueOf_eq_of_not_mem {x : Idele K}
    {h : ∀ v : Place K, ∃ y : Idele L, x v = Idele.normIdeleFun K L y v} {w : Place L}
    (hbad : NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w ∉
      badSet (K := K) (L := L) x) :
    yValueOf (K := K) (L := L) x h w =
      NK.GlobalCFTdeep.SecondInequality.KummerCase.yValueAt placeAbove
        (unitAt (K := K) (L := L) x)
        (NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w) w := by
  classical
  rw [yValueOf, dif_neg hbad]

/-- A single local unit at `placeAbove v` (`1` elsewhere) is a local unit at every place above a
place `v` outside `badSet x`. -/
theorem yValueAt_mem_localUnits (x : Idele K) {v : Place K}
    (hv : v ∉ badSet (K := K) (L := L) x) (w : Place L) :
    NK.GlobalCFTdeep.SecondInequality.KummerCase.yValueAt placeAbove
        (unitAt (K := K) (L := L) x) v w ∈ Place.localUnits L w := by
  classical
  by_cases h : w = placeAbove (K := K) (L := L) v
  · subst h
    rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.yValueAt_self]
    exact unitAt_mem_localUnits x hv
  · rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.yValueAt_of_ne h]
    exact Subgroup.one_mem _

theorem singleIdele_eq_yValueAt (x : Idele K) (v : Place K) (w : Place L) :
    NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
        (placeAbove (K := K) (L := L) v) (unitAt (K := K) (L := L) x v) w =
      NK.GlobalCFTdeep.SecondInequality.KummerCase.yValueAt placeAbove
        (unitAt (K := K) (L := L) x) v w := rfl

/-- The idèle `yValueOf x h` is a local unit at all but finitely many places. -/
theorem eventually_yValueOf_mem_localUnits (x : Idele K)
    (h : ∀ v : Place K, ∃ y : Idele L, x v = Idele.normIdeleFun K L y v) :
    ∀ᶠ w in Filter.cofinite,
      yValueOf (K := K) (L := L) x h w ∈ Place.localUnits L w := by
  classical
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset
    (finite_placeUnder_mem_of_finset (K := K) (L := L) (badSet (K := K) (L := L) x)) ?_
  intro w hw
  simp only [Set.mem_ofPred_eq] at hw
  by_contra hbad
  rw [yValueOf_eq_of_not_mem (x := x) (h := h) hbad] at hw
  exact hw (yValueAt_mem_localUnits (K := K) (L := L) x hbad w)

/-! ## The local–global principle -/

theorem mem_normImage_iff_localNorm {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] (x : NK.GlobalCFT.Idele K) :
    x ∈ NK.GlobalCFT.Idele.normImage K L ↔
      ∀ v : NK.GlobalCFT.Place K, ∃ y : NK.GlobalCFT.Idele L,
        x v = NK.GlobalCFT.Idele.normIdeleFun K L y v := by
  classical
  constructor
  · rintro ⟨y, hy⟩ v
    exact ⟨y, hy v⟩
  · intro h
    rw [Idele.mem_normImage]
    have hyeventually := eventually_yValueOf_mem_localUnits (K := K) (L := L) x h
    let y : Idele L := ⟨yValueOf (K := K) (L := L) x h, hyeventually⟩
    refine ⟨y, fun v => ?_⟩
    by_cases hv : v ∈ badSet (K := K) (L := L) x
    · have hycongr : ∀ w : Place L, Place.LiesOver w v → y w = (h v).choose w := by
        intro w hw
        have hplace : NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w = v :=
          NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_eq_of_liesOver hw
        have hb : NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w ∈
            badSet (K := K) (L := L) x := by rw [hplace]; exact hv
        rw [show y w = (h (NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w)).choose w
          from yValueOf_eq_of_mem (K := K) (L := L) (x := x) (h := h) (w := w) hb]
        rw [hplace]
      rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_congr_of_liesOver
        (y := y) (y' := (h v).choose) hycongr]
      exact (h v).choose_spec
    · obtain ⟨Q, rfl⟩ : ∃ Q : HeightOneSpectrum (𝓞 K), v = Place.ofFinite Q := by
        rcases v with w | Q
        · exact absurd (mem_badSet_of_isInfinite (K := K) (L := L) (x := x)
            (v := Place.ofInfinite w) (Place.isInfinite_ofInfinite w)) hv
        · exact ⟨Q, rfl⟩
      have hycongr : ∀ w : Place L, Place.LiesOver w (Place.ofFinite Q) →
          y w = NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
              (placeAbove (K := K) (L := L) (Place.ofFinite Q))
              (unitAt (K := K) (L := L) x (Place.ofFinite Q)) w := by
        intro w hw
        have hplace : NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w =
            Place.ofFinite Q :=
          NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder_eq_of_liesOver hw
        have hb : NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w ∉
            badSet (K := K) (L := L) x := by rw [hplace]; exact hv
        rw [show y w = NK.GlobalCFTdeep.SecondInequality.KummerCase.yValueAt placeAbove
              (unitAt (K := K) (L := L) x)
              (NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w) w
          from yValueOf_eq_of_not_mem (K := K) (L := L) (x := x) (h := h) (w := w) hb]
        rw [← singleIdele_eq_yValueAt (K := K) (L := L) x
          (NK.GlobalCFTdeep.SecondInequality.KummerCase.placeUnder K L w) w, hplace]
      rw [NK.GlobalCFTdeep.SecondInequality.KummerCase.normIdeleFun_congr_of_liesOver
        (y := y) (y' := NK.GlobalCFTdeep.SecondInequality.KummerCase.singleIdele
          (placeAbove (K := K) (L := L) (Place.ofFinite Q))
          (unitAt (K := K) (L := L) x (Place.ofFinite Q))) hycongr]
      exact (unitAt_norm (K := K) (L := L) x hv).symm

end NK.CFTLib.IdeleHasse
