/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The universal property of `Ẑ = lim_n ℤ ⧸ nℤ`

`Ẑ = NK.LocalAnabelian.Zhat` is the limit of the finite quotients `ℤ ⧸ dℤ` of `ℤ`,
and `compHomZMod d hd : Ẑ →* Multiplicative (ZMod d)` is the `d`-th component map.

The initial statement of the file is the *universal property* of this limit: every
compatible family of elements `c d ∈ ℤ/dℤ` (compatible meaning that `c e` is the
reduction of `c d` whenever `e ∣ d`) is the family of components of a unique `z : Ẑ`.

The proof goes through the compactness of `Ẑ`:

* every component map `compHomZMod d hd` is surjective (it is hit by the dense copy of `ℤ`),
* the fibres `{z | compHomZMod d hd z = c d hd}` are closed, and any finite intersection
  of them contains a point, namely a preimage of `c N` for `N` the product of the levels
  involved (compatibility of the family `c` and of the component maps does the rest);
* a compact space in which a family of closed sets has the finite intersection property
  has nonempty intersection.

Uniqueness follows because the component maps separate points: an element of `Ẑ` is
determined by its components on the `mZ d` (`d ≥ 1`), and every finite index subgroup of
`ℤ` contains some `dℤ`.

Everything is stated with the explicit definitions from
`Submission.NK.TameStructureDeep.Degree.zhatComponents`.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Degree.zhatComponents
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.TameStructureDeep.Degree

open NK.TameStructure.ProCyclic

noncomputable section

/-- **Naturality of the `d`-th component of `Ẑ`.**  For `e ∣ d`, reducing the `d`-th
component of `Ẑ` (viewed in `Multiplicative (ZMod d)`) to `Multiplicative (ZMod e)`
agrees with both the transition map of the limit diagram and the ring reduction
`ZMod.castHom h (ZMod e)`. -/
theorem zmodQuotEquiv_natural (d e : ℕ) (hd : d ≠ 0) (he : e ≠ 0) (h : e ∣ d)
    (q : (Multiplicative ℤ) ⧸ (mZ d hd).toSubgroup) :
    ZMod.castHom h (ZMod e) (Multiplicative.toAdd (zmodQuotEquiv d hd q)) =
      Multiplicative.toAdd (zmodQuotEquiv e he
        (QuotientGroup.map (mZ d hd).toSubgroup (mZ e he).toSubgroup (MonoidHom.id _)
          (by simpa using mZ_le_mZ hd he h) q)) := by
  induction q using QuotientGroup.induction_on with
  | _ x =>
    rw [← ofAdd_toAdd x, QuotientGroup.map_mk]
    rw [show zmodQuotEquiv e he
          (QuotientGroup.mk ((MonoidHom.id (Multiplicative ℤ))
            (Multiplicative.ofAdd (Multiplicative.toAdd x)))) =
        toZModHom e (Multiplicative.ofAdd (Multiplicative.toAdd x)) from rfl]
    rw [show zmodQuotEquiv d hd
          (QuotientGroup.mk (Multiplicative.ofAdd (Multiplicative.toAdd x))) =
        toZModHom d (Multiplicative.ofAdd (Multiplicative.toAdd x)) from rfl]
    rw [toZModHom_apply, toZModHom_apply, toAdd_ofAdd, toAdd_ofAdd, ZMod.castHom_apply]
    exact ZMod.cast_intCast h _

/-- **Compatibility of the component maps of `Ẑ`.**  For `e ∣ d` the `e`-th and the `d`-th
component of an element of `Ẑ` are related by the reduction map. -/
theorem zmod_cast_toAdd_compHomZMod (d e : ℕ) (hd : d ≠ 0) (he : e ≠ 0) (h : e ∣ d)
    (z : NK.LocalAnabelian.Zhat) :
    ZMod.castHom h (ZMod e) (Multiplicative.toAdd (compHomZMod d hd z)) =
      Multiplicative.toAdd (compHomZMod e he z) := by
  have hle : (mZ d hd).toSubgroup ≤ (mZ e he).toSubgroup := mZ_le_mZ hd he h
  have hπ : (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of (Multiplicative ℤ))).map
      (CategoryTheory.homOfLE hle) (z.val (mZ d hd)) = z.val (mZ e he) :=
    z.property (CategoryTheory.homOfLE hle)
  show ZMod.castHom h (ZMod e)
        (Multiplicative.toAdd (zmodQuotEquiv d hd (z.val (mZ d hd)))) =
      Multiplicative.toAdd (zmodQuotEquiv e he (z.val (mZ e he)))
  rw [← hπ]
  exact zmodQuotEquiv_natural d e hd he h _

/-- Every component map `compHomZMod d hd` is surjective: it is hit by the dense copy of
`ℤ` inside `Ẑ`. -/
theorem compHomZMod_surjective (d : ℕ) (hd : d ≠ 0) :
    Function.Surjective (compHomZMod d hd) := by
  intro y
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd y)
  refine ⟨intCastZhat k, ?_⟩
  have h1 : compHomZMod d hd (intCastZhat k) = Multiplicative.ofAdd ((k : ZMod d)) := by
    rw [compHomZMod_apply, compHom_intCastZhat]
    rw [show zmodQuotEquiv d hd (QuotientGroup.mk (Multiplicative.ofAdd k)) =
        toZModHom d (Multiplicative.ofAdd k) from rfl, toZModHom_apply]
  rw [h1, hk, ofAdd_toAdd]

/-- The component maps of `Ẑ` are continuous. -/
theorem continuous_compHomZMod (d : ℕ) (hd : d ≠ 0) : Continuous (compHomZMod d hd) := by
  change Continuous (fun z : NK.LocalAnabelian.Zhat => zmodQuotEquiv d hd (compHom d hd z))
  exact Continuous.comp continuous_of_discreteTopology (compHom_cont d hd)

/-- **The component maps separate points of `Ẑ`.**  If two elements have the same `d`-th
component for every `d ≥ 1`, they are equal. -/
theorem eq_of_compHomZMod_eq (z z' : NK.LocalAnabelian.Zhat)
    (h : ∀ (d : ℕ) (hd : d ≠ 0), compHomZMod d hd z = compHomZMod d hd z') : z = z' := by
  apply ProfiniteGrp.limit_ext
  intro H
  set n : ℕ := H.toSubgroup.index with hn_def
  have hn : n ≠ 0 := by
    rw [hn_def]
    exact Subgroup.finiteIndex_iff.mp H.isFiniteIndex'
  -- the two elements agree on the `n`-th component, `n` the index of `H`
  have hval : z.val (mZ n hn) = z'.val (mZ n hn) := by
    apply (zmodQuotEquiv n hn).injective
    exact h n hn
  -- `H` contains `mZ n`
  have hpow : Multiplicative.ofAdd (n : ℤ) ∈ H.toSubgroup := by
    have hmem : (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ^ H.toSubgroup.index ∈
        H.toSubgroup := Subgroup.pow_index_mem H.toSubgroup _
    rw [← hn_def] at hmem
    have h2 : (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ^ n =
        Multiplicative.ofAdd (n : ℤ) := by
      rw [← ofAdd_nsmul]
      congr 1
      simp
    rwa [h2] at hmem
  have hle : (mZ n hn).toSubgroup ≤ H.toSubgroup := by
    intro x hx
    rw [← ofAdd_toAdd x] at hx ⊢
    rw [mem_mZ] at hx
    obtain ⟨c, hc⟩ := hx
    rw [hc]
    have hzx : Multiplicative.ofAdd ((n : ℤ) * c) = (Multiplicative.ofAdd (n : ℤ)) ^ c := by
      rw [show (n : ℤ) * c = c • (n : ℤ) by simp [mul_comm], ofAdd_zsmul]
    rw [hzx]
    exact Subgroup.zpow_mem _ hpow c
  have hπ : (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of (Multiplicative ℤ))).map
      (CategoryTheory.homOfLE hle) (z.val (mZ n hn)) = z.val H :=
    z.property (CategoryTheory.homOfLE hle)
  have hπ' : (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of (Multiplicative ℤ))).map
      (CategoryTheory.homOfLE hle) (z'.val (mZ n hn)) = z'.val H :=
    z'.property (CategoryTheory.homOfLE hle)
  calc z.val H
      = (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of (Multiplicative ℤ))).map
          (CategoryTheory.homOfLE hle) (z.val (mZ n hn)) := hπ.symm
    _ = (ProfiniteGrp.ProfiniteCompletion.diagram (GrpCat.of (Multiplicative ℤ))).map
          (CategoryTheory.homOfLE hle) (z'.val (mZ n hn)) := by rw [hval]
    _ = z'.val H := hπ'

/-- **Existence and uniqueness of `z` with prescribed components.**  A compatible family of
elements `c d ∈ ℤ/dℤ` (for `d ≥ 1`) is the family of components of a unique element of `Ẑ`. -/
theorem zhat_existsUnique_compHomZMod_eq
    (c : (d : ℕ) → (hd : d ≠ 0) → Multiplicative (ZMod d))
    (hc : ∀ (d e : ℕ) (hd : d ≠ 0) (he : e ≠ 0) (h : e ∣ d),
      ZMod.castHom h (ZMod e) (Multiplicative.toAdd (c d hd)) = Multiplicative.toAdd (c e he)) :
    ∃! z : NK.LocalAnabelian.Zhat, ∀ (d : ℕ) (hd : d ≠ 0),
      NK.TameStructureDeep.Degree.compHomZMod d hd z = c d hd := by
  -- the closed sets of elements with a prescribed `d`-th component
  let F : {d : ℕ // d ≠ 0} → Set NK.LocalAnabelian.Zhat :=
    fun i => {z | compHomZMod i.1 i.2 z = c i.1 i.2}
  have hclosed : ∀ i, IsClosed (F i) := fun i =>
    isClosed_eq (continuous_compHomZMod i.1 i.2) continuous_const
  -- the finite intersection property: the product of the levels is a common refinement
  have hfip : ∀ u : Finset {d : ℕ // d ≠ 0}, (⋂ i ∈ u, F i).Nonempty := by
    intro u
    obtain ⟨z, hz⟩ := compHomZMod_surjective (∏ i ∈ u, i.1)
      (Finset.prod_ne_zero_iff.mpr fun i _ => i.2) (c _ (Finset.prod_ne_zero_iff.mpr fun i _ => i.2))
    refine ⟨z, ?_⟩
    rw [Set.mem_iInter]
    intro i
    rw [Set.mem_iInter]
    intro hi
    have hdvd : i.1 ∣ ∏ j ∈ u, j.1 := Finset.dvd_prod_of_mem _ hi
    have hcast := zmod_cast_toAdd_compHomZMod _ i.1
      (Finset.prod_ne_zero_iff.mpr fun j _ => j.2) i.2 hdvd z
    rw [hz] at hcast
    have hcomp := hc _ i.1 (Finset.prod_ne_zero_iff.mpr fun j _ => j.2) i.2 hdvd
    exact Multiplicative.toAdd.injective (by rw [← hcast, hcomp])
  obtain ⟨z, hzmem⟩ := CompactSpace.iInter_nonempty (t := F) hclosed hfip
  have hzF : ∀ i, z ∈ F i := Set.mem_iInter.mp hzmem
  refine ⟨z, fun d hd => hzF ⟨d, hd⟩, fun z' hz' => ?_⟩
  refine eq_of_compHomZMod_eq z' z fun d hd => ?_
  rw [hz' d hd, hzF ⟨d, hd⟩]

end

end NK.TameStructureDeep.Degree
