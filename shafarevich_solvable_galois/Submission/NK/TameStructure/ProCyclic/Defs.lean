/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pro-cyclic profinite groups: the `Ẑ`-components

This file sets up the technical device by which a continuous surjection `Ẑ ↠ H` is produced
for a pro-cyclic profinite group `H` (`NK.LocalTame.IsProCyclic H`).

Write `Ẑ = NK.LocalAnabelian.Zhat` for the profinite completion of `ℤ`, i.e.
`Ẑ = limit (diagram (GrpCat.of (Multiplicative ℤ)))`, the limit of the finite quotients
`ℤ ⧸ mℤ`.  Its elements are compatible families `z.val mℤ`, and the projections
`z ↦ z.val mℤ` are the *components* of `Ẑ`:

* `mZ m hm` — the finite index normal subgroup `mℤ` of `Multiplicative ℤ`, i.e. an object of the
  index category of the completion (the same subgroup as `NK.TameData.Zhat.mZ`);
* `compHom d hd` — the continuous homomorphism `Ẑ →* ℤ ⧸ dℤ` given by the `d`-th component;
* `quotHom x` — for `x` in a finite group `Q`, the unique homomorphism `ℤ ⧸ dℤ →* Q` (`d` the
  order of `x`) with `1 ↦ x`, obtained by factoring `k ↦ x ^ k` through `dℤ`;
* `famHom g N` — the composite `Ẑ →* H ⧸ N` for an open normal subgroup `N ≤ H`, given by
  `z ↦ (gN) ^ k` on the dense copy of `ℤ` inside `Ẑ`.

The key point of the whole construction is that these component maps are *canonical enough* to
be compatible: `famHom g N` depends only on the coset `gN` of a single element `g`, so the
transition maps `H ⧸ M → H ⧸ N` for `M ≤ N` match the two component maps
(`famHom_compat` in the main file), which is what allows them to be glued into a map `Ẑ →* H`.

## Main definitions

* `NK.TameStructure.ProCyclic.mZ`
* `NK.TameStructure.ProCyclic.compHom`
* `NK.TameStructure.ProCyclic.quotHom`
* `NK.TameStructure.ProCyclic.famHom`
-/
import Mathlib
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalAnabelian.ResidueField.Recovery
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSimpArgs false

open scoped Classical
open ProfiniteGrp

namespace NK.TameStructure.ProCyclic

noncomputable section

/-- `Multiplicative ℤ` as a group object. -/
abbrev ZGrp : GrpCat := GrpCat.of (Multiplicative ℤ)

/-- The base of the profinite completion of `ℤ`. -/
abbrev Zhat := NK.LocalAnabelian.Zhat

/-- The finite index normal subgroup `mℤ` of `Multiplicative ℤ`, viewed as an object of the
index category of the profinite completion of `ℤ`. -/
def mZ (m : ℕ) (hm : m ≠ 0) : FiniteIndexNormalSubgroup (Multiplicative ℤ) :=
  @FiniteIndexNormalSubgroup.ofSubgroup (Multiplicative ℤ) _
    (AddSubgroup.toSubgroup (AddSubgroup.zmultiples (m : ℤ))) _ (by
      rw [AddSubgroup.finiteIndex_toSubgroup_iff, AddSubgroup.finiteIndex_iff,
        Int.index_zmultiples]
      simp [hm])

/-- `ofAdd n` lies in `mℤ` exactly when `m ∣ n`. -/
theorem mem_mZ (m : ℕ) (hm : m ≠ 0) (n : ℤ) :
    Multiplicative.ofAdd n ∈ (mZ m hm).toSubgroup ↔ ((m : ℤ) ∣ n) := by
  rw [mZ]
  simp only [FiniteIndexNormalSubgroup.ofSubgroup, Multiplicative.mem_toSubgroup]
  exact Int.mem_zmultiples_iff

/-- **The `d`-th component of `Ẑ`.**  Projection of the profinite completion of `ℤ` onto its
finite quotient `ℤ ⧸ dℤ`, i.e. reduction modulo `d`. -/
def compHom (d : ℕ) (hd : d ≠ 0) : Zhat →* ((Multiplicative ℤ) ⧸ (mZ d hd).toSubgroup) :=
  { toFun := fun z => z.val (mZ d hd)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

/-- The `d`-th component map sends the canonical dense copy of `ℤ` to the reduction map. -/
theorem compHom_eta (d : ℕ) (hd : d ≠ 0) (m : Multiplicative ℤ) :
    compHom d hd ((ProfiniteCompletion.eta ZGrp) m) = QuotientGroup.mk m := rfl

/-- The `d`-th component map is continuous (it is a projection of the limit). -/
theorem compHom_cont (d : ℕ) (hd : d ≠ 0) : Continuous (compHom d hd) :=
  ((ProfiniteGrp.limitCone (ProfiniteCompletion.diagram ZGrp)).π.app (mZ d hd)).hom.continuous_toFun

/-- **Factoring the cyclic group through its order.**  For `x` in a finite group `Q` of order `d`,
the homomorphism `ℤ →* Q`, `k ↦ x ^ k`, kills `dℤ`, so it descends to `ℤ ⧸ dℤ`. -/
theorem ker_condition {Q : Type*} [Group Q] [Finite Q] (x : Q) :
    (mZ (orderOf x) (orderOf_pos x).ne').toSubgroup ≤ (zpowersHom Q x).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hz' : Multiplicative.ofAdd z.toAdd ∈ (mZ (orderOf x) (orderOf_pos x).ne').toSubgroup := by
    rwa [ofAdd_toAdd]
  have hdiv : ((orderOf x : ℕ) : ℤ) ∣ z.toAdd :=
    (mem_mZ (orderOf x) (orderOf_pos x).ne' z.toAdd).mp hz'
  obtain ⟨c, hc⟩ := hdiv
  rw [zpowersHom_apply, hc, zpow_mul]
  have h1 : x ^ ((orderOf x : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  rw [h1, one_zpow]

/-- **The map `ℤ ⧸ dℤ →* Q` with `1 ↦ x`**, for `x` an element of a finite group `Q` and
`d = orderOf x`. -/
def quotHom {Q : Type*} [Group Q] [Finite Q] (x : Q) :
    ((Multiplicative ℤ) ⧸ (mZ (orderOf x) (orderOf_pos x).ne').toSubgroup) →* Q :=
  QuotientGroup.lift _ (zpowersHom Q x) (ker_condition x)

/-- `quotHom x` is continuous: its source `ℤ ⧸ dℤ` is a finite quotient of `ℤ`, hence discrete,
so every map out of it is continuous. -/
theorem quotHom_cont {Q : Type*} [Group Q] [TopologicalSpace Q] [Finite Q] (x : Q) :
    Continuous (quotHom x) := continuous_of_discreteTopology

section Profinite

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]

/-- **The component map `Ẑ →* H ⧸ N`**.  For an open normal subgroup `N ≤ H` and an element
`g : H`, this is the homomorphism determined by
`(ProfiniteCompletion.eta ZGrp) k ↦ (QuotientGroup.mk' N.toSubgroup g) ^ k`
on the dense copy of `ℤ` inside `Ẑ`: it is the composite of the `d`-th component of `Ẑ`
(`d = orderOf (gN)`) with the factorisation `ℤ ⧸ dℤ →* H ⧸ N`.

Since the dense copy of `ℤ` generates `Ẑ` topologically and `H ⧸ N` is Hausdorff, this map is
*unique* with that property; this uniqueness is what makes the family `famHom g N` compatible
when `N` varies. -/
def famHom (g : H) (N : OpenNormalSubgroup H) : Zhat →* (H ⧸ N.toSubgroup) :=
  (quotHom (QuotientGroup.mk' N.toSubgroup g)).comp
    (compHom (orderOf (QuotientGroup.mk' N.toSubgroup g)) (orderOf_pos _).ne')

/-- **The defining property of `famHom`.**  On the dense copy of `ℤ` inside `Ẑ` it is the map
`k ↦ (gN) ^ k`. -/
theorem famHom_eta (g : H) (N : OpenNormalSubgroup H) (m : Multiplicative ℤ) :
    famHom g N ((ProfiniteCompletion.eta ZGrp) m) =
      (QuotientGroup.mk' N.toSubgroup g) ^ m.toAdd := by
  simp only [famHom, MonoidHom.comp_apply, compHom_eta, quotHom, QuotientGroup.lift_mk']
  exact zpowersHom_apply _ (QuotientGroup.mk' N.toSubgroup g) m

/-- `famHom g N` is continuous. -/
theorem famHom_cont (g : H) (N : OpenNormalSubgroup H) : Continuous (famHom g N) :=
  Continuous.comp
    (f := ⇑(compHom (orderOf (QuotientGroup.mk' N.toSubgroup g)) (orderOf_pos _).ne'))
    (g := ⇑(quotHom (QuotientGroup.mk' N.toSubgroup g)))
    (quotHom_cont _) (compHom_cont _ _)

/-- The canonical copy of `ℤ` inside `Ẑ` has dense range. -/
theorem denseRange_eta :
    DenseRange ((ProfiniteCompletion.eta ZGrp) : Multiplicative ℤ → Zhat) :=
  ProfiniteCompletion.denseRange ZGrp
/-- The canonical copy of the integer `k` in `Ẑ` (the dense copy of `ℤ` inside `Ẑ`). -/
noncomputable def intCastZhat (k : ℤ) : Zhat :=
  (ProfiniteCompletion.etaFn ZGrp) (Multiplicative.ofAdd k)

/-- The `d`-th component of the canonical copy of `ℤ` is the class of `k` modulo `d`. -/
theorem compHom_intCastZhat (d : ℕ) (hd : d ≠ 0) (k : ℤ) :
    compHom d hd (intCastZhat k) = QuotientGroup.mk (Multiplicative.ofAdd k) := rfl

/-- **The defining property of `famHom`**, in terms of an integer exponent. -/
theorem famHom_intCastZhat (g : H) (N : OpenNormalSubgroup H) (k : ℤ) :
    famHom g N (intCastZhat k) = (QuotientGroup.mk' N.toSubgroup g) ^ k := by
  show (quotHom (QuotientGroup.mk' N.toSubgroup g))
      (compHom (orderOf (QuotientGroup.mk' N.toSubgroup g)) (orderOf_pos _).ne' (intCastZhat k)) =
    (QuotientGroup.mk' N.toSubgroup g) ^ k
  rw [compHom_intCastZhat, quotHom, QuotientGroup.lift_mk', zpowersHom_apply, toAdd_ofAdd]

end Profinite

end

end NK.TameStructure.ProCyclic
