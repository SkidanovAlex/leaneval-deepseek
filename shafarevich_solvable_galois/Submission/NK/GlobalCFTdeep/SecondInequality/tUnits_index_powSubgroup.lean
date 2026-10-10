import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.finrank_tUnits
import Submission.NK.GroupTheory.Abelian.card_quot_lsmul_range_of_finite
import Submission.NK.GroupTheory.Abelian.card_quot_lsmul_range_of_free
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The index of the subgroup of `p`-th powers in the group of `T`-units

Let `K` be a number field containing a primitive `p`-th root of unity `ζ` (`p` prime), and let
`T` be a finite set of places of `K` containing all the infinite places.  Writing
`U(T) = NK.GlobalCFTdeep.TUnits T ⊆ Kˣ` for the group of `T`-units (the elements of `Kˣ`
which are local units outside `T`), we prove

`[U(T) : U(T)^p] = p ^ Nat.card T`,

i.e. `tUnits_index_powSubgroup`.  This is the Kummer-theoretic input of the proof of the second
inequality of global class field theory (Milne, *Class Field Theory*, VI.§6, proof of 6.9: the
group of `p`-th powers in the `S`-units has index `p ^ |S|`).

## The two ingredients

* **The rank computation.**  By Dirichlet's `S`-unit theorem
  (`NK.GlobalCFTdeep.Herbrand.finrank_tUnits`) the group `U(T)` is a finitely generated
  abelian group of `ℤ`-rank `Nat.card T - 1`.  For every finitely generated abelian group `A`
  (i.e. every finitely generated `ℤ`-module) and every `p ≠ 0` one has

  `Nat.card (A ⧸ p • ⊤) = p ^ Module.finrank ℤ A * Nat.card (Submodule.torsionBy ℤ A p)`

  (`card_quot_lsmul_range_of_moduleFinite` below): quotienting by `p` multiplies the free part by
  `(ℤ/p)^r` and replaces the torsion part by its `p`-torsion, both computations being made on the
  free quotient `A ⧸ torsion A` and on the finite torsion subgroup separately.

* **The `p`-torsion of the `T`-units.**  The `p`-torsion of `U(T)` consists of the `p`-th roots
  of unity, since a root of unity has vanishing valuation at every finite place.  As `K` contains
  a primitive `p`-th root of unity, there are exactly `p` of them
  (`card_ker_powMonoidHom_TUnits`).

Combining the two gives `[U(T) : U(T)^p] = p ^ (Nat.card T - 1) · p = p ^ Nat.card T`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality

open NK.GlobalCFT NK.GlobalCFTdeep

/-! ### `p`-th roots of unity are `T`-units -/

/-- An element of `Kˣ` with `x ^ p = 1` has vanishing valuation at every finite place, hence is a
`T`-unit for every set of places `T`. -/
theorem tUnits_of_pow_eq_one {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (T : Set (Place K)) {x : Kˣ} (hx : x ^ p = 1) : x ∈ TUnits T := by
  rw [mem_TUnits_iff_expUnit]
  intro q _
  have hxz : x ^ (p : ℤ) = 1 := by simpa using hx
  have h1 : expUnit q (x ^ (p : ℤ)) = 0 := by rw [hxz, expUnit_one]
  rw [expUnit_zpow] at h1
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact (mul_eq_zero.mp h1).resolve_left hpz

/-- The `p`-torsion of the `T`-units is the group of `p`-th roots of unity in `K`, which has
cardinality `p` when `K` contains a primitive `p`-th root of unity. -/
theorem card_ker_powMonoidHom_TUnits {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (T : Set (Place K)) :
    Nat.card (powMonoidHom (α := TUnits (L := K) T) p).ker = p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Nat.card (powMonoidHom (α := TUnits (L := K) T) p).ker =
      Nat.card ↥(rootsOfUnity p K) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun u => ⟨(u.1 : Kˣ), ?_⟩
        invFun := fun x =>
          ⟨⟨(x : Kˣ), tUnits_of_pow_eq_one p hp T ((mem_rootsOfUnity p (x : Kˣ)).mp x.2)⟩, ?_⟩
        left_inv := fun u => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
    · have h2 := MonoidHom.mem_ker.mp u.2
      have h3 := congrArg (fun z : TUnits (L := K) T => (z : Kˣ)) h2
      exact (mem_rootsOfUnity p (u.1 : Kˣ)).mpr (by simpa using h3)
    · rw [MonoidHom.mem_ker]
      exact Subtype.ext ((mem_rootsOfUnity p (x : Kˣ)).mp x.2)
  rw [hcard]
  exact IsPrimitiveRoot.card_rootsOfUnity hζ

/-! ### The index of the `p`-th powers in a finitely generated abelian group -/

/-- The `p`-torsion of `Additive G` agrees with the kernel of the `p`-th power map on `G`. -/
theorem card_torsionBy_eq_card_ker {U : Type*} [CommGroup U] (p : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (Additive U) p) = Nat.card (powMonoidHom (α := U) p).ker := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨Additive.toMul x.1, ?_⟩
      invFun := fun u => ⟨Additive.ofMul u.1, ?_⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun u => Subtype.ext rfl }
  · rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have h := (Submodule.mem_torsionBy_iff (R := ℤ) p x.1).mp x.2
    have hz : Additive.toMul x.1 ^ (p : ℤ) = (1 : U) := congrArg Additive.toMul h
    rw [zpow_natCast] at hz
    exact hz
  · rw [Submodule.mem_torsionBy_iff]
    have h := MonoidHom.mem_ker.mp u.2
    rw [powMonoidHom_apply] at h
    have key : (p : ℤ) • Additive.ofMul u.1 = Additive.ofMul (u.1 ^ (p : ℤ)) := rfl
    rw [key, zpow_natCast, h]
    rfl

/-- The subgroup spanned by the `p`-th powers of a subgroup `H` of a commutative group, viewed
inside `H`, is the range of the `p`-th power map on `H`. -/
theorem subgroupOf_map_powMonoidHom {G : Type*} [CommGroup G] (p : ℕ) (H : Subgroup G) :
    (Subgroup.map (powMonoidHom (α := G) p) H).subgroupOf H = (powMonoidHom (α := H) p).range := by
  ext1
  simp [Subgroup.mem_subgroupOf, Subtype.ext_iff]

/-- The index of the `p`-th powers in a commutative group is the cardinality of the quotient by
multiplication by `p` in the associated `ℤ`-module `Additive G`. -/
theorem index_range_powMonoidHom_eq_card_quot {U : Type*} [CommGroup U] (p : ℕ) :
    (powMonoidHom (α := U) p).range.index =
      Nat.card (Additive U ⧸ (LinearMap.lsmul ℤ (Additive U) (p : ℤ)).range) := by
  have h : (powMonoidHom (α := U) p).range.toAddSubgroup =
      ((LinearMap.lsmul ℤ (Additive U) (p : ℤ)).range).toAddSubgroup := by
    ext x
    rw [Additive.mem_toAddSubgroup, Submodule.mem_toAddSubgroup, MonoidHom.mem_range,
      LinearMap.mem_range]
    simp only [LinearMap.lsmul_apply, powMonoidHom_apply]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨Additive.ofMul a, ?_⟩
      rw [show (p : ℤ) • Additive.ofMul a = Additive.ofMul (a ^ (p : ℤ)) from rfl,
        zpow_natCast, ha]
      rfl
    · rintro ⟨b, hb⟩
      refine ⟨Additive.toMul b, ?_⟩
      rw [← hb]
      rw [show Additive.toMul ((p : ℤ) • b) = Additive.toMul b ^ (p : ℤ) from rfl,
        zpow_natCast]
  rw [Subgroup.index]
  show Nat.card (Additive U ⧸ ((powMonoidHom (α := U) p).range).toAddSubgroup)
      = Nat.card (Additive U ⧸ (LinearMap.lsmul ℤ (Additive U) (p : ℤ)).range)
  rw [h]
  rfl

/-- **The index of the `p`-th powers in a finitely generated abelian group.**  For a finitely
generated abelian group `A` and `p ≠ 0`, the quotient of `A` by the multiples of `p` has
cardinality `p ^ r · |A[p]|`, where `r` is the `ℤ`-rank of `A` (the rank of its free quotient)
and `A[p]` is its `p`-torsion subgroup.

Indeed `A` is an extension of a free `ℤ`-module of rank `r` by its (finite) torsion subgroup, so
`A/pA` is an extension of `(ℤ/p)^r` by `T/pT`, and `T/pT ≅ T[p] = A[p]` for finite `T`. -/
theorem card_quot_lsmul_range_of_moduleFinite {A : Type*} [AddCommGroup A] [Module.Finite ℤ A]
    (p : ℕ) (hp : p ≠ 0) :
    Nat.card (A ⧸ (LinearMap.lsmul ℤ A (p : ℤ)).range) =
      p ^ Module.finrank ℤ A * Nat.card (Submodule.torsionBy ℤ A p) := by
  classical
  set S : Submodule ℤ A := (LinearMap.lsmul ℤ A (p : ℤ)).range with hS
  set T : Submodule ℤ A := Submodule.torsion ℤ A with hT
  have hTle : T ≤ Submodule.torsion ℤ A := le_of_eq hT
  haveI : Module.Finite ℤ ↥T := inferInstance
  haveI hTfin : Finite ↥T := Module.finite_of_fg_torsion ↥T (fun x => by
    obtain ⟨a, hax⟩ := x.2
    exact ⟨a, Subtype.ext hax⟩)
  -- `|A/S| = |(S ⊔ T)/S| · |A/(S ⊔ T)|`
  have h1 : Nat.card (A ⧸ S) =
      Nat.card ((S ⊔ T).map S.mkQ) * Nat.card (A ⧸ (S ⊔ T)) :=
    (Submodule.card_quotient_mul_card_quotient (S ⊔ T) S le_sup_left).symm
  -- the image of `S ⊔ T` in `A/S` is the image of `T`
  have h2 : (S ⊔ T).map S.mkQ = T.map S.mkQ := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  -- `T/(S ⊓ T) ≅ (S ⊔ T)/S` (second isomorphism theorem)
  have h3 : Nat.card (T.map S.mkQ) = Nat.card (↥T ⧸ S.comap T.subtype) := by
    have hker : (S.mkQ.comp T.subtype).ker = S.comap T.subtype := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have hran : (S.mkQ.comp T.subtype).range = T.map S.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [← hran, ← hker]
    exact (Nat.card_congr (LinearMap.quotKerEquivRange (S.mkQ.comp T.subtype)).toEquiv).symm
  -- inside the torsion, `p • A ∩ A[p^∞] = p • A[p^∞]`
  have h4 : S.comap T.subtype = (LinearMap.lsmul ℤ ↥T (p : ℤ)).range := by
    ext t
    constructor
    · intro ht
      rw [Submodule.mem_comap, hS, LinearMap.mem_range] at ht
      obtain ⟨a, ha⟩ := ht
      have haT : a ∈ T := by
        have hzero : T.mkQ a = 0 := by
          have hsm : (p : ℤ) • T.mkQ a = 0 := by
            rw [← map_smul, ← LinearMap.lsmul_apply, ha, Submodule.mkQ_apply,
              Submodule.Quotient.mk_eq_zero]
            exact t.2
          exact (smul_eq_zero_iff_right (R := ℤ) (M := A ⧸ T)
            (show (p : ℤ) ≠ 0 by exact_mod_cast hp)).mp hsm
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
      exact ⟨⟨a, haT⟩, Subtype.ext ha⟩
    · rintro ⟨b, hb⟩
      rw [Submodule.mem_comap, hS, LinearMap.mem_range]
      exact ⟨(b : A), congrArg (fun z : ↥T => (z : A)) hb⟩
  -- the finite case, and `T[p] = A[p]`
  have h5a : Nat.card (↥T ⧸ (LinearMap.lsmul ℤ ↥T (p : ℤ)).range) =
      Nat.card (Submodule.torsionBy ℤ ↥T p) :=
    NK.GroupTheory.Abelian.card_quot_lsmul_range_of_finite (T := ↥T) p
  have h5b : Nat.card (Submodule.torsionBy ℤ ↥T p) =
      Nat.card (Submodule.torsionBy ℤ A p) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨(x.1 : A), ?_⟩
        invFun := fun y => ⟨⟨(y.1 : A), ?_⟩, ?_⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl }
    · exact (Submodule.mem_torsionBy_iff (R := ℤ) p (x.1 : A)).mpr
        (congrArg (fun z : ↥T => (z : A))
          ((Submodule.mem_torsionBy_iff (R := ℤ) p x.1).mp x.2))
    · refine ⟨⟨(p : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr ?_⟩, ?_⟩
      · exact_mod_cast hp
      · exact (Submodule.mem_torsionBy_iff (R := ℤ) p y.1).mp y.2
    · have h := (Submodule.mem_torsionBy_iff (R := ℤ) p y.1).mp y.2
      exact (Submodule.mem_torsionBy_iff (R := ℤ) p _).mpr (Subtype.ext h)
  -- the free case, using `finrank (A ⧸ T) = finrank A`
  have h6 : Nat.card (A ⧸ (S ⊔ T)) = p ^ Module.finrank ℤ A := by
    have hmap : (S ⊔ T).map T.mkQ = (LinearMap.lsmul ℤ (A ⧸ T) (p : ℤ)).range := by
      have hcomp : T.mkQ.comp (LinearMap.lsmul ℤ A (p : ℤ)) =
          (LinearMap.lsmul ℤ (A ⧸ T) (p : ℤ)).comp T.mkQ := by
        ext x
        simp [LinearMap.comp_apply]
      rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq, hS,
        ← LinearMap.range_comp (LinearMap.lsmul ℤ A (p : ℤ)) T.mkQ, hcomp,
        LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top]
    rw [← Nat.card_congr
      (Submodule.quotientQuotientEquivQuotient (S := T) (T := S ⊔ T) le_sup_right).toEquiv]
    rw [hmap, NK.GroupTheory.Abelian.card_quot_lsmul_range_of_free (F := A ⧸ T) p hp,
      finrank_quotient_eq_of_le_torsion hTle]
  calc Nat.card (A ⧸ (LinearMap.lsmul ℤ A (p : ℤ)).range)
      = Nat.card (A ⧸ S) := by rw [hS]
    _ = Nat.card ((S ⊔ T).map S.mkQ) * Nat.card (A ⧸ (S ⊔ T)) := h1
    _ = Nat.card (T.map S.mkQ) * Nat.card (A ⧸ (S ⊔ T)) := by rw [h2]
    _ = Nat.card (↥T ⧸ S.comap T.subtype) * Nat.card (A ⧸ (S ⊔ T)) := by rw [h3]
    _ = Nat.card (↥T ⧸ (LinearMap.lsmul ℤ ↥T (p : ℤ)).range) * p ^ Module.finrank ℤ A := by
        rw [h4, h6]
    _ = Nat.card (Submodule.torsionBy ℤ ↥T p) * p ^ Module.finrank ℤ A := by rw [h5a]
    _ = Nat.card (Submodule.torsionBy ℤ A p) * p ^ Module.finrank ℤ A := by rw [h5b]
    _ = p ^ Module.finrank ℤ A * Nat.card (Submodule.torsionBy ℤ A p) := by rw [mul_comm]

/-! ### The index of the `p`-th powers in the `T`-units -/

theorem tUnits_index_powSubgroup {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (T : Finset (NK.GlobalCFT.Place K))
    (hTinf : ∀ w : NK.GlobalCFT.Place K, w.IsInfinite → w ∈ T) :
    ((Subgroup.map (powMonoidHom p) (NK.GlobalCFTdeep.TUnits (L := K) (T : Set (NK.GlobalCFT.Place K)))).subgroupOf
        (NK.GlobalCFTdeep.TUnits (L := K) (T : Set (NK.GlobalCFT.Place K)))).index = p ^ Nat.card T := by
  classical
  set U := NK.GlobalCFTdeep.TUnits (L := K) (T : Set (NK.GlobalCFT.Place K)) with hU
  haveI hfin : Module.Finite ℤ (Additive U) :=
    (NK.GlobalCFTdeep.Herbrand.finrank_tUnits (L := K) (T : Set (NK.GlobalCFT.Place K))
      (fun w hw => hTinf w hw)).1
  have hrank : Module.finrank ℤ (Additive U) =
      Nat.card (T : Set (NK.GlobalCFT.Place K)) - 1 :=
    (NK.GlobalCFTdeep.Herbrand.finrank_tUnits (L := K) (T : Set (NK.GlobalCFT.Place K))
      (fun w hw => hTinf w hw)).2
  have hcardT : Nat.card (T : Set (NK.GlobalCFT.Place K)) = Nat.card T := rfl
  have hpos : 1 ≤ Nat.card T := by
    obtain ⟨w⟩ := Fintype.card_pos_iff.mp (NK.GlobalCFTdeep.one_le_card_infinitePlace (L := K))
    have : 0 < Nat.card T := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨NK.GlobalCFT.Place.ofInfinite w, hTinf _ trivial⟩
    omega
  calc ((Subgroup.map (powMonoidHom p) U).subgroupOf U).index
      = (powMonoidHom (α := U) p).range.index := by
        rw [NK.GlobalCFTdeep.SecondInequality.subgroupOf_map_powMonoidHom]
    _ = Nat.card (Additive U ⧸ (LinearMap.lsmul ℤ (Additive U) (p : ℤ)).range) :=
        NK.GlobalCFTdeep.SecondInequality.index_range_powMonoidHom_eq_card_quot (U := U) p
    _ = p ^ Module.finrank ℤ (Additive U) *
          Nat.card (Submodule.torsionBy ℤ (Additive U) p) :=
        NK.GlobalCFTdeep.SecondInequality.card_quot_lsmul_range_of_moduleFinite p hp.ne_zero
    _ = p ^ (Nat.card T - 1) * p := by
        rw [hrank, hcardT, NK.GlobalCFTdeep.SecondInequality.card_torsionBy_eq_card_ker,
          NK.GlobalCFTdeep.SecondInequality.card_ker_powMonoidHom_TUnits p hp hζ
            (T : Set (NK.GlobalCFT.Place K))]
    _ = p ^ Nat.card T := by
        rw [← pow_succ, Nat.sub_add_cancel hpos]

end NK.GlobalCFTdeep.SecondInequality
