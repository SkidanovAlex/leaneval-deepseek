import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.exists_expUnit_eq_single
import Submission.NK.GlobalCFTdeep.Herbrand.ker_tUnitsVal
import Submission.NK.GlobalCFTdeep.Herbrand.tUnitsVal_range_finiteIndex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Dirichlet's `S`-unit theorem for the `T`-units of a number field

For a number field `L` and a finite set of places `T` containing all the infinite places, the group
of `T`-units `U(T) ⊆ Lˣ` (the units which are local units outside `T`) is finitely generated of
rank `|T| - 1` (Dirichlet's `S`-unit theorem).  In the form required here:

`Module.Finite ℤ (Additive (TUnits T))` and
`Module.finrank ℤ (Additive (TUnits T)) = Nat.card T - 1`.

## The route

The valuation map `tUnitsVal T : Additive (TUnits T) →ₗ[ℤ] (SSet T → ℤ)` (where `SSet T` are the
finite places lying in `T`) has

* kernel the units of `𝓞 L` (`ker_tUnitsVal`), whose `ℤ`-rank is `card (InfinitePlace L) - 1`
  (Dirichlet's unit theorem, `NumberField.Units.finrank_eq`), and
* image of finite index in `ℤ^{SSet T}` (`tUnitsVal_range_finiteIndex`), built from the fact that
  every finite place has a power which is principal (`exists_expUnit_eq_single`, finiteness of the
  ideal class group).

Rank additivity for the exact sequence of the valuation map then gives
`finrank = card (SSet T) + (card (InfinitePlace L) - 1) = |T| - 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {L : Type} [Field L] [NumberField L]

/-- The finite places lying in a finite set of places form a finite type. -/
instance instFiniteSSet (T : Set (Place L)) [Finite T] : Finite (SSet T) :=
  Finite.of_injective (fun q : SSet T => (⟨Place.ofFinite q.1, q.2⟩ : T)) fun _ _ h =>
    Subtype.ext (Place.ofFinite_inj.mp (Subtype.ext_iff.mp h))

/-- The places in `T` are the finite places in `T` together with the infinite places (all of which
lie in `T`). -/
noncomputable def tUnitsPlaceEquiv (T : Set (Place L))
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) : ↥T ≃ SSet T ⊕ InfinitePlace L where
  toFun x := match x with
    | ⟨Sum.inl w, _⟩ => Sum.inr w
    | ⟨Sum.inr q, hq⟩ => Sum.inl ⟨q, hq⟩
  invFun y := match y with
    | Sum.inl q => ⟨Place.ofFinite q.1, q.2⟩
    | Sum.inr w => ⟨Place.ofInfinite w, hTinf (Place.ofInfinite w) trivial⟩
  left_inv := by rintro ⟨(_ | _), _⟩ <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

theorem natCard_eq_of_sset (T : Set (Place L)) [Finite T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T) :
    Nat.card T = Nat.card (SSet T) + Fintype.card (InfinitePlace L) := by
  haveI : Fintype (SSet T) := Fintype.ofFinite _
  haveI : Fintype ↥T := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := ↥T), Fintype.card_congr (tUnitsPlaceEquiv T hTinf),
    Fintype.card_sum, Nat.card_eq_fintype_card]

theorem one_le_card_infinitePlace : 1 ≤ Fintype.card (InfinitePlace L) :=
  Fintype.card_pos_iff.mpr inferInstance

/-- The kernel of the valuation map has the rank of the unit group of `𝓞 L`, namely
`card (InfinitePlace L) - 1`. -/
theorem tUnits_ker_finrank (T : Set (Place L))
    (hker : LinearMap.ker (tUnitsVal T) = LinearMap.range (unitsToTUnits T)) :
    Module.finrank ℤ (LinearMap.ker (tUnitsVal T)) = Fintype.card (InfinitePlace L) - 1 := by
  have e : Additive ((𝓞 L)ˣ) ≃ₗ[ℤ] LinearMap.ker (tUnitsVal T) :=
    (LinearEquiv.ofInjective (unitsToTUnits T) (unitsToTUnits_injective T)).trans
      (LinearEquiv.ofEq _ _ hker.symm)
  rw [← LinearEquiv.finrank_eq e, NumberField.Units.finrank_eq, NumberField.Units.rank]

theorem tUnits_ker_moduleFinite (T : Set (Place L))
    (hker : LinearMap.ker (tUnitsVal T) = LinearMap.range (unitsToTUnits T)) :
    Module.Finite ℤ (LinearMap.ker (tUnitsVal T)) :=
  Module.Finite.equiv ((LinearEquiv.ofInjective (unitsToTUnits T)
    (unitsToTUnits_injective T)).trans (LinearEquiv.ofEq _ _ hker.symm))

/-- If the valuation map hits `N • ⊤`, then its image has rank `card (SSet T)`. -/
theorem tUnits_range_finrank (T : Set (Place L)) [Finite T]
    (hfin : ∃ N : ℕ, 0 < N ∧ ∀ c : SSet T → ℤ, ∃ x : Additive (TUnits T),
      (N : ℤ) • c = tUnitsVal T x) :
    Module.finrank ℤ (LinearMap.range (tUnitsVal T)) = Nat.card (SSet T) := by
  haveI : Fintype (SSet T) := Fintype.ofFinite _
  obtain ⟨N, hN, hc⟩ := hfin
  have hrank : Module.rank ℤ ((SSet T → ℤ) ⧸ LinearMap.range (tUnitsVal T)) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    refine ⟨(N : ℤ), ?_, ?_⟩
    · exact_mod_cast hN.ne'
    · refine Submodule.Quotient.induction_on (LinearMap.range (tUnitsVal T)) x (fun c => ?_)
      rw [← Submodule.mkQ_apply, ← LinearMap.map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      obtain ⟨y, hy⟩ := hc c
      exact hy ▸ LinearMap.mem_range_self _ _
  have hfq : Module.finrank ℤ ((SSet T → ℤ) ⧸ LinearMap.range (tUnitsVal T)) = 0 :=
    Module.finrank_eq_of_rank_eq (n := 0) (by simp [hrank])
  have hd := Submodule.finrank_quotient_add_finrank (LinearMap.range (tUnitsVal T))
  rw [hfq, zero_add, Module.finrank_pi ℤ] at hd
  rw [Nat.card_eq_fintype_card]
  exact hd

/-- The `T`-units are a finitely generated abelian group. -/
theorem tUnits_moduleFinite (T : Set (Place L)) [Finite T]
    (hker : LinearMap.ker (tUnitsVal T) = LinearMap.range (unitsToTUnits T))
    (hfin : ∃ N : ℕ, 0 < N ∧ ∀ c : SSet T → ℤ, ∃ x : Additive (TUnits T),
      (N : ℤ) • c = tUnitsVal T x) :
    Module.Finite ℤ (Additive (TUnits T)) := by
  haveI : Fintype (SSet T) := Fintype.ofFinite _
  haveI hK : Module.Finite ℤ (LinearMap.ker (tUnitsVal T)) := tUnits_ker_moduleFinite T hker
  haveI hW : Module.Finite ℤ (LinearMap.range (tUnitsVal T)) := by
    haveI : IsNoetherian ℤ (SSet T → ℤ) := inferInstance
    exact Module.Finite.iff_fg.mpr (isNoetherian_def.mp inferInstance _)
  refine Module.Finite.of_exact
    (f := (LinearMap.ker (tUnitsVal T)).subtype)
    (g := LinearMap.rangeRestrict (tUnitsVal T)) ?_ ?_
  · rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]
  · intro w
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp w.2
    exact ⟨x, Subtype.ext hx⟩

/-- From a unit supported at a single finite place for every place, build a family of `T`-units
with a common multiplier `N`: `u q` has valuation `N` at `q` and `0` at every other finite place
in `T`. -/
theorem tUnits_family_diag (T : Set (Place L)) [Finite T]
    (hsingle : ∀ q : HeightOneSpectrum (𝓞 L), ∃ N : ℕ, 0 < N ∧ ∃ a : Lˣ, expUnit q a = N ∧
      ∀ q' : HeightOneSpectrum (𝓞 L), q' ≠ q → expUnit q' a = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ a : SSet T → TUnits T,
      (∀ q : SSet T, expUnit q.1 ((a q : TUnits T) : Lˣ) = (N : ℤ)) ∧
      (∀ q q' : SSet T, q' ≠ q → expUnit q'.1 ((a q : TUnits T) : Lˣ) = 0) := by
  classical
  haveI : Fintype (SSet T) := Fintype.ofFinite _
  let Nq : SSet T → ℕ := fun q => Classical.choose (hsingle q.1)
  have hNq : ∀ q, 0 < Nq q := fun q => (Classical.choose_spec (hsingle q.1)).1
  let aq : SSet T → Lˣ := fun q => Classical.choose (Classical.choose_spec (hsingle q.1)).2
  have haq : ∀ q, expUnit q.1 (aq q) = (Nq q : ℤ) ∧
      ∀ q' : HeightOneSpectrum (𝓞 L), q' ≠ q.1 → expUnit q' (aq q) = 0 :=
    fun q => Classical.choose_spec (Classical.choose_spec (hsingle q.1)).2
  let Mq : SSet T → ℤ := fun q => (((Finset.univ : Finset (SSet T)).erase q).prod Nq : ℕ)
  have hMq : ∀ q, Mq q * (Nq q : ℤ) = ((Finset.univ : Finset (SSet T)).prod Nq : ℕ) := by
    intro q
    have hprod : ((Finset.univ : Finset (SSet T)).erase q).prod Nq * Nq q =
        (Finset.univ : Finset (SSet T)).prod Nq :=
      Finset.prod_erase_mul _ _ (Finset.mem_univ q)
    have hMq' : Mq q = (((Finset.univ : Finset (SSet T)).erase q).prod Nq : ℕ) := rfl
    rw [hMq', ← Nat.cast_mul, hprod]
  refine ⟨(Finset.univ : Finset (SSet T)).prod Nq, Finset.prod_pos (fun q _ => hNq q),
    fun q => ⟨aq q ^ (Mq q), ?_⟩, ?_, ?_⟩
  · rw [mem_TUnits_iff_expUnit]
    intro q' hq'
    rw [expUnit_zpow]
    have hne : q' ≠ q.1 := by
      intro h
      exact hq' (by rw [← mem_SSet, h]; exact q.2)
    rw [(haq q).2 q' hne, mul_zero]
  · intro q
    rw [expUnit_zpow, (haq q).1, hMq q]
  · intro q q' hq'
    rw [expUnit_zpow]
    have hne : q'.1 ≠ q.1 := fun h => hq' (Subtype.ext h)
    rw [(haq q).2 q'.1 hne, mul_zero]

end NK.GlobalCFTdeep

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT NK.GlobalCFTdeep

theorem finrank_tUnits {L : Type} [Field L] [NumberField L] (T : Set (NK.GlobalCFT.Place L))
    [Finite T] (hTinf : ∀ w : NK.GlobalCFT.Place L, w.IsInfinite → w ∈ T) :
    Module.Finite ℤ (Additive (NK.GlobalCFTdeep.TUnits (L := L) T)) ∧
      Module.finrank ℤ (Additive (NK.GlobalCFTdeep.TUnits (L := L) T)) = Nat.card T - 1 := by
  classical
  haveI : Fintype (NK.GlobalCFTdeep.SSet T) := Fintype.ofFinite _
  obtain ⟨N, hN, adiag, hdiagN, hdiag0⟩ :=
    NK.GlobalCFTdeep.tUnits_family_diag T fun q => NK.GlobalCFTdeep.Herbrand.exists_expUnit_eq_single q
  have hfin : ∃ N : ℕ, 0 < N ∧ ∀ c : NK.GlobalCFTdeep.SSet T → ℤ,
      ∃ x : Additive (NK.GlobalCFTdeep.TUnits (L := L) T),
        (N : ℤ) • c = NK.GlobalCFTdeep.tUnitsVal T x :=
    ⟨N, hN, fun c => NK.GlobalCFTdeep.Herbrand.tUnitsVal_range_finiteIndex T hN adiag hdiagN hdiag0 c⟩
  have hker : LinearMap.ker (NK.GlobalCFTdeep.tUnitsVal T) =
      LinearMap.range (NK.GlobalCFTdeep.unitsToTUnits (L := L) T) :=
    NK.GlobalCFTdeep.Herbrand.ker_tUnitsVal T
  haveI : Module.Finite ℤ (Additive (NK.GlobalCFTdeep.TUnits (L := L) T)) :=
    NK.GlobalCFTdeep.tUnits_moduleFinite T hker hfin
  refine ⟨inferInstance, ?_⟩
  have hfr := NK.GlobalCFTdeep.tUnits_range_finrank T hfin
  have hfk := NK.GlobalCFTdeep.tUnits_ker_finrank T hker
  have hd := Submodule.finrank_quotient_add_finrank
    (LinearMap.ker (NK.GlobalCFTdeep.tUnitsVal T))
  have hq : Module.finrank ℤ (Additive (NK.GlobalCFTdeep.TUnits (L := L) T) ⧸
      LinearMap.ker (NK.GlobalCFTdeep.tUnitsVal T)) =
      Module.finrank ℤ (LinearMap.range (NK.GlobalCFTdeep.tUnitsVal T)) :=
    LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (NK.GlobalCFTdeep.tUnitsVal T))
  have hval : Module.finrank ℤ (Additive (NK.GlobalCFTdeep.TUnits (L := L) T)) =
      Nat.card (NK.GlobalCFTdeep.SSet T) + (Nat.card (InfinitePlace L) - 1) := by
    rw [← hd, hq, hfr, hfk, Nat.card_eq_fintype_card (α := InfinitePlace L)]
  rw [hval, NK.GlobalCFTdeep.natCard_eq_of_sset T hTinf,
    Nat.card_eq_fintype_card (α := InfinitePlace L)]
  have hm : 1 ≤ Fintype.card (InfinitePlace L) :=
    NK.GlobalCFTdeep.one_le_card_infinitePlace
  omega

end NK.GlobalCFTdeep.Herbrand
