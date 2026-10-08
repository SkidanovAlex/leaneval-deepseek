import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ZassenhausSuzuki

open scoped Classical

theorem card_sigma_fiber_over_class {G : Type} [Group G] [Finite G] (X : Set G)
    (hX : ∀ g : G, ∀ x : G, x ∈ X → g * x * g⁻¹ ∈ X) (y : ConjClasses G)
    (hy : (y.carrier ∩ X).Nonempty) :
    Nat.card (Σ x : {x : {x : G // x ∈ X} // ConjClasses.mk x.1 = y},
        ↥(Subgroup.centralizer ({x.1.1} : Set G))) = Nat.card G := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨x₀, hx₀y, hx₀X⟩ := hy
  have hx₀mk : ConjClasses.mk x₀ = y := ConjClasses.mem_carrier_iff_mk_eq.mp hx₀y
  -- `X` is a union of conjugacy classes, so it contains the whole class `y`.
  have hsub : y.carrier ⊆ X := by
    intro w hwy
    have hwmk : ConjClasses.mk w = y := ConjClasses.mem_carrier_iff_mk_eq.mp hwy
    have hisconj : IsConj w x₀ :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (by rw [hwmk, hx₀mk])
    obtain ⟨c, hc⟩ := isConj_iff.mp hisconj
    have hw : w = c⁻¹ * x₀ * c := by rw [← hc]; group
    rw [hw]
    simpa using hX c⁻¹ x₀ hx₀X
  -- Orbit-stabilizer in terms of the centralizer.
  have hOS : ∀ a : G, Nat.card ↥(MulAction.orbit (ConjAct G) a) *
      Nat.card ↥(Subgroup.centralizer ({a} : Set G)) = Nat.card G := by
    intro a
    haveI : Fintype (ConjAct G) := Fintype.ofFinite (ConjAct G)
    haveI : Fintype ↥(MulAction.orbit (ConjAct G) a) := Fintype.ofFinite _
    haveI : Fintype ↥(MulAction.stabilizer (ConjAct G) a) := Fintype.ofFinite _
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) a
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
    rw [Subgroup.nat_card_centralizer_nat_card_stabilizer a, h]
    exact Nat.card_congr ConjAct.ofConjAct.toEquiv
  -- All elements of the class `y` have centralizers of the same cardinality.
  have hsame : ∀ z : ↥y.carrier, Nat.card ↥(Subgroup.centralizer ({z.1} : Set G))
      = Nat.card ↥(Subgroup.centralizer ({x₀} : Set G)) := by
    intro z
    have hzmk : ConjClasses.mk z.1 = y := ConjClasses.mem_carrier_iff_mk_eq.mp z.2
    have horbit : MulAction.orbit (ConjAct G) z.1 = MulAction.orbit (ConjAct G) x₀ := by
      rw [ConjAct.orbit_eq_carrier_conjClasses, ConjAct.orbit_eq_carrier_conjClasses,
        hzmk, hx₀mk]
    have h1 := hOS z.1
    have h2 := hOS x₀
    rw [horbit] at h1
    haveI : Nonempty ↥(MulAction.orbit (ConjAct G) x₀) :=
      ⟨x₀, MulAction.mem_orbit_self x₀⟩
    exact Nat.mul_left_cancel Nat.card_pos (h1.trans h2.symm)
  -- Sum of the cardinalities of the fibres.
  have hsum : Nat.card (Σ z : ↥y.carrier, ↥(Subgroup.centralizer ({z.1} : Set G)))
      = Nat.card ↥y.carrier * Nat.card ↥(Subgroup.centralizer ({x₀} : Set G)) := by
    haveI : Fintype ↥y.carrier := Fintype.ofFinite _
    rw [Nat.card_sigma, Finset.sum_congr rfl (fun z _ => hsame z), Finset.sum_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul, Nat.cast_id]
  -- The orbit-stabilizer identity for `x₀`.
  have hGH : Nat.card ↥y.carrier * Nat.card ↥(Subgroup.centralizer ({x₀} : Set G))
      = Nat.card G := by
    have h2 := hOS x₀
    rw [ConjAct.orbit_eq_carrier_conjClasses, hx₀mk] at h2
    exact h2
  -- Reindex the sigma type.
  let e : {x : {x : G // x ∈ X} // ConjClasses.mk x.1 = y} ≃ ↥y.carrier :=
    { toFun := fun x => ⟨x.1.1, ConjClasses.mem_carrier_iff_mk_eq.mpr x.2⟩
      invFun := fun z => ⟨⟨z.1, hsub z.2⟩, ConjClasses.mem_carrier_iff_mk_eq.mp z.2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun z => Subtype.ext rfl }
  have hE : Nat.card (Σ x : {x : {x : G // x ∈ X} // ConjClasses.mk x.1 = y},
        ↥(Subgroup.centralizer ({x.1.1} : Set G)))
      = Nat.card (Σ z : ↥y.carrier, ↥(Subgroup.centralizer ({z.1} : Set G))) :=
    Nat.card_congr (Equiv.sigmaCongr e (fun _ => Equiv.refl _))
  rw [hE, hsum, hGH]

end Work.ZassenhausSuzuki
