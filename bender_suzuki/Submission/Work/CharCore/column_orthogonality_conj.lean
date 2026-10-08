import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.classFun_eq_sum_irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.column_orthogonality_conj`

Column orthogonality of the irreducible complex characters of a finite group: for
`g, h : G` with `g` conjugate to `h`,

`∑_{χ ∈ Irr G} χ g * conj (χ h) = |C_G(g)|`.

The proof uses the second orthogonality relation for the class function `δ` which is `1`
on the conjugacy class of `g` and `0` elsewhere.  Expanding `δ` in the orthonormal basis
`Irr G` of the class functions (`Work.CharCore.classFun_eq_sum_irr`) gives
`δ = ∑_χ ⟨δ, χ⟩ χ` with `⟨δ, χ⟩ = |G|⁻¹ · |C| · conj (χ g)` (`C` the class of `g`), and
evaluating at `h` (which lies in `C`) gives
`1 = |G|⁻¹ · |C| · ∑_χ conj (χ g) * χ h`; conjugating and using the orbit–stabiliser
relation `|C| · |C_G(g)| = |G|` yields the claim.
-/

noncomputable section

open Classical Finset

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- Membership in the conjugacy class of `g`. -/
theorem mem_conjClass_carrier (g x : G) :
    x ∈ (ConjClasses.mk g).carrier ↔ IsConj x g := by
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]

/-- The indicator of a conjugacy class is a class function. -/
theorem isClassFun_indicator_conjClass (g : G) :
    IsClassFun (Set.indicator (ConjClasses.mk g).carrier (fun _ : G => (1 : ℂ))) := by
  intro x y
  have hconj : IsConj (y * x * y⁻¹) x := IsConj.symm (isConj_iff.mpr ⟨y, rfl⟩)
  have hiff : (y * x * y⁻¹) ∈ (ConjClasses.mk g).carrier ↔
      x ∈ (ConjClasses.mk g).carrier := by
    rw [mem_conjClass_carrier, mem_conjClass_carrier]
    exact ⟨fun h' => hconj.symm.trans h', fun h' => hconj.trans h'⟩
  by_cases hx : x ∈ (ConjClasses.mk g).carrier
  · rw [Set.indicator_of_mem (hiff.mpr hx) (fun _ : G => (1 : ℂ)),
      Set.indicator_of_mem hx (fun _ : G => (1 : ℂ))]
  · rw [Set.indicator_of_notMem (fun h' => hx (hiff.mp h')) (fun _ : G => (1 : ℂ)),
      Set.indicator_of_notMem hx (fun _ : G => (1 : ℂ))]

/-- A class function is constant on a conjugacy class. -/
theorem eq_of_mem_conjClass {χ : G → ℂ} (hχ : IsClassFun χ) {g x : G}
    (hx : x ∈ (ConjClasses.mk g).carrier) : χ x = χ g := by
  obtain ⟨a, ha⟩ := isConj_iff.mp ((mem_conjClass_carrier g x).mp hx)
  rw [← ha]
  exact (hχ x a).symm

/-- The inner product of the indicator of the conjugacy class of `g` with an irreducible
character `χ`. -/
theorem cfInner_indicator_conjClass (g : G) (χ : G → ℂ) (hχ : χ ∈ Irr G) :
    cfInner (Set.indicator (ConjClasses.mk g).carrier (fun _ : G => (1 : ℂ))) χ
      = ((Fintype.card G : ℂ)⁻¹ * ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ))
          * starRingEnd ℂ (χ g) := by
  have hclassχ : IsClassFun χ := isClassFun_of_mem_Irr hχ
  rw [cfInner_apply]
  have hpointwise : ∀ x : G,
      (Set.indicator (ConjClasses.mk g).carrier (fun _ : G => (1 : ℂ))) x
        * starRingEnd ℂ (χ x)
        = if x ∈ (ConjClasses.mk g).carrier then starRingEnd ℂ (χ g) else 0 := by
    intro x
    by_cases hx : x ∈ (ConjClasses.mk g).carrier
    · rw [Set.indicator_of_mem hx (fun _ : G => (1 : ℂ)), one_mul, if_pos hx,
        eq_of_mem_conjClass hclassχ hx]
    · rw [Set.indicator_of_notMem hx (fun _ : G => (1 : ℂ)), zero_mul, if_neg hx]
  rw [Finset.sum_congr rfl (fun x _ => hpointwise x)]
  have hstep2 : (∑ x : G, (if x ∈ (ConjClasses.mk g).carrier
        then starRingEnd ℂ (χ g) else 0))
      = (∑ x : G, (if x ∈ (ConjClasses.mk g).carrier then (1 : ℂ) else 0))
          * starRingEnd ℂ (χ g) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ (ConjClasses.mk g).carrier <;> simp [hx]
  rw [hstep2]
  have hcount : (∑ x : G, (if x ∈ (ConjClasses.mk g).carrier then (1 : ℂ) else 0))
      = ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ) := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    rw [← Fintype.card_subtype (fun x : G => x ∈ (ConjClasses.mk g).carrier),
      Nat.card_eq_fintype_card]
  rw [hcount, mul_assoc]

theorem column_orthogonality_conj {G : Type*} [Group G] [Fintype G] {g h : G} (hh : IsConj g h) :
    ∑ χ ∈ Irr G, χ g * starRingEnd ℂ (χ h) =
      ((Nat.card (Subgroup.centralizer ({g} : Set G)) : ℕ) : ℂ) := by
  classical
  set S : ℂ := ∑ χ ∈ Irr G, χ g * starRingEnd ℂ (χ h) with hSdef
  have hmemg : g ∈ (ConjClasses.mk g).carrier := (mem_conjClass_carrier g g).mpr (IsConj.refl g)
  have hmemh : h ∈ (ConjClasses.mk g).carrier := (mem_conjClass_carrier g h).mpr hh.symm
  -- orbit–stabiliser: `|C| * |C_G(g)| = |G|`
  have horbitcard : Nat.card (MulAction.orbit (ConjAct G) g)
      = Nat.card (ConjClasses.mk g).carrier :=
    Nat.card_congr (Set.equivOfEq (ConjAct.orbit_eq_carrier_conjClasses g))
  have hstab : Nat.card (MulAction.stabilizer (ConjAct G) g)
      = Nat.card (Subgroup.centralizer ({g} : Set G)) :=
    (Subgroup.nat_card_centralizer_nat_card_stabilizer g).symm
  have horbit : Nat.card (MulAction.orbit (ConjAct G) g)
      * Nat.card (MulAction.stabilizer (ConjAct G) g) = Nat.card G := by
    have h' := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card] at h'
  have hcm : Nat.card (ConjClasses.mk g).carrier
      * Nat.card (Subgroup.centralizer ({g} : Set G)) = Nat.card G := by
    rw [← horbitcard, ← hstab]
    exact horbit
  -- expansion of the class indicator
  have heval : (1 : ℂ) = ∑ χ ∈ Irr G,
      cfInner (Set.indicator (ConjClasses.mk g).carrier (fun _ : G => (1 : ℂ))) χ * χ h := by
    have h' := congrFun (classFun_eq_sum_irr (isClassFun_indicator_conjClass g)) h
    rw [Set.indicator_of_mem hmemh (fun _ : G => (1 : ℂ))] at h'
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h'
  have hstep : (∑ χ ∈ Irr G,
        cfInner (Set.indicator (ConjClasses.mk g).carrier (fun _ : G => (1 : ℂ))) χ * χ h)
      = ((Fintype.card G : ℂ)⁻¹ * ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ))
          * (∑ χ ∈ Irr G, starRingEnd ℂ (χ g) * χ h) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [cfInner_indicator_conjClass g χ hχ]
    ring
  have hevalT : (1 : ℂ)
      = ((Fintype.card G : ℂ)⁻¹ * ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ))
          * (∑ χ ∈ Irr G, starRingEnd ℂ (χ g) * χ h) := heval.trans hstep
  -- conjugate
  have hA : starRingEnd ℂ
        ((Fintype.card G : ℂ)⁻¹ * ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ))
      = (Fintype.card G : ℂ)⁻¹ * ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ) := by
    simp
  have hconj : (1 : ℂ)
      = ((Fintype.card G : ℂ)⁻¹ * ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ)) * S := by
    have h' := congrArg (starRingEnd ℂ) hevalT
    rw [map_one, map_mul, hA] at h'
    have hT : starRingEnd ℂ (∑ χ ∈ Irr G, starRingEnd ℂ (χ g) * χ h) = S := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [map_mul, starRingEnd_self_apply]
    rw [hT] at h'
    exact h'
  -- final algebra
  have hkey : ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ) * S = (Fintype.card G : ℂ) := by
    have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have h3 : (Fintype.card G : ℂ)
          * ((Fintype.card G : ℂ)⁻¹ * ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ))
        = ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ) := by
      rw [← mul_assoc, mul_inv_cancel₀ hG, one_mul]
    calc ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ) * S
        = ((Fintype.card G : ℂ) * ((Fintype.card G : ℂ)⁻¹
            * ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ))) * S := by rw [h3]
      _ = (Fintype.card G : ℂ) * (((Fintype.card G : ℂ)⁻¹
            * ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ)) * S) := by rw [mul_assoc]
      _ = (Fintype.card G : ℂ) * 1 := by rw [← hconj]
      _ = (Fintype.card G : ℂ) := mul_one _
  have hcast : ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ)
      * ((Nat.card (Subgroup.centralizer ({g} : Set G)) : ℕ) : ℂ) = (Fintype.card G : ℂ) := by
    rw [← Nat.cast_mul, hcm, Nat.card_eq_fintype_card]
  have hc : ((Nat.card (ConjClasses.mk g).carrier : ℕ) : ℂ) ≠ 0 := by
    haveI : Nonempty (ConjClasses.mk g).carrier := ⟨⟨g, hmemg⟩⟩
    exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp Nat.card_pos)
  rw [← hcast] at hkey
  exact mul_left_cancel₀ hc hkey

end Work.CharCore
