import Mathlib
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec1.unique_fixed`

Peterfalvi I §1 (10)(a) for `p = 2`: if `H` is a Bender subgroup of a finite group `G`, then every
element of order `2` of `G` fixes exactly one point of `Ω = G ⧸ H`, i.e. it lies in exactly one
conjugate of `H`.

* Uniqueness is the definition: if an involution `u` fixes `QuotientGroup.mk a` and
  `QuotientGroup.mk b`, then `a⁻¹ * u * a` is an element of order `2` of `H ⊓ H^{a⁻¹ b}`; if
  `a⁻¹ * b ∉ H` this contradicts `2 ∤ |H ∩ H^{a⁻¹ b}|`.
* Existence needs no Sylow theory.  `2 ∣ |H|` gives (Cauchy) an involution `v ∈ H`; the point
  `pt H` is fixed by `v`, and by uniqueness it is the *only* fixed point of `v`.  Hence the
  2-group `⟨v⟩` acts on `Ω` with exactly one fixed point, so `|Ω|` is odd (a `p`-group acting on a
  finite set has as many fixed points as the set has elements, mod `p`).  Applied to the 2-group
  `⟨u⟩`, whose fixed points on `Ω` are the points fixed by `u`, this gives `u` a fixed point.
-/

set_option autoImplicit false

open Submission.Blueprint
open Work.DoubleTransitivity

namespace Work.DoubleTransitivity.Sec1

/-- Conjugating an element of order `2` again gives an element of order `2`. -/
private lemma orderOf_conj_inv_eq_two {G : Type} [Group G] {u a : G} (hu : orderOf u = 2) :
    orderOf (a⁻¹ * u * a) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · have h : (a⁻¹ * u * a) ^ 2 = a⁻¹ * u ^ 2 * a := by
      rw [pow_two, pow_two]; group
    rw [h, ← hu, pow_orderOf_eq_one, mul_one, inv_mul_cancel]
  · intro h
    have hu1 : u = 1 := by
      calc u = a * (a⁻¹ * u * a) * a⁻¹ := by group
        _ = a * 1 * a⁻¹ := by rw [h]
        _ = 1 := by group
    rw [hu1, orderOf_one] at hu
    exact absurd hu (by norm_num)

/-- **Peterfalvi I §1 (10)(a), uniqueness half.**  Two points of `Ω = G ⧸ H` fixed by an
element of order `2` coincide. -/
theorem eq_of_smul_eq_of_orderOf_eq_two {G : Type} [Group G] {H : Subgroup G} (hH : IsBender H)
    {u : G} (hu : orderOf u = 2) {ω₁ ω₂ : Omega H} (h1 : u • ω₁ = ω₁) (h2 : u • ω₂ = ω₂) :
    ω₁ = ω₂ := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective ω₁
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective ω₂
  rw [mk_eq_mk_iff]
  by_contra hab
  have hua : u ∈ conj a H := smul_mk_eq_mk_iff.mp h1
  have hub : u ∈ conj b H := smul_mk_eq_mk_iff.mp h2
  have hwa : a⁻¹ * u * a ∈ H := (mem_conj a u H).mp hua
  have hwb : b⁻¹ * u * b ∈ H := (mem_conj b u H).mp hub
  have hw : a⁻¹ * u * a ∈ H ⊓ conj (a⁻¹ * b) H := by
    refine ⟨hwa, ?_⟩
    have heq : (a⁻¹ * b)⁻¹ * (a⁻¹ * u * a) * (a⁻¹ * b) = b⁻¹ * u * b := by group
    exact (mem_conj (a⁻¹ * b) (a⁻¹ * u * a) H).mpr (by rw [heq]; exact hwb)
  have hdvd : 2 ∣ Nat.card ↥(H ⊓ conj (a⁻¹ * b) H) :=
    dvd_trans (by rw [Nat.card_zpowers, orderOf_conj_inv_eq_two hu])
      (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hw))
  exact hH.2 (a⁻¹ * b) hab hdvd

/-- **Peterfalvi I §1 (10)(a).**  Every element of order `2` of `G` has exactly one fixed point on
`Ω = G ⧸ H`, i.e. lies in exactly one conjugate of the Bender subgroup `H`. -/
theorem unique_fixed {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsBender H) {u : G} (hu : orderOf u = 2) :
    ∃! ω : Omega H, u • ω = ω := by
  classical
  -- An involution of `H` (Cauchy, using `2 ∣ |H|`).
  obtain ⟨v₀, hv₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 hH.1
  have hvG : orderOf (v₀ : G) = 2 := by rw [Subgroup.orderOf_coe, hv₀]
  have hvH : (v₀ : G) ∈ H := v₀.2
  -- The 2-group `⟨v₀⟩` acts on `Ω` with exactly one fixed point, so `|Ω|` is odd.
  have hOdd : Odd (Nat.card (Omega H)) := by
    have hP : IsPGroup 2 ↥(Subgroup.zpowers (v₀ : G)) := by
      refine IsPGroup.of_card_dvd_pow (n := 1) ?_
      rw [Nat.card_zpowers, hvG]; norm_num
    have hmod := hP.card_modEq_card_fixedPoints (p := 2) (Omega H)
    have hone : Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers (v₀ : G)) (Omega H)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      constructor
      · refine ⟨fun x y => Subtype.ext ?_⟩
        exact eq_of_smul_eq_of_orderOf_eq_two hH hvG
          (MulAction.mem_fixedPoints.mp x.2 ⟨(v₀ : G), Subgroup.mem_zpowers _⟩)
          (MulAction.mem_fixedPoints.mp y.2 ⟨(v₀ : G), Subgroup.mem_zpowers _⟩)
      · refine ⟨pt H, ?_⟩
        rw [MulAction.mem_fixedPoints]
        intro g
        have hgH : (g : G) ∈ H := Subgroup.zpowers_le.mpr hvH g.2
        rw [show g • pt H = (g : G) • pt H from rfl, smul_pt]
        exact mk_one_eq_iff.mpr hgH
    rw [hone] at hmod
    rw [Nat.odd_iff, hmod]
  -- Hence the 2-group `⟨u⟩` has a fixed point on `Ω`.
  have hPu : IsPGroup 2 ↥(Subgroup.zpowers u) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, hu]; norm_num
  obtain ⟨ω, hω⟩ := hPu.nonempty_fixed_point_of_prime_not_dvd_card (p := 2) (Omega H) (by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hOdd)
  have hfix : u • ω = ω := MulAction.mem_fixedPoints.mp hω ⟨u, Subgroup.mem_zpowers u⟩
  exact ⟨ω, hfix, fun ω' hω' => eq_of_smul_eq_of_orderOf_eq_two hH hu hω' hfix⟩

end Work.DoubleTransitivity.Sec1
