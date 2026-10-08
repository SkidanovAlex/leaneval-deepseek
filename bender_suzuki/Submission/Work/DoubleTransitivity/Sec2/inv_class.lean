import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.Alg.exists_involution_conjugating
import Submission.Work.DoubleTransitivity.Sec2.prop1a_odd

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec2.inv_class`

Peterfalvi I Ch. I §2 Proposition 1 (b): in a finite group admitting a **proper** Bender
subgroup `H`, the involutions of `G` form a single conjugacy class.

Equivalently (and this is the form used here): for any two elements `s`, `t` of `G` of order `2`
there is `g : G` with `g⁻¹ * s * g = t`.

The proof combines three facts already available in the area.

* Every involution fixes a **unique** point of `Ω = G ⧸ H` (`Sec1.unique_fixed`).
* Two involutions fixing **different** points share no common fixed point, so their product has
  odd order (`prop1a_odd`); two involutions whose product has odd order generate a dihedral
  group in which one of the reflections conjugates the first to the second
  (`Alg.exists_involution_conjugating`).  Hence such involutions are conjugate.
* If the two involutions fix the **same** point `ω`, use an intermediary: since `H ≠ ⊤` there is
  a further point `ω' ≠ ω`, and `ω'` is the unique fixed point of an involution `v` (its
  stabiliser is a conjugate of `H`, which has even order).  Then `s` is conjugate to `v` and `t`
  is conjugate to `v` (different fixed points), whence `s` is conjugate to `t`.
-/

set_option autoImplicit false

namespace Work.DoubleTransitivity.Sec2

/-- **From a common-free pair to conjugacy.**  Two involutions `s`, `t` that fix no common point
of `Ω = G ⧸ H` are conjugate: `s * t` has odd order (`prop1a_odd`), so the dihedral group
`⟨s, t⟩` contains an involution `u` with `u⁻¹ * s * u = t` (`Alg.exists_involution_conjugating`). -/
private theorem exists_conj_of_not_exists_common_fixed {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (hH : IsBender H) {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hst : ¬ ∃ ω : Omega H, s • ω = ω ∧ t • ω = ω) :
    ∃ g : G, g⁻¹ * s * g = t := by
  obtain ⟨u, -, hu, -⟩ :=
    Alg.exists_involution_conjugating hs ht (prop1a_odd hH hs ht hst)
  exact ⟨u, hu⟩

/-- If `H ≠ ⊤` then `Ω = G ⧸ H` has more than one point. -/
private theorem exists_mk_ne {G : Type} [Group G] {H : Subgroup G} (hne : H ≠ ⊤)
    (ω : Omega H) : ∃ ω' : Omega H, ω' ≠ ω := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra h
    exact hne ((Subgroup.eq_top_iff' H).mpr fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  have hne1 : (QuotientGroup.mk (1 : G) : Omega H) ≠ QuotientGroup.mk g := by
    intro hcon
    exact hg (by simpa using mk_eq_mk_iff.mp hcon)
  by_cases h : ω = QuotientGroup.mk (1 : G)
  · exact ⟨QuotientGroup.mk g, fun hcon => hne1.symm (hcon.trans h)⟩
  · exact ⟨QuotientGroup.mk (1 : G), fun hcon => h (hcon.symm)⟩

/-- Every point of `Ω = G ⧸ H` is the unique fixed point of some involution of `G`: its
stabiliser is a conjugate of `H`, and `H` has even order (`2 ∣ |H|`). -/
private theorem exists_involution_fixing {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsBender H) (ω : Omega H) :
    ∃ v : G, orderOf v = 2 ∧ v • ω = ω := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 hH.1
  refine ⟨g * (w : G) * g⁻¹, ?_, ?_⟩
  · have hwG : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe, hw]
    simpa [MulAut.conj_apply, hwG] using MulEquiv.orderOf_eq (MulAut.conj g) (w : G)
  · rw [smul_mk]
    apply mk_eq_mk_iff.mpr
    have heq : ((g * (w : G) * g⁻¹) * g)⁻¹ * g = (w : G)⁻¹ := by group
    rw [heq]
    exact H.inv_mem w.2

/-- **Peterfalvi I Ch. I §2 Proposition 1 (b).**  In a finite group admitting a proper Bender
subgroup, all involutions are conjugate. -/
theorem inv_class {G : Type} [Group G] [Finite G] {H : Subgroup G} (hH : IsBender H)
    (hne : H ≠ ⊤) {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2) :
    ∃ g : G, g⁻¹ * s * g = t := by
  classical
  obtain ⟨ωs, -, hsuniq⟩ := Sec1.unique_fixed hH hs
  obtain ⟨ωt, -, htuniq⟩ := Sec1.unique_fixed hH ht
  by_cases hsame : ωs = ωt
  · -- Same fixed point: use an involution at a different point as intermediary.
    obtain ⟨ω', hω'ne⟩ := exists_mk_ne hne ωs
    obtain ⟨v, hv2, hvfix⟩ := exists_involution_fixing hH ω'
    obtain ⟨ωv, -, hvuniq⟩ := Sec1.unique_fixed hH hv2
    have hvω' : ωv = ω' := (hvuniq ω' hvfix).symm
    -- `s` and `v` have no common fixed point.
    have hsv : ∃ g : G, g⁻¹ * s * g = v :=
      exists_conj_of_not_exists_common_fixed hH hs hv2 (by
        rintro ⟨ω, hsω, hvω⟩
        have h1 : ω = ωs := hsuniq ω hsω
        have h2 : ω = ωv := hvuniq ω hvω
        exact hω'ne (hvω'.symm.trans (h2.symm.trans h1)))
    -- `t` and `v` have no common fixed point (`ωt = ωs ≠ ω'`).
    have htv : ∃ g : G, g⁻¹ * t * g = v :=
      exists_conj_of_not_exists_common_fixed hH ht hv2 (by
        rintro ⟨ω, htω, hvω⟩
        have h1 : ω = ωt := htuniq ω htω
        have h2 : ω = ωv := hvuniq ω hvω
        exact hω'ne ((hvω'.symm.trans (h2.symm.trans h1)).trans hsame.symm))
    obtain ⟨g₁, hg₁⟩ := hsv
    obtain ⟨g₂, hg₂⟩ := htv
    refine ⟨g₁ * g₂⁻¹, ?_⟩
    have hseq : s = g₁ * (g₂⁻¹ * t * g₂) * g₁⁻¹ := by
      have h1 : s = g₁ * (g₁⁻¹ * s * g₁) * g₁⁻¹ := by group
      rw [h1, hg₁, ← hg₂]
    rw [hseq]
    group
  · -- Distinct fixed points: the involutions are directly conjugate.
    exact exists_conj_of_not_exists_common_fixed hH hs ht (by
      rintro ⟨ω, hsω, htω⟩
      exact hsame (hsuniq ω hsω ▸ htuniq ω htω))

end Work.DoubleTransitivity.Sec2
