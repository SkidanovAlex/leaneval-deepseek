/-
# Peterfalvi I Ch. I §2 Prop. 1 (b): the involutions of `G` form a single conjugacy class

`H` is a strongly embedded subgroup of a finite group `G` and `Ω = G ⧸ H` is the set of its
conjugates (`Work.ThreePoints.Omega`).  The result proved here is the second assertion of
Peterfalvi I Ch. I §2 Proposition 1 (p. 151):

> `Inv(G)` is a conjugacy class of `G`,

i.e. any two involutions of `G` are conjugate.  The proof follows the source:

* an involution `s` fixes a **unique** point `ω_s` of `Ω` (this is the uniqueness half of
  `ncard_fixedPts_zpowers`); if two involutions `s`, `t` have `ω_s ≠ ω_t`, then `s * t` has odd
  order (`Work.ThreePoints.odd_orderOf_mul`), so `s` and `t` are conjugate by an involution of
  the dihedral group `⟨s, t⟩` (`Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul`);
* if `ω_s = ω_t`, the subgroup `H` is proper, so some conjugate of `H` is different from the
  common stabiliser; that conjugate has even order, hence contains an involution `v`, and
  `ω_v ≠ ω_s`.  Applying the first case to `(s, v)` and to `(t, v)` and transitivity of
  conjugacy gives the result.
-/
import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

/-! ## 1. The unique fixed point of an involution -/

/-- **Peterfalvi I Ch. I §2** (uniqueness clause of `ncard_fixedPts_zpowers`): an involution of
`G` fixes a unique point of `Ω = G ⧸ H`. -/
theorem existsUnique_fixedPts_of_orderOf_eq_two {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h : IsStronglyEmbedded H) {x : G} (hx : orderOf x = 2) :
    ∃! ω : G ⧸ H, x • ω = ω := by
  obtain ⟨ω, hω⟩ := Set.ncard_eq_one.mp (ncard_fixedPts_zpowers h hx)
  refine ⟨ω, ?_, ?_⟩
  · have hmem : ω ∈ fixedPts H (Subgroup.zpowers x) := by
      rw [hω]; exact Set.mem_singleton ω
    exact (mem_fixedPts.mp hmem) x (Subgroup.mem_zpowers x)
  · intro ω' hω'
    have hmem : ω' ∈ fixedPts H (Subgroup.zpowers x) := by
      rw [mem_fixedPts_iff_le_stabilizer, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact hω'
    rw [hω] at hmem
    exact Set.mem_singleton_iff.mp hmem

/-! ## 2. Involutions with distinct fixed points are conjugate -/

/-- **Peterfalvi I Ch. I §2 Prop. 1 (a).**  Two involutions with no common fixed point in
`Ω = G ⧸ H` are conjugate (by an involution of the dihedral group they generate). -/
theorem isConj_of_no_common_fixedPts {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h : IsStronglyEmbedded H) {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hsep : ∀ ω : G ⧸ H, s • ω = ω → t • ω ≠ ω) : IsConj s t := by
  obtain ⟨u, -, hu, -⟩ :=
    exists_involution_conj_of_odd_orderOf_mul hs ht (odd_orderOf_mul h hs ht hsep)
  exact isConj_iff.mpr ⟨u, hu⟩

/-! ## 3. Every point of `Ω` is fixed by an involution -/

/-- Any point of `Ω = G ⧸ H` is fixed by an involution of `G`: its stabiliser is a conjugate of
the strongly embedded subgroup `H`, hence has even order, and an element of order `2` of `H`
conjugates to one of that stabiliser. -/
theorem exists_involution_smul_eq_self {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h : IsStronglyEmbedded H) (ω : G ⧸ H) : ∃ v : G, orderOf v = 2 ∧ v • ω = ω := by
  classical
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  haveI : Fintype ↥H := Fintype.ofFinite ↥H
  have hdvd : 2 ∣ Fintype.card ↥H := by
    have h2 := IsStronglyEmbedded.two_dvd_card h
    rwa [Nat.card_eq_fintype_card] at h2
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card (G := ↥H) 2 hdvd
  refine ⟨g * (w : G) * g⁻¹, ?_, ?_⟩
  · have hwg : orderOf (w : G) = 2 := by
      have h1 := orderOf_injective H.subtype Subtype.coe_injective w
      rwa [hw] at h1
    have h1 := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (w : G)
    rw [hwg] at h1
    simpa [mulAut_conj_apply] using h1
  · rw [smul_mk, QuotientGroup.eq]
    have he : (g * (w : G) * g⁻¹ * g)⁻¹ * g = (w : G)⁻¹ := by group
    rw [he]
    exact H.inv_mem w.2

/-! ## 4. A point different from a prescribed one -/

/-- If `H ≠ ⊤` there is a point of `Ω = G ⧸ H` different from any prescribed one. -/
theorem exists_ne_mk_of_ne_top {G : Type} [Group G] {H : Subgroup G} (hH : H ≠ ⊤)
    (ω : G ⧸ H) : ∃ ω' : G ⧸ H, ω' ≠ ω := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
    by_contra h
    refine hH ((Subgroup.eq_top_iff' H).mpr fun x => ?_)
    by_contra hx
    exact h ⟨x, hx⟩
  have hne1 : (QuotientGroup.mk (1 : G)) ≠ (g : G ⧸ H) := by
    intro hcon
    exact hg (by simpa using QuotientGroup.eq.mp hcon)
  by_cases h : ω = (QuotientGroup.mk (1 : G))
  · exact ⟨(g : G ⧸ H), fun hcon => hne1.symm (hcon.trans h)⟩
  · exact ⟨(QuotientGroup.mk (1 : G)), fun hcon => h (hcon.symm)⟩

/-! ## 5. The main result -/

/-- **Peterfalvi I Ch. I §2 Proposition 1 (b).**  In a finite group with a strongly embedded
subgroup, all involutions are conjugate. -/
theorem involutions_conj_of_stronglyEmbedded {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {s t : G}
    (hs : orderOf s = 2) (ht : orderOf t = 2) : IsConj s t := by
  classical
  obtain ⟨ωs, -, hsuniq⟩ := existsUnique_fixedPts_of_orderOf_eq_two hH hs
  obtain ⟨ωt, -, htuniq⟩ := existsUnique_fixedPts_of_orderOf_eq_two hH ht
  by_cases hne : ωs = ωt
  · -- the two involutions have the same fixed point: use a third one as an intermediary
    obtain ⟨ω', hω'ne⟩ := exists_ne_mk_of_ne_top (IsStronglyEmbedded.ne_top hH) ωs
    obtain ⟨v, hv2, hvfix⟩ := exists_involution_smul_eq_self hH ω'
    have hvuniq : ∀ ω : G ⧸ H, v • ω = ω → ω = ω' := by
      obtain ⟨a, -, huniq⟩ := existsUnique_fixedPts_of_orderOf_eq_two hH hv2
      intro ω hω
      rw [huniq ω hω, huniq ω' hvfix]
    have hsv : IsConj s v := isConj_of_no_common_fixedPts hH hs hv2 (fun ω hω => by
      rw [hsuniq ω hω]
      exact fun hcon => hω'ne (hvuniq ωs hcon).symm)
    have htv : IsConj t v := isConj_of_no_common_fixedPts hH ht hv2 (fun ω hω => by
      rw [htuniq ω hω]
      exact fun hcon => hω'ne ((hne.trans (hvuniq ωt hcon)).symm))
    exact hsv.trans htv.symm
  · -- distinct fixed points: the two involutions are directly conjugate
    exact isConj_of_no_common_fixedPts hH hs ht (fun ω hω => by
      rw [hsuniq ω hω]
      exact fun hcon => hne (htuniq ωs hcon))

end Work.ThreePoints
