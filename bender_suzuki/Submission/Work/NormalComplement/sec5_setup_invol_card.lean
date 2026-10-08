import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.involutions_card_eq_of_surjective_centralOddKer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- For a subgroup `S` of `G`, the set of involutions of `G` lying in `S` has the same
cardinality as the set of involutions of `S` itself: coercion along `S.subtype` identifies the
order of an element with the order of its image. -/
lemma ncard_orderOf_eq_two_eq_natCard (G : Type*) [Group G] (S : Subgroup G) :
    {t : G | t ∈ S ∧ orderOf t = 2}.ncard = Nat.card {u : ↥S // orderOf u = 2} := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr ?_
  refine
  { toFun := fun t => ⟨⟨t.1, t.2.1⟩, ?_⟩
    invFun := fun u => ⟨u.1.1, u.1.2, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have h := orderOf_injective S.subtype S.subtype_injective (⟨t.1, t.2.1⟩ : ↥S)
    rw [← h]
    exact t.2.2
  · have h : orderOf ((u.1 : ↥S) : G) = orderOf (u.1 : ↥S) :=
      orderOf_injective S.subtype S.subtype_injective u.1
    rw [h]
    exact u.2
  · intro t; exact Subtype.ext rfl
  · intro u; exact Subtype.ext (Subtype.ext rfl)

/-- A homomorphism with **central** kernel `N` of **odd** order maps the involutions of a
subgroup `L ⊇ N` bijectively onto the involutions of the image: merging is impossible because an
element of `N` has odd order, and every involution of `L.map φ` lifts to an involution of `L` by
extracting a square root in the odd-order group `N`.

This is the count transport used in `Work.NormalComplement.sec5_setup`: with `X = ↥F₀`, `Z = Y`,
`φ` the quotient map of kernel `Z(F₀)`, `L = (F₀ ⊓ H).subgroupOf F₀`, it gives
`|Inv (L.map φ)| = |Inv L| = 2^p - 1`.

Suggested proof: `Work.Models.Port.Commons.GroupTheory.involutions_card_eq_of_surjective_centralOddKer`
applied to the restriction `ψ : ↥L →* ↥(L.map φ)` (surjective by `Subgroup.mem_map`; its kernel is
`N.subgroupOf L`, central and of odd order), together with the translation
`{x : G | x ∈ S ∧ orderOf x = 2}.ncard = Nat.card {t : ↥S // orderOf t = 2}` (via
`Nat.card_coe_set_eq` and `orderOf_injective S.subtype S.subtype_injective`). -/
theorem sec5_setup_invol_card {X Z : Type} [Group X] [Finite X] [Group Z]
    (φ : X →* Z) {N : Subgroup X} (hker : φ.ker = N) (hcenter : N ≤ Subgroup.center X)
    (hodd : Odd (Nat.card N)) {L : Subgroup X} (hNL : N ≤ L) :
    {z : Z | z ∈ (L.map φ : Subgroup Z) ∧ orderOf z = 2}.ncard =
      {x : X | x ∈ L ∧ orderOf x = 2}.ncard := by
  classical
  -- The restricted map `↥L →* ↥(L.map φ)`.
  let f : ↥L →* Z := φ.comp L.subtype
  have hmap : ∀ x : ↥L, f x ∈ (L.map φ : Subgroup Z) := by
    intro x
    rw [Subgroup.mem_map]
    exact ⟨(x : X), x.2, rfl⟩
  let ψ : ↥L →* ↥(L.map φ : Subgroup Z) := f.codRestrict _ hmap
  have hsurj : Function.Surjective ψ := by
    intro s
    rcases Subgroup.mem_map.mp s.2 with ⟨x, hxL, hxφ⟩
    refine ⟨⟨x, hxL⟩, ?_⟩
    apply Subtype.ext
    simpa [ψ, f] using hxφ
  have hkerψ : MonoidHom.ker ψ = N.subgroupOf L := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have hφ : φ (u : X) = 1 := by
        have := congrArg (Subtype.val) h
        simpa [ψ, f] using this
      exact hker ▸ MonoidHom.mem_ker.mpr hφ
    · intro h
      have hφ1 : φ (u : X) = 1 := MonoidHom.mem_ker.mp (hker ▸ h)
      apply Subtype.ext
      simpa [ψ, f] using hφ1
  have hcenterψ : MonoidHom.ker ψ ≤ Subgroup.center ↥L := by
    rw [hkerψ]
    intro u hu
    rw [Subgroup.mem_center_iff]
    intro v
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcenter (Subgroup.mem_subgroupOf.mp hu)) (v : X)
  have hoddψ : Odd (Nat.card (MonoidHom.ker ψ)) := by
    rw [hkerψ]
    have he : Nat.card ↥(N.subgroupOf L) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv
    rw [he]
    exact hodd
  have hcard :=
    Commons.GroupTheory.involutions_card_eq_of_surjective_centralOddKer ψ hsurj hcenterψ hoddψ
  rw [ncard_orderOf_eq_two_eq_natCard Z (L.map φ),
    ncard_orderOf_eq_two_eq_natCard X L]
  exact hcard.symm

end Work.NormalComplement
