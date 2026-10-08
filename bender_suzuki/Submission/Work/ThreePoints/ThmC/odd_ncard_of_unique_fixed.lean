import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThreePoints.ThmC

/-- A fixed-point-free involution `σ` on a finite set `T` splits `T` into two-element orbits
`{x, σ x}`, hence `T` has even cardinality.

The proof picks a canonical representative from each orbit as the `<`-smaller element under an
arbitrary linear order on the finite type; the involution then gives a bijection between the
chosen representatives and the remaining elements. -/
theorem even_ncard_of_fpf_involutive {α : Type} [Finite α] (σ : α → α)
    (hσ : Function.Involutive σ) {T : Set α}
    (hmaps : ∀ x ∈ T, σ x ∈ T) (hfix : ∀ x ∈ T, σ x ≠ x) :
    Even T.ncard := by
  letI : Fintype α := Fintype.ofFinite α
  let e := Fintype.equivFin α
  letI : LinearOrder α := LinearOrder.lift' (fun x => (e x : ℕ))
      (fun a b h => e.injective (Fin.ext h))
  -- `U` is the set of chosen representatives: the `<`-smaller element of each orbit.
  let U : Set α := {x ∈ T | σ x < x}
  -- `σ` maps `U` exactly onto the complementary part of `T`.
  have himg : σ '' U = {x ∈ T | ¬ σ x < x} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hmaps x hx.1, by rw [hσ x]; exact not_lt_of_gt hx.2⟩
    · rintro ⟨hyT, hy⟩
      have hlt : y < σ y := by
        rcases lt_or_gt_of_ne (hfix y hyT) with h | h
        · exact absurd h hy
        · exact h
      exact ⟨σ y, ⟨hmaps y hyT, by rw [hσ y]; exact hlt⟩, hσ y⟩
  have hdisj : Disjoint U (σ '' U) := by
    rw [Set.disjoint_left]
    intro x hxU hximg
    obtain ⟨y, hyU, hyx⟩ := hximg
    have h1 : σ x < x := hxU.2
    have h2 : σ y < y := hyU.2
    have hxy : σ x = y := by rw [← hyx, hσ y]
    rw [hxy] at h1
    rw [← hyx] at h1
    exact absurd h1 (not_lt_of_gt h2)
  have hcover : T = U ∪ σ '' U := by
    apply Set.Subset.antisymm
    · intro x hxT
      by_cases hlt : σ x < x
      · exact Or.inl ⟨hxT, hlt⟩
      · exact Or.inr (by rw [himg]; exact ⟨hxT, hlt⟩)
    · rintro x (hx | hx)
      · exact hx.1
      · rw [himg] at hx; exact hx.1
  have hcard : T.ncard = U.ncard + (σ '' U).ncard := by
    rw [hcover]
    exact Set.ncard_union_eq hdisj
  have himgcard : (σ '' U).ncard = U.ncard := Set.ncard_image_of_injective U hσ.injective
  rw [hcard, himgcard]
  exact ⟨U.ncard, rfl⟩

/-- If an involution `σ` (i.e. `Function.Involutive σ`) preserves a finite set `S` and has exactly
one fixed point in `S`, then `S` has odd cardinality.  (The non-fixed points split into pairs.) -/
theorem odd_ncard_of_unique_fixed {α : Type} [Finite α] (σ : α → α)
    (hσ : Function.Involutive σ) {S : Set α} (hS : ∀ x ∈ S, σ x ∈ S)
    (huniq : ∀ x y, x ∈ S → σ x = x → y ∈ S → σ y = y → x = y)
    (hex : ∃ x ∈ S, σ x = x) : Odd S.ncard := by
  -- Extract the unique fixed point `a` of `σ` in `S`.
  obtain ⟨a, haS, ha⟩ := hex
  -- Remove it: `T` carries a fixed-point-free involution and hence is even.
  let T : Set α := S \ {a}
  have hTσ : ∀ x ∈ T, σ x ∈ T := by
    rintro x ⟨hxS, hxa⟩
    refine ⟨hS x hxS, ?_⟩
    intro hcon
    refine hxa ?_
    rw [Set.mem_singleton_iff] at hcon ⊢
    rw [← hσ x, hcon, ha]
  have hTfix : ∀ x ∈ T, σ x ≠ x := by
    rintro x ⟨hxS, hxa⟩ hfix
    exact hxa (huniq x a hxS hfix haS ha)
  have hEven : Even T.ncard := even_ncard_of_fpf_involutive σ hσ hTσ hTfix
  -- Reassemble `S = insert a T` and apply the parity lemma for inserting one element.
  have hS_eq : S = insert a T := by
    ext x
    constructor
    · intro hx
      by_cases h : x = a
      · rw [h]; exact Set.mem_insert a T
      · exact Set.mem_insert_of_mem a ⟨hx, h⟩
    · intro hx
      rcases Set.mem_insert_iff.mp hx with h | h
      · rw [h]; exact haS
      · exact h.1
  have haT : a ∉ T := by simp [T]
  rw [hS_eq, Set.odd_card_insert_iff haT]
  exact hEven

end Work.ThreePoints.ThmC
