import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

-- local instances (`Fintype`, a linear order) are introduced inside the proof below
set_option linter.style.haveILetI false in
/-- If an involution `σ` (i.e. `Function.Involutive σ`) preserves a finite set `S` of odd
cardinality, then `σ` fixes a point of `S`.  (The non-fixed points of `S` split into pairs.) -/
theorem exists_fixed_of_odd_ncard {α : Type} [Finite α] (σ : α → α)
    (hσ : Function.Involutive σ) {S : Set α} (hS : ∀ x ∈ S, σ x ∈ S) (hodd : Odd S.ncard) :
    ∃ x ∈ S, σ x = x := by
  -- Suppose there are no fixed points; then `σ` pairs up the points of `S`, so `S.ncard` is even.
  classical
  by_contra hcon
  have hcon' : ∀ x, x ∈ S → σ x ≠ x := by
    intro x hxS heq
    exact hcon ⟨x, hxS, heq⟩
  haveI : Fintype α := Fintype.ofFinite α
  -- An arbitrary linear order on the finite type `α`, used only to split `S` into two halves.
  letI : LinearOrder α := LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  set s : Finset α := S.toFinset with hs
  have hmem : ∀ x, x ∈ s ↔ x ∈ S := by intro x; rw [hs]; exact Set.mem_toFinset
  have hcard : s.card = S.ncard := by rw [hs]; exact (Set.ncard_eq_toFinset_card' S).symm
  have hmap : ∀ x ∈ s, σ x ∈ s := by intro x hx; rw [hmem] at hx ⊢; exact hS x hx
  have hne : ∀ x ∈ s, σ x ≠ x := by intro x hx h; exact hcon' x ((hmem x).mp hx) h
  -- `A` collects the points of `s` below their partner, `B` those above.
  set A := s.filter (fun x => x < σ x) with hA
  set B := s.filter (fun x => σ x < x) with hB
  -- With no fixed points, `B` is exactly the complement of `A` in `s`.
  have hBeq : B = s.filter (fun x => ¬ (x < σ x)) := by
    rw [hB]
    refine Finset.filter_congr (fun x hx => ?_)
    constructor
    · intro hlt hlt'; exact absurd hlt' (not_lt.mpr hlt.le)
    · intro hnlt
      rcases lt_trichotomy x (σ x) with hlt | heq | hgt
      · exact absurd hlt hnlt
      · exact absurd heq.symm (hne x hx)
      · exact hgt
  have hsum : s.card = A.card + B.card := by
    rw [hBeq, hA]
    exact (Finset.card_filter_add_card_filter_not (s := s) (p := fun x => x < σ x)).symm
  -- `σ` is a bijection from `A` onto `B`.
  have hAB : A.card = B.card := by
    refine Finset.card_bij (s := A) (t := B) (fun x hx => σ x) ?_ ?_ ?_
    · intro x hx
      simp only [hA, hB, Finset.mem_filter] at hx ⊢
      exact ⟨hmap x hx.1, by rw [hσ x]; exact hx.2⟩
    · intro x1 hx1 x2 hx2 heq
      exact hσ.injective heq
    · intro b hb
      simp only [hB, Finset.mem_filter] at hb
      refine ⟨σ b, ?_, by rw [hσ b]⟩
      simp only [hA, Finset.mem_filter]
      exact ⟨hmap b hb.1, by rw [hσ b]; exact hb.2⟩
  have heven : Even s.card := by
    rw [hsum, hAB]
    exact ⟨B.card, rfl⟩
  have hodd_s : Odd s.card := by rw [hcard]; exact hodd
  exact (Nat.not_even_iff_odd.mpr hodd_s) heven

end Work.ThreePoints.ThmC
