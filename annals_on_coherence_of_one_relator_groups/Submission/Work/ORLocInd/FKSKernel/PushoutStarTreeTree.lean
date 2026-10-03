/-
# The star graph of a pushout is a tree

This file proves `Work.ORBassSerre.IsTree (Vtx φ)` for the star graph `Vtx φ` of
`Submission.Work.ORLocInd.FKSKernel.PushoutStarTree`, assuming that all the edge maps `φ i` are
injective.

A path starting at a centre alternates between centres and leaves.  Following such a path records
a sequence of "steps" from one centre to the next, each step carrying an element of the image of
some `G i`.  Reducedness forces the indices of consecutive steps to differ and each step to be
non-trivial modulo the base subgroup, so that the sequence is a *reduced* word in `CoprodI G` (in
the sense of `Monoid.PushoutI.Reduced`) whose product lies in the base subgroup; Mathlib's
`Monoid.PushoutI.Reduced.eq_empty_of_mem_range` then forces the word to be empty, so the path has
length zero.
-/
import Mathlib
import Submission.Work.ORLocInd.FKSKernel.PushoutStarTree

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.FKSKernel

open Quiver
open Classical

variable {ι : Type u} {H : Type u} {G : ι → Type u} [Group H] [∀ i, Group (G i)]

/-! ## Representatives and preimages -/

/-- A chosen representative of a coset of the base subgroup. -/
noncomputable def repC (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) : Psh φ :=
  Classical.choose (Quotient.exists_rep γ)

theorem repC_mk (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    Quotient.mk'' (repC φ γ) = γ :=
  Classical.choose_spec (Quotient.exists_rep γ)

/-- A preimage of an element of the image of the `i`-th group. -/
noncomputable def prei (φ : ∀ i, H →* G i) (i : ι) (u : Psh φ) (hu : u ∈ ofSub φ i) : G i :=
  Classical.choose hu

theorem of_prei (φ : ∀ i, H →* G i) (i : ι) (u : Psh φ) (hu : u ∈ ofSub φ i) :
    Monoid.PushoutI.of (φ := φ) i (prei φ i u hu) = u :=
  Classical.choose_spec hu

/-- The transport of a membership in the base subgroup to a membership in the range of `φ i`. -/
theorem mem_range_of_mem_baseSub {φ : ∀ i, H →* G i} (hφ : ∀ i, Function.Injective (φ i))
    {i : ι} {x : G i} (h : Monoid.PushoutI.of (φ := φ) i x ∈ baseSub φ) : x ∈ (φ i).range := by
  obtain ⟨y, hy⟩ := h
  have hy' : Monoid.PushoutI.of (φ := φ) i (φ i y) = Monoid.PushoutI.of (φ := φ) i x := by
    rw [Monoid.PushoutI.of_apply_eq_base (φ := φ) i y]
    exact hy
  exact ⟨y, Monoid.PushoutI.of_injective (φ := φ) hφ i hy'⟩

/-! ## The state of a path started at a centre -/

/-- The coset (of the base subgroup) of the last centre visited by a path started at `ctr γ`.
For a path ending at a centre this is the coset of the endpoint; for a path ending at a leaf this
is the coset of the centre from which that leaf is entered. -/
noncomputable def cstateC (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    {y : Vtx φ} → Quiver.Path (ctr φ γ) y → Psh φ ⧸ baseSub φ
  | _, .nil => γ
  | _, .cons p e => if p.length % 2 = 1 then e.lbl else cstateC φ γ p

theorem cstateC_nil (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    cstateC φ γ (Quiver.Path.nil : Quiver.Path (ctr φ γ) (ctr φ γ)) = γ := rfl

theorem cstateC_cons (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) {x y : Vtx φ}
    (p : Quiver.Path (ctr φ γ) x) (e : x ⟶ y) :
    cstateC φ γ (p.cons e) = if p.length % 2 = 1 then e.lbl else cstateC φ γ p := rfl

/-- An arrow changes the type of the endpoint. -/
theorem ctr_excl {φ : ∀ i, H →* G i} {x y : Vtx φ} (e : x ⟶ y) :
    (∃ c, x = ctr φ c) ↔ ¬ (∃ c, y = ctr φ c) := by
  constructor
  · rintro ⟨c, rfl⟩ ⟨c', hc'⟩
    exact ctr_ne_lf φ c' c e.idx (hc'.symm.trans (arrow_ctr_left (φ := φ) e).2)
  · intro h
    obtain ⟨⟨j, c''⟩, he⟩ := e
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨c'', h1⟩
    · exact absurd ⟨c'', h2⟩ h

/-- A path starting at a centre ends at a centre exactly when its length is even. -/
theorem length_even_iff_ctr (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    ∀ (y : Vtx φ) (p : Quiver.Path (ctr φ γ) y), ((∃ c, y = ctr φ c) ↔ p.length % 2 = 0)
  | _, Quiver.Path.nil => by
      simp only [Quiver.Path.length_nil, Nat.zero_mod]
      exact ⟨fun _ => trivial, fun _ => ⟨γ, rfl⟩⟩
  | _, @Quiver.Path.cons _ _ _ x y p e => by
      have ih := length_even_iff_ctr φ γ x p
      have hcx := ctr_excl e
      have hmod : (p.length + 1) % 2 = 0 ↔ p.length % 2 = 1 := by omega
      rw [Quiver.Path.length_cons, hmod]
      constructor
      · intro h
        have hx : ¬ (∃ c, x = ctr φ c) := fun hx => (hcx.mp hx) h
        have h0 : p.length % 2 ≠ 0 := fun h0 => hx (ih.mpr h0)
        omega
      · intro h
        have h0 : p.length % 2 ≠ 0 := by omega
        have hx : ¬ (∃ c, x = ctr φ c) := fun hx => h0 (ih.mp hx)
        by_contra hy
        exact hx (hcx.mpr fun hy' => hy hy')

/-- The state of a path started at a centre is the coset of the last centre visited. -/
theorem cstateC_spec (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    ∀ (y : Vtx φ) (p : Quiver.Path (ctr φ γ) y),
      (∃ c, y = ctr φ c ∧ cstateC φ γ p = c) ∨ (∃ i, y = lf φ i (cstateC φ γ p))
  | _, Quiver.Path.nil => Or.inl ⟨γ, rfl, cstateC_nil φ γ⟩
  | _, @Quiver.Path.cons _ _ _ x _ p e => by
      have hpar := length_even_iff_ctr φ γ x p
      rcases cstateC_spec φ γ x p with ⟨c, hy, hst⟩ | ⟨i, hy⟩
      · -- `p` ends at a centre
        have hlen : p.length % 2 = 0 := hpar.mp ⟨c, hy⟩
        have hstate : cstateC φ γ (p.cons e) = c := by
          rw [cstateC_cons, if_neg (by omega), hst]
        rcases Arrow.endpoints e with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hbl : e.lbl = c := ctr_inj (h1.symm.trans hy)
          refine Or.inr ⟨e.idx, ?_⟩
          rw [hstate]
          exact hbl ▸ h2
        · exact absurd (hy.symm.trans h1) (ctr_ne_lf φ c e.lbl e.idx)
      · -- `p` ends at a leaf
        rcases Arrow.endpoints e with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd (h1.symm.trans hy) (ctr_ne_lf φ e.lbl (cstateC φ γ p) i)
        · have hx : ¬ (∃ c, x = ctr φ c) :=
            fun hx => hx.elim fun c hc => ctr_ne_lf φ c (cstateC φ γ p) i (hc.symm.trans hy)
          have hlen : p.length % 2 = 1 := by
            have h0 : p.length % 2 ≠ 0 := fun h0 => hx ((length_even_iff_ctr φ γ x p).mpr h0)
            omega
          have hstate : cstateC φ γ (p.cons e) = e.lbl := by
            rw [cstateC_cons, if_pos hlen]
          exact Or.inl ⟨e.lbl, h2, hstate⟩

/-! ## The letters of a path started at a centre -/

/-- The letters of a path started at a centre: for each step from a leaf to a centre, the ratio of
the chosen representatives of the two successive centres, as an element of the pushout. -/
noncomputable def clets (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    {y : Vtx φ} → Quiver.Path (ctr φ γ) y → List (ι × Psh φ)
  | _, .nil => []
  | _, .cons p e =>
      clets φ γ p ++
        (if p.length % 2 = 1 then
          [(e.idx, (repC φ (cstateC φ γ p))⁻¹ * repC φ e.lbl)] else [])

theorem clets_nil (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    clets φ γ (Quiver.Path.nil : Quiver.Path (ctr φ γ) (ctr φ γ)) = [] := rfl

theorem clets_cons (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) {x y : Vtx φ}
    (p : Quiver.Path (ctr φ γ) x) (e : x ⟶ y) :
    clets φ γ (p.cons e) = clets φ γ p ++
      (if p.length % 2 = 1 then
        [(e.idx, (repC φ (cstateC φ γ p))⁻¹ * repC φ e.lbl)] else []) := rfl

/-- The length of the list of letters is half the length of the path. -/
theorem clets_length (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    ∀ (y : Vtx φ) (p : Quiver.Path (ctr φ γ) y), (clets φ γ p).length = p.length / 2
  | _, Quiver.Path.nil => by simp [clets]
  | _, Quiver.Path.cons p e => by
      rw [clets_cons, List.length_append, clets_length φ γ _ p, Quiver.Path.length_cons]
      by_cases h : p.length % 2 = 1
      · rw [if_pos h]
        simp only [List.length_cons, List.length_nil]
        omega
      · rw [if_neg h]
        simp only [List.length_nil, Nat.add_zero]
        omega

/-- The product in the pushout of the letters of a path is the ratio of the representatives of the
initial and final centres. -/
theorem prod_clets (φ : ∀ i, H →* G i) (γ : Psh φ ⧸ baseSub φ) :
    ∀ (y : Vtx φ) (p : Quiver.Path (ctr φ γ) y),
      ((clets φ γ p).map (fun x => x.2)).prod = (repC φ γ)⁻¹ * repC φ (cstateC φ γ p)
  | _, Quiver.Path.nil => by
      simp only [clets_nil, List.map_nil, List.prod_nil, cstateC_nil]
      group
  | _, Quiver.Path.cons p e => by
      rw [clets_cons, List.map_append]
      rw [List.prod_append, prod_clets φ γ _ p]
      by_cases h : p.length % 2 = 1
      · rw [if_pos h, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          cstateC_cons, if_pos h]
        group
      · rw [if_neg h, List.map_nil, List.prod_nil, mul_one, cstateC_cons, if_neg h]

end Work.ORLocInd.FKSKernel
