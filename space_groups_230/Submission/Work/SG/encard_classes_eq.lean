import Mathlib
import Submission.Work.SG.Defs

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SG/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared definitions + generated data: Submission/Work/SG/Defs.lean (namespace Work.SG) — do NOT edit it. native_decide is NOT permitted (only kernel decide / rfl); keep certificate checks kernel-cheap. Siblings run in parallel; import them when they land.

# encard_classes_eq — counting classes from a representative system (easy, ~80–150 lines)

**Claim.** `r` an equivalence on `X`; `G : ι → X` hits every class; `r (G k) (G l) ↔ π k = π l`
with `π : ι → κ` surjective, `κ` finite. Then the set of classes `{S | ∃ a, S = {b | r a b}}` has
`encard = Nat.card κ`.

**Sketch.** Build the bijection `κ ≃ classes`: `c ↦ {b | r (G k) b}` for any `k` with `π k = c`
(well defined by `hsep` + transitivity; `Classical.choose` on `hπ`). Injective by `hsep`,
surjective by `hcover` (class of `a` = class of `G k` when `r (G k) a`). Then
`Set.encard_congr`/`Set.encard_eq_coe_toFinset_card`, or go through `Set.ncard` +
`Set.Finite`. Useful: `Set.encard_univ`, `Set.encard_coe_eq_coe_finsetCard`, `ENat.card`,
`Equiv.Set.univ`, `Nat.card_eq_card_toFinset`.

**Pitfalls.** Pure set theory; no geometry. `Nat.card κ` (not `Fintype.card`) is intentional.
-/

namespace Work.SG

/-- Counting equivalence classes through a complete, separated family of representatives: if
every element is equivalent to some `G k`, and `G k ~ G l ↔ π k = π l` with `π` onto the finite
type `κ`, then the set of classes has `Nat.card κ` elements. -/
theorem encard_classes_eq {X ι κ : Type*} [Finite κ] {r : X → X → Prop} (hr : Equivalence r)
    (G : ι → X) (π : ι → κ) (hπ : Function.Surjective π)
    (hcover : ∀ x, ∃ k, r (G k) x) (hsep : ∀ k l, r (G k) (G l) ↔ π k = π l) :
    Set.encard {S : Set X | ∃ a, S = {b | r a b}} = Nat.card κ := by
  classical
  -- a section of `π`
  let kk : κ → ι := fun c => Classical.choose (hπ c)
  have hkk : ∀ c, π (kk c) = c := fun c => Classical.choose_spec (hπ c)
  -- the canonical representative of the class labelled by `c`
  let f : κ → Set X := fun c => {b | r (G (kk c)) b}
  -- `f` is injective: equal classes have equal labels
  have hf_inj : Function.Injective f := by
    intro c d hcd
    have hmem : G (kk c) ∈ f d :=
      hcd ▸ (show G (kk c) ∈ f c from hr.refl (G (kk c)))
    have h1 : π (kk d) = π (kk c) := (hsep (kk d) (kk c)).mp hmem
    rw [hkk d, hkk c] at h1
    exact h1.symm
  -- the range of `f` is exactly the set of classes
  have hrange : Set.range f = {S : Set X | ∃ a, S = {b | r a b}} := by
    ext S
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨G (kk c), rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨k0, hk0⟩ := hcover a
      refine ⟨π k0, ?_⟩
      have hsep1 : r (G (kk (π k0))) (G k0) := by
        rw [hsep, hkk]
      show f (π k0) = {b | r a b}
      ext b
      constructor
      · intro hb
        exact hr.trans (hr.trans (hr.symm hk0) (hr.symm hsep1)) hb
      · intro hb
        exact hr.trans hsep1 (hr.trans hk0 hb)
  rw [← hrange, hf_inj.encard_range]
  exact ENat.card_eq_coe_natCard κ

end Work.SG
