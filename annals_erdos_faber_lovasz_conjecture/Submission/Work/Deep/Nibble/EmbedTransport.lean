import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.EFL.Embed

/-!
# Transporting a hypergraph along a bijection of vertex types
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

/-- Transport a hypergraph along a bijection of vertex types. -/
def transportH {α β : Type*} (e : α ≃ β) (𝓗 : Set (Set α)) : Set (Set β) :=
  {f | ∃ g ∈ 𝓗, f = e '' g}

theorem mem_transportH {α β : Type*} {e : α ≃ β} {𝓗 : Set (Set α)} {f : Set β} :
    f ∈ transportH e 𝓗 ↔ ∃ g ∈ 𝓗, f = e '' g := Iff.rfl

theorem transportH_ncard {α β : Type*} {e : α ≃ β} {𝓗 : Set (Set α)} {r : ℕ}
    (h : ∀ g ∈ 𝓗, g.ncard = r) : ∀ f ∈ transportH e 𝓗, f.ncard = r := by
  rintro f ⟨g, hg, rfl⟩
  rw [Set.ncard_image_of_injective _ e.injective, h g hg]

theorem transportH_linear {α β : Type*} {e : α ≃ β} {𝓗 : Set (Set α)}
    (h : ∀ ⦃g⦄, g ∈ 𝓗 → ∀ ⦃g'⦄, g' ∈ 𝓗 → g ≠ g' → (g ∩ g').Subsingleton) :
    ∀ ⦃f⦄, f ∈ transportH e 𝓗 → ∀ ⦃f'⦄, f' ∈ transportH e 𝓗 → f ≠ f' →
      (f ∩ f').Subsingleton := by
  rintro f ⟨g, hg, rfl⟩ f' ⟨g', hg', rfl⟩ hne
  rw [← Set.image_inter e.injective]
  exact (h hg hg' (fun hh => hne (by rw [hh]))).image _

theorem transportH_deg {α β : Type*} {e : α ≃ β} {𝓗 : Set (Set α)} (x : α) :
    ({f ∈ transportH e 𝓗 | e x ∈ f} : Set (Set β)).ncard
      = ({g ∈ 𝓗 | x ∈ g} : Set (Set α)).ncard := by
  have hset : ({f ∈ transportH e 𝓗 | e x ∈ f} : Set (Set β))
      = (fun g : Set α => e '' g) '' {g ∈ 𝓗 | x ∈ g} := by
    ext f; constructor
    · rintro ⟨⟨g, hg, rfl⟩, hx⟩
      refine ⟨g, ⟨hg, ?_⟩, rfl⟩
      obtain ⟨y, hy, hy'⟩ := hx
      rwa [e.injective hy'] at hy
    · rintro ⟨g, ⟨hg, hx⟩, rfl⟩
      exact ⟨⟨g, hg, rfl⟩, ⟨x, hx, rfl⟩⟩
  rw [hset, Set.ncard_image_of_injective _ (Set.image_injective.mpr e.injective)]

private theorem symm_image_image {α β : Type*} (e : α ≃ β) (g : Set α) :
    e.symm '' (e '' g) = g := by
  ext x; constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

private theorem image_symm_image {α β : Type*} (e : α ≃ β) (f : Set β) :
    e '' (e.symm '' f) = f := by
  ext y; constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    simpa using hw
  · intro hy
    exact ⟨e.symm y, ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

private theorem image_inter_nonempty {α β : Type*} (e : α ≃ β) (g A : Set α) :
    (g ∩ A).Nonempty → (e '' g ∩ e '' A).Nonempty := by
  intro h
  simpa [Set.image_inter e.injective] using h.image e

private theorem symm_image_inter_nonempty {α β : Type*} (e : α ≃ β) (f : Set β) (A : Set α) :
    (f ∩ e '' A).Nonempty → (e.symm '' f ∩ A).Nonempty := by
  rintro ⟨y, hy, hyA⟩
  obtain ⟨x, hxA, hxy⟩ := hyA
  exact ⟨x, ⟨⟨y, hy, by rw [← hxy, e.symm_apply_apply]⟩, hxA⟩⟩

private theorem transportH_symm_image_mem {α β : Type*} (e : α ≃ β) {𝓗 : Set (Set α)}
    {f : Set β} (hf : f ∈ transportH e 𝓗) : e.symm '' f ∈ 𝓗 := by
  obtain ⟨g, hg, rfl⟩ := hf
  rwa [symm_image_image e g]

/-- Transport an identification of edges along a bijection of vertex types. -/
def transportH_ident {α β : Type*} (e : α ≃ β) (𝓗 : Set (Set α)) (A : Set α) :
    {g : Set α // g ∈ 𝓗 ∧ (g ∩ A).Nonempty} ≃
      {f : Set β // f ∈ transportH e 𝓗 ∧ (f ∩ e '' A).Nonempty} where
  toFun g := ⟨e '' g.1, ⟨g.1, g.2.1, rfl⟩, image_inter_nonempty e g.1 A g.2.2⟩
  invFun f := ⟨e.symm '' f.1, transportH_symm_image_mem e f.2.1,
    symm_image_inter_nonempty e f.1 A f.2.2⟩
  left_inv g := Subtype.ext (symm_image_image e g.1)
  right_inv f := Subtype.ext (image_symm_image e f.1)

/-- Subtypes defined by two propositionally equal sets are equivalent. -/
def subtype_congr_meet {Z : Type*} {𝓖' : Set (Set Z)} {A B : Set Z} (h : A = B) :
    {f : Set Z // f ∈ 𝓖' ∧ (f ∩ A).Nonempty} ≃
      {f : Set Z // f ∈ 𝓖' ∧ (f ∩ B).Nonempty} where
  toFun f := ⟨f.1, f.2.1, by rw [← h]; exact f.2.2⟩
  invFun f := ⟨f.1, f.2.1, by rw [h]; exact f.2.2⟩
  left_inv f := rfl
  right_inv f := rfl

end

end Work.Deep.Nibble
