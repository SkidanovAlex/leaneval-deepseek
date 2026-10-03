import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- If every value of `s : κ → ι` is attained at least twice (a "nonce" for each element),
then the image of `s` has at most half as many elements as `κ`.

Proof: `univ` is the disjoint union of the fibers of `s`, each element of `image s` has a
fiber of cardinality at least `2`, hence `Fintype.card κ = ∑_{b ∈ image s} #(fiber b) ≥ 2 #(image s)`. -/
theorem card_image_le_half_of_nonceFree {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (s : κ → ι) (hs : ∀ j : κ, ∃ k : κ, k ≠ j ∧ s k = s j) :
    2 * (Finset.univ.image s).card ≤ Fintype.card κ := by
  classical
  -- Every fiber of `s` over a point of the image has at least two elements.
  have hfiber : ∀ b ∈ (Finset.univ.image s : Finset ι),
      2 ≤ ((Finset.univ : Finset κ).filter (fun a => s a = b)).card := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a, -, ha⟩ := hb
    obtain ⟨k, hkne, hk⟩ := hs a
    have hk' : s k = b := by rw [hk, ha]
    have hsub : ({a, k} : Finset κ) ⊆ (Finset.univ : Finset κ).filter (fun x => s x = b) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl
      · exact ha
      · exact hk'
    calc (2 : ℕ) = ({a, k} : Finset κ).card := (Finset.card_pair hkne.symm).symm
      _ ≤ _ := Finset.card_le_card hsub
  -- `univ` splits as the sum of its fibers.
  have h1 : (Finset.univ : Finset κ).card
      = ∑ b ∈ (Finset.univ.image s : Finset ι),
          ((Finset.univ : Finset κ).filter (fun a => s a = b)).card :=
    Finset.card_eq_sum_card_fiberwise
      (by intro a _; exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  calc 2 * (Finset.univ.image s).card
      = ∑ b ∈ (Finset.univ.image s : Finset ι), (2 : ℕ) := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ b ∈ (Finset.univ.image s : Finset ι),
          ((Finset.univ : Finset κ).filter (fun a => s a = b)).card := Finset.sum_le_sum hfiber
    _ = (Finset.univ : Finset κ).card := h1.symm
    _ = Fintype.card κ := Finset.card_univ

end Work.BourgainPlan.IonescuWainger
