import Mathlib
import Submission.Work.LT.Defs

open Finset

namespace Work.LT

/-- `hammingNorm` is invariant under reindexing along a bijection. -/
private lemma hammingNorm_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (f : β → ZMod 2) :
    hammingNorm (fun a => f (e a)) = hammingNorm f := by
  rw [show hammingNorm (fun a : α => f (e a)) = #{a | f (e a) ≠ 0} from rfl,
      show hammingNorm f = #{b | f b ≠ 0} from rfl,
      ← Fintype.card_subtype (fun a : α => f (e a) ≠ 0),
      ← Fintype.card_subtype (fun b : β => f b ≠ 0)]
  exact Fintype.card_congr (Equiv.subtypeEquiv e (fun a => Iff.rfl))

/-- `hammingNorm` on a sigma type turns into the sum of the `hammingNorm`s on the fibres. -/
lemma hammingNorm_sigma {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (g : Sigma α → ZMod 2) :
    hammingNorm g = ∑ i, hammingNorm (fun a : α i => g ⟨i, a⟩) := by
  classical
  simp only [hammingNorm]
  rw [← Finset.card_sigma]
  congr 1
  ext y
  simp [Finset.mem_sigma, Sigma.eta]

/-- The Hamming weight of a word on `G × Fin Δ × Fin Δ` is the sum, over the middle index `i`, of
the Hamming weights of the slices `(g, j) ↦ f (g, i, j)`. -/
theorem hammingNorm_triple {G : Type} [Fintype G] {Δ : ℕ} (f : G × Fin Δ × Fin Δ → ZMod 2) :
    (hammingNorm f : ℝ) =
      ∑ i : Fin Δ, (hammingNorm (fun p : G × Fin Δ => f (p.1, i, p.2)) : ℝ) := by
  have hnat : hammingNorm f =
      ∑ i : Fin Δ, hammingNorm (fun p : G × Fin Δ => f (p.1, i, p.2)) := by
    let e : (Σ _ : Fin Δ, G × Fin Δ) ≃ G × (Fin Δ × Fin Δ) :=
      { toFun := fun y => (y.2.1, y.1, y.2.2)
        invFun := fun x => ⟨x.2.1, x.1, x.2.2⟩
        left_inv := by rintro ⟨i, g, j⟩; rfl
        right_inv := by rintro ⟨g, i, j⟩; rfl }
    rw [show hammingNorm f = hammingNorm (fun y : (Σ _ : Fin Δ, G × Fin Δ) => f (e y)) from
          (hammingNorm_comp_equiv e f).symm]
    rw [hammingNorm_sigma]
    apply Finset.sum_congr rfl
    rintro i -
    rfl
  rw [hnat]
  push_cast
  rfl

end Work.LT
