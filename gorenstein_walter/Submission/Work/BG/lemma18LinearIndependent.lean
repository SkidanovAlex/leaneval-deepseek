import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

/-- **Lemma 1.8 (Bender–Glauberman): distinct irreducible characters are linearly
independent.**

Any family `β : ι → ClassFunction B ℂ` of pairwise distinct irreducible characters is
linearly independent over `ℂ`: a finite linear relation `∑ cᵢ • βᵢ = 0` forces every
coefficient to vanish.

The proof embeds `β` into the type `IrreducibleCharacter B` of irreducible characters
(this embedding is injective exactly because `β` is and because the two families have the
same underlying class functions), and then applies the first orthogonality relation in its
linear-independence form `linearIndependent_irreducibleCharacter`. -/
theorem lemma18LinearIndependent {B : Type*} [Group B] [Finite B] [Fintype B]
    [Invertible (Nat.card B : ℂ)] {ι : Type*} [Fintype ι]
    (β : ι → OddOrder.RepresentationTheory.ClassFunction B ℂ)
    (hβ : ∀ i, OddOrder.RepresentationTheory.IsIrreducibleCharacter (β i))
    (hinj : Function.Injective β) (c : ι → ℂ)
    (h : ∑ i, c i • β i = 0) : ∀ i, c i = 0 := by
  have hli : LinearIndependent ℂ β := by
    -- Bundle each irreducible class function of the family as an element of
    -- `IrreducibleCharacter B`; the resulting map is injective because `β` is.
    have h1 := (OddOrder.RepresentationTheory.linearIndependent_irreducibleCharacter (G := B)).comp
      (fun i => (⟨β i, hβ i⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter B))
      (fun i j hij => hinj (Subtype.ext_iff.mp hij))
    -- The bundled family has the same underlying class functions as `β`.
    have heq : ((fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter B =>
        (χ : OddOrder.RepresentationTheory.ClassFunction B ℂ)) ∘
        fun i => (⟨β i, hβ i⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter B)) = β := rfl
    rwa [heq] at h1
  rw [Fintype.linearIndependent_iff] at hli
  exact hli c h

end Work.BG
