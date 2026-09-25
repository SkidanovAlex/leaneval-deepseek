import Mathlib
import Submission.Work.LT.relT_defs

namespace Work.LT

/-- `fhat` is additive, subtractive, and the `B`-sum of the difference of two functions is the
difference of the `B`-sums. -/
theorem relT_fhat_add :
    (∀ (p : ℕ) [NeZero p] {a b c : Fin 3} (z : ZMod p × ZMod p)
       (h1 h2 : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
       (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
      fhat p a b c z (h1 + h2) g = fhat p a b c z h1 g + fhat p a b c z h2 g)
  ∧ (∀ (p : ℕ) [NeZero p] {a b c : Fin 3} (z : ZMod p × ZMod p)
       (h1 h2 : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
       (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
      fhat p a b c z (h1 - h2) g = fhat p a b c z h1 g - fhat p a b c z h2 g)
  ∧ (∀ (p : ℕ) [NeZero p] {a b c : Fin 3} (B : Finset (ZMod p × ZMod p))
       (h1 h2 : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ),
      (fun g => ∑ z ∈ B, fhat p a b c z (h1 - h2) g)
        = (fun g => ∑ z ∈ B, fhat p a b c z h1 g) - (fun g => ∑ z ∈ B, fhat p a b c z h2 g)) := by
  have hsub : ∀ (p : ℕ) [NeZero p] {a b c : Fin 3} (z : ZMod p × ZMod p)
      (h1 h2 : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
      (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
      fhat p a b c z (h1 - h2) g = fhat p a b c z h1 g - fhat p a b c z h2 g := by
    intro p _ a b c z h1 h2 g
    simp [fhat, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_div]
  refine ⟨?_, hsub, ?_⟩
  · intro p _ a b c z h1 h2 g
    simp [fhat, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_div]
  · intro p _ a b c B h1 h2
    funext g
    simp only [Pi.sub_apply, hsub]
    rw [Finset.sum_sub_distrib]

end Work.LT
