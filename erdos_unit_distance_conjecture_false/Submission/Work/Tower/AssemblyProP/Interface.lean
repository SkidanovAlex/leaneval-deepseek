import Submission.Work.Tower.AssemblyProP.Main
import Submission.Work.Tower.CyclotomicBase.Main
import Submission.Work.Tower.Shafarevich.Main

/-!
# The final assembly, with the class-field-theory input explicit

`Work.Interface.exists_tower` is the *only* statement of the project that is still unproved.  Its
mathematical content splits in two:

* `Work.Tower.CyclotomicBase.exists_cubic_unramified_extension_data` — the cyclotomic base of the
  tower (a totally real cubic field `F` of discriminant `(∏ rᵢ)²` with an everywhere unramified
  elementary abelian `3`-extension of degree `3^(ℓ-1)`), *proved*;
* Shafarevich's relation-rank estimate for the maximal `T`-split unramified `3`-extension, in the
  pro-`p` (cohomological) form delivered by `Work.Tower.Shafarevich.H2Estimate`, *not proved*.

The theorem below is the complete reduction: from `∃ C₀, H2Estimate C₀` to the statement of
`Work.Interface.exists_tower`.  Nothing else is missing.
-/

open NumberField
open scoped Classical nonZeroDivisors IsMulCommutative

namespace Work
namespace Tower
namespace AssemblyProP

/-- **The final reduction.**  Shafarevich's estimate in the form `∃ C₀, H2Estimate C₀`, together
with the cyclotomic base (which is proved) and the Golod--Šafarevič endgame (which is proved),
gives the statement of `Work.Interface.exists_tower`. -/
theorem exists_tower_of_H2Estimate (h : ∃ C₀ : ℕ, Work.Tower.Shafarevich.H2Estimate C₀) :
    ∀ (H : ℝ), 0 < H →
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧
      Function.Injective q ∧ (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) := by
  obtain ⟨C₀, hC₀⟩ := h
  obtain ⟨C₁, hC₁⟩ := Work.Tower.shafarevich_relation_bound_proP_of_H2_estimate C₀ hC₀
  refine exists_tower_intermediateField_pos ?_ ⟨C₁, hC₁⟩
  intro ℓ hℓ r hr hr3 hrinj
  obtain ⟨M, hMF, hMN, hMA, hMG, F, h1, h2, h3, h4, _h5, h6, h7, h8, h9⟩ :=
    Work.Tower.exists_cubic_unramified_extension_data ℓ hℓ r hr hr3 hrinj
  exact ⟨M, hMF, hMN, hMA, hMG, F, h1, h2, h3, h6, h4, h7, h8, h9⟩

end AssemblyProP
end Tower
end Work
