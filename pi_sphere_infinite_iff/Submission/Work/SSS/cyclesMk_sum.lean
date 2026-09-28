import Mathlib
import Submission.Work.SSS.serreE1CruxDefs

set_option backward.isDefEq.respectTransparency false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- `Work.SSS`-style `cyclesMk` is linear in the element: the cycle attached to a linear combination
of cycles is the same linear combination of the cycles attached to the summands. -/
theorem cyclesMk_sum {K : ChainComplex (ModuleCat ℤ) ℕ} {i : ℕ} {ι : Type} [Fintype ι]
    (a : ι → ℤ) (x : ι → K.X i)
    (hx : ∀ j, (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) (x j) = 0)
    (h : (ModuleCat.Hom.hom (K.d i ((ComplexShape.down ℕ).next i))) (∑ j, a j • x j) = 0) :
    K.cyclesMk (∑ j, a j • x j) ((ComplexShape.down ℕ).next i) rfl h
      = ∑ j, a j • K.cyclesMk (x j) ((ComplexShape.down ℕ).next i) rfl (hx j) := by
  -- The inclusion `K.iCycles i : K.cycles i ⟶ K.X i` is a monomorphism, and `forget₂ _ Ab`
  -- turns it into an injective map; it suffices to compare the images of both sides.
  apply (Preadditive.mono_iff_injective (K.iCycles i)).1 inferInstance
  -- `map_sum`/`map_zsmul` push the additive map through the linear combination, and
  -- `i_cyclesMk` unwinds `cyclesMk`; both sides become `∑ j, a j • x j`.
  simp only [map_sum, map_zsmul, HomologicalComplex.i_cyclesMk]

end Work.SSS
