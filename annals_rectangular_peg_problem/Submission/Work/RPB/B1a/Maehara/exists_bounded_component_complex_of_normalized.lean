import Mathlib
import Submission.Work.RPB.B1a.Maehara.Defs
import Submission.Work.RPB1a.Caratheodory.Brouwer.normalized_reduction_bounded_component

namespace Work.RPB.B1a.Maehara

/-- **From the normalised case to the general case.**

Assume (hypothesis `h`) that every *normalised* continuous injective curve `γ : Circle → ℂ` — one
whose range lies in the rectangle `RectC = [-1,1] × [-2,2]`, meets its boundary `BdC` only in the
two points `-1` and `1`, and contains those two points — has a bounded connected component in the
complement of its range.  Then the same holds for an arbitrary continuous injective curve.

This is the reduction proved in
`Work.RPB1a.Caratheodory.Brouwer.normalized_reduction_bounded_component`: choose two points `p, q`
of `range γ` at maximum distance (compactness of `Circle`), so that `D = ‖q - p‖ > 0`, and push the
plane through the similarity `T z = 2 (z - p)/(q - p) - 1`.  Then `T p = -1`, `T q = 1`, the
maximality of `p, q` gives `‖T z + 1‖ ≤ 2` and `‖T z - 1‖ ≤ 2` for `z ∈ range γ`, and the "lens"
computation shows that `T ∘ γ` is normalised in the above sense.  Applying `h` to `T ∘ γ` and
pulling the bounded complementary component back along `T⁻¹` (a similarity, hence bi-Lipschitz and
boundedness preserving) gives the claim. -/
theorem exists_bounded_component_complex_of_normalized
    (h : ∀ (γ : Circle → ℂ), Continuous γ → Function.Injective γ →
        (-1 : ℂ) ∈ Set.range γ → (1 : ℂ) ∈ Set.range γ →
        Set.range γ ⊆ RectC → Set.range γ ∩ BdC = {(-1 : ℂ), (1 : ℂ)} →
        ∃ x : ℂ, x ∉ Set.range γ ∧
          Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x))
    (γ : Circle → ℂ) (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ x : ℂ, x ∉ Set.range γ ∧ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) x) := by
  refine _root_.Work.RPB1a.Caratheodory.Brouwer.normalized_reduction_bounded_component
    ?_ γ hγ hinj
  intro γ' hγ' hinj' hrect hbd hm1 h1
  -- Rewrite the pointwise normalisation hypotheses in the form used by `h`.
  refine h γ' hγ' hinj' hm1 h1 (fun z hz => mem_RectC.mpr (hrect z hz)) ?_
  refine Set.Subset.antisymm ?_ ?_
  · -- `range γ' ∩ BdC ⊆ {-1, 1}`
    rintro z ⟨hz, hzBd⟩
    rcases hbd z hz (mem_BdC.mp hzBd) with hz' | hz' <;> simp [hz']
  · -- `{-1, 1} ⊆ range γ' ∩ BdC`
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨hm1, by simp [mem_BdC]⟩
    · exact ⟨h1, by simp [mem_BdC]⟩

end Work.RPB.B1a.Maehara
