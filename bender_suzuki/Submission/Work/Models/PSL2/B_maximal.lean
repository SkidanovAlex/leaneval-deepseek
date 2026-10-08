import Mathlib
import Submission.Work.Models.PSL2.Defs
import Submission.Work.Models.PSL2.bruhat
import Submission.Work.Models.PSL2.w_facts

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.PSL2

/-- A subgroup containing `B` and `w` is everything: by the Bruhat decomposition every element
of `SL(2,F)` is either upper triangular or of the form `b₁ w b₂` with `b₁, b₂` upper
triangular.  (The derivation of this from `bruhat` is the substance of `B_maximal`.) -/
theorem eq_top_of_le_of_mem_w {F : Type*} [Field F] [CharP F 2] (M : Subgroup (Work.Models.SL2 F))
    (hM : Work.Models.PSL2.B (F := F) ≤ M) (hw : w (F := F) ∈ M) : M = ⊤ := by
  refine eq_top_iff.mpr fun A _ => ?_
  rcases bruhat (F := F) A with hA | ⟨b₁, hb₁, b₂, hb₂, hA⟩
  · exact hM hA
  · rw [hA]
    exact M.mul_mem (M.mul_mem (hM hb₁) hw) (hM hb₂)

/-- **`B` is a maximal subgroup of `SL(2,F)`** for `F` a field of characteristic `2`: any
subgroup strictly containing the standard Borel `B` is everything.

Indeed, if `B ≤ M ≠ B` pick `g ∈ M \ B`.  The Bruhat decomposition writes `g = b₁ w b₂` with
`b₁, b₂ ∈ B` (the other alternative `g ∈ B` is excluded), whence `w = b₁⁻¹ g b₂⁻¹ ∈ M`.  But
another application of Bruhat shows that `B` together with `w` generates `SL(2,F)`
(`eq_top_of_le_of_mem_w`), so `M = ⊤`. -/
theorem B_maximal {F : Type*} [Field F] [CharP F 2] (M : Subgroup (Work.Models.SL2 F))
    (hM : Work.Models.PSL2.B (F := F) ≤ M) (hne : M ≠ Work.Models.PSL2.B (F := F)) :
    M = ⊤ := by
  -- `M` contains an element outside `B`, otherwise `M = B`.
  have hex : ∃ g ∈ M, g ∉ B (F := F) := by
    by_contra h
    refine hne (le_antisymm (fun x hx => ?_) hM)
    by_contra hxB
    exact h ⟨x, hx, hxB⟩
  obtain ⟨g, hgM, hgB⟩ := hex
  -- the Bruhat decomposition of that element exhibits `w` as an element of `M`
  have hwM : w (F := F) ∈ M := by
    rcases bruhat (F := F) g with h | ⟨b₁, hb₁, b₂, hb₂, hg⟩
    · exact absurd h hgB
    · have hmem : b₁ * w (F := F) * b₂ ∈ M := hg ▸ hgM
      have hconj : b₁⁻¹ * (b₁ * w (F := F) * b₂) * b₂⁻¹ = w (F := F) := by group
      rw [← hconj]
      exact M.mul_mem (M.mul_mem (M.inv_mem (hM hb₁)) hmem) (M.inv_mem (hM hb₂))
  exact eq_top_of_le_of_mem_w M hM hwM

end Work.Models.PSL2
