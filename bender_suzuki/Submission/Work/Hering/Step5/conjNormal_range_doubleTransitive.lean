import Mathlib
import Submission.Work.Hering.InvSubgroup
import Submission.Work.Hering.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The conjugation action on `V = Inv(G) ∪ {1}` is doubly transitive on `V \ {1}`

`V = invSubgroup hDT h4` consists of the involutions of `G` together with `1`, so its non-trivial
elements are exactly the involutions of `G`. Since `G` acts doubly transitively on its involutions
(`DTInv`), the conjugation action `G →* MulAut V` (`MulAut.conjNormal`) is doubly transitive on the
non-trivial elements of `V`: any two ordered pairs of distinct non-trivial elements of `V` are
carried to one another by an automorphism induced by an element of `G`.
-/

namespace Work.Hering.Step5

theorem conjNormal_range_doubleTransitive {G : Type*} [Group G] {hDT : DTInv G} {h4 : HasFourGroup G} :
    ∀ a b c d : ↥(invSubgroup hDT h4), a ≠ 1 → b ≠ 1 → c ≠ 1 → d ≠ 1 → a ≠ b → c ≠ d →
      ∃ g ∈ (@MulAut.conjNormal G _ (invSubgroup hDT h4) (invSubgroup_normal hDT h4)).range,
        g a = c ∧ g b = d := by
  -- A non-trivial element of `V` is an involution of `G`.
  have hmem : ∀ x : ↥(invSubgroup hDT h4), x ≠ 1 → orderOf (x : G) = 2 := by
    intro x hx
    have hx' := x.2
    rw [mem_invSubgroup] at hx'
    rcases hx' with h | h
    · exact h
    · exact absurd (Subtype.ext h) hx
  intro a b c d ha hb hc hd hab hcd
  -- Double transitivity of `G` on its involutions provides the conjugating element.
  obtain ⟨g, hg1, hg2⟩ :=
    hDT (a : G) (b : G) (c : G) (d : G)
      (hmem a ha) (hmem b hb) (hmem c hc) (hmem d hd)
      (fun h => hab (Subtype.ext h)) (fun h => hcd (Subtype.ext h))
  refine ⟨@MulAut.conjNormal G _ (invSubgroup hDT h4) (invSubgroup_normal hDT h4) g,
    ⟨g, rfl⟩, ?_, ?_⟩
  · apply Subtype.ext
    simpa only [MulAut.conjNormal_apply] using hg1
  · apply Subtype.ext
    simpa only [MulAut.conjNormal_apply] using hg2

end Work.Hering.Step5
