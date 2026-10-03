import Mathlib
import Submission.Work.ORHughesFree.Prop51.ConclB

namespace Work.ORHughesFree.Prop51

theorem conclB_add {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    {x y : P} {T₁ T₂ : Work.ORHughesFree.Tree}
    (hx : Work.ORHughesFree.Prop51.ConclB d x T₁) (hy : Work.ORHughesFree.Prop51.ConclB d y T₂) :
    Work.ORHughesFree.Prop51.ConclB d (x + y) (T₁ + T₂) := by
  obtain ⟨f, hf, hfb, hfk⟩ := hx
  obtain ⟨g, hg, hgb, hgk⟩ := hy
  refine ⟨f + g, by rw [map_add, hf, hg], ?_, ?_⟩
  · intro k
    exact Tree.le_trans (treeH_le_add d (d.coeffToP_mem (f.1 k)) (d.coeffToP_mem (g.1 k)))
      (Tree.le_add (hfb k) (hgb k))
  · intro k hk j hj
    have hsum : d.treeH (d.coeffToP (f.1 k)) + d.treeH (d.coeffToP (g.1 k)) = T₁ + T₂ :=
      Tree.le_antisymm (Tree.le_add (hfb k) (hgb k))
        (hk ▸ treeH_le_add d (d.coeffToP_mem (f.1 k)) (d.coeffToP_mem (g.1 k)))
    obtain ⟨h1, h2⟩ := (Tree.le_add_eq (hfb k) (hgb k)).mp hsum
    rw [SkewLaurentSeries.add_apply, hfk k h1 j hj, hgk k h2 j hj, add_zero]

end Work.ORHughesFree.Prop51
