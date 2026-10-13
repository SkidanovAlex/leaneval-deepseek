import Mathlib

namespace Work.DSG2

theorem closure_range_comp_eq_of_denseRange {X Y T : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] (i : Y → X) (g : X → T) (hi : DenseRange i) (hg : Continuous g) :
    closure (Set.range fun y => g (i y)) = closure (Set.range g) := by
  apply Set.Subset.antisymm
  · exact closure_mono (Set.range_comp_subset_range i g)
  · calc closure (Set.range g) = closure (g '' Set.univ) := by rw [Set.image_univ]
    _ = closure (g '' closure (Set.range i)) := by rw [hi.closure_eq]
    _ ⊆ closure (closure (g '' Set.range i)) :=
        closure_mono (image_closure_subset_closure_image hg (s := Set.range i))
    _ = closure (g '' Set.range i) := closure_closure
    _ = closure (Set.range fun y => g (i y)) := by rw [Set.range_comp' g i]

end Work.DSG2
