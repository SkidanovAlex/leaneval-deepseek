import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.CritFixDefs
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.CritFixAux.Pre
import Submission.Work.WilG4c.CritFixAux.Fill

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilkG4c

theorem CritFixGoodMem (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S)
    (hder : WilkiesDesign.SOMin.SharpDeriv S) (p n F0 : ℕ) :
    ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.AlDgListSlice p n f L ∩ Work.WilkG4c.AlGood p n f L =
        Work.WilkG4c.CritFix p n f L ∩ Work.WilkG4c.AlGood p n f L := by
  intro D f L hf
  ext z
  constructor
  · rintro ⟨hz, hzg⟩
    exact ⟨AlDgListSlice_subset_CritFix f L hz, hzg⟩
  · rintro ⟨hz, hzg⟩
    exact ⟨critFix_inter_AlGood_subset S hcd hder F0 D f L hf ⟨hz, hzg⟩, hzg⟩

end Work.WilkG4c

namespace Work.WilG4c

/-- Alias of `Work.WilkG4c.CritFixGoodMem` in the namespace of the directory, so that clients of
the module `Submission.Work.WilG4c.CritFixGoodMem` may refer to it under either spelling. -/
theorem CritFixGoodMem (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S)
    (hder : WilkiesDesign.SOMin.SharpDeriv S) (p n F0 : ℕ) :
    ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.AlDgListSlice p n f L ∩ Work.WilkG4c.AlGood p n f L =
        Work.WilkG4c.CritFix p n f L ∩ Work.WilkG4c.AlGood p n f L :=
  Work.WilkG4c.CritFixGoodMem S hcd hder p n F0

end Work.WilG4c
