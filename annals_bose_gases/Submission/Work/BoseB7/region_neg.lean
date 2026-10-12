import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB7.Q3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7

theorem region_neg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) :
    (∀ (KH a : ℝ) (i : Mode), F.PH KH a (-i) ↔ F.PH KH a i) ∧
    (∀ (KL μ a : ℝ) (i : Mode), F.PL KL μ a (-i) ↔ F.PL KL μ a i) ∧
    (∀ i : Mode, (-i ∈ Work.BoseB7.excited Mode) ↔ (i ∈ Work.BoseB7.excited Mode)) := by
  -- `PH` and `PL` are conditions on `‖kmom i‖` only, and `kmom` is odd, so both
  -- regions are invariant under `i ↦ -i`; ditto for the excited-mode set, which
  -- is `univ.erase 0` and `-i = 0 ↔ i = 0`.
  refine ⟨?_, ?_, ?_⟩
  · intro KH a i
    simp only [FockData.PH, F.kmom_neg, norm_neg]
  · intro KL μ a i
    simp only [FockData.PL, F.kmom_neg, norm_neg]
  · intro i
    simp only [Work.BoseB7.excited, Finset.mem_erase, Finset.mem_univ, and_true, neg_ne_zero]

end Work.BoseB7
