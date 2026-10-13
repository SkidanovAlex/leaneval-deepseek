import Mathlib
import Submission.Work.WilG4a.lip_loci_defs

set_option autoImplicit false
noncomputable section
open Classical
open WilkiesConjecture WilkiesDesign
namespace Work.WilG4a

theorem posSetAux_eq (p : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ) :
    Work.WilG4a.posSetAux f = Work.WilG4a.posSet f := by
  ext z
  simp only [posSetAux, posSet, projLast, posHalf, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Fin.snoc_last]
  constructor
  · rintro ⟨t, h1, h2⟩
    refine ⟨t, ?_, h2⟩
    rwa [mem_derSet, Fin.init_snoc, Fin.snoc_last] at h1
  · rintro ⟨s, hs, hspos⟩
    exact ⟨s, (mem_derSet f (Fin.snoc z s)).mpr (by simpa using hs), by simpa using hspos⟩

end Work.WilG4a
