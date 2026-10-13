import Mathlib
import Submission.Work.WilE3.Frame.Vcoef

namespace Work.WilE3.Frame

lemma injective_iota_of_jacValC_ne_zero {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r) (h : Fin j → WilkiesDesign.E.EAPoly k r)
    (ι : Fin j → Fin k) (z : Fin k → ℂ) (hz : Work.WilE3.Frame.jacValC c h ι z ≠ 0) :
    Function.Injective ι := by
  intro a b hab
  by_contra hne
  refine hz ?_
  rw [jacValC_eq_det]
  refine Matrix.det_zero_of_column_eq hne ?_
  intro x
  simp only [jacMatC, Matrix.of_apply, hab]

end Work.WilE3.Frame
