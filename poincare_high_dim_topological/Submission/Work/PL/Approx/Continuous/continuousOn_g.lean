import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Cutoff.continuous_cubeCut

namespace Work.PL.Approx.Continuous

/-- The G5 cutoff deformation `g x = f x + cubeCut β'' β' (f x) • (ℓ x - f x)` is continuous on
`K.space` whenever `f` and `ℓ` are.  Only continuity of the cutoff `cubeCut β'' β'` (true for all
`β''`, `β'`, with no non-degeneracy hypothesis) is used. -/
lemma continuousOn_g {N n : ℕ} (K : PL.Cx N) (f ℓ : PL.E N → PL.E n) (β'' β' : ℝ)
    (hf : ContinuousOn f K.space) (hℓ : ContinuousOn ℓ K.space) :
    ContinuousOn (fun x => f x + cubeCut β'' β' (f x) • (ℓ x - f x)) K.space := by
  have hc : Continuous (fun y : PL.E n => cubeCut β'' β' y) :=
    Work.PL.Approx.Cutoff.continuous_cubeCut β'' β'
  exact hf.add ((hc.comp_continuousOn hf).smul (hℓ.sub hf))

end Work.PL.Approx.Continuous
