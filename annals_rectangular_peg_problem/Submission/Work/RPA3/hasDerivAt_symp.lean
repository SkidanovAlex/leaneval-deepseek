import Mathlib
import Submission.Work.RPA3.Defs

namespace Work.RPA3

/-- Projection of a differentiable curve to the first component. -/
private theorem hasDerivAt_fst' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E × F} {f' : E × F} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).1) f'.1 x := by
  simpa [Function.comp_def] using
    ((ContinuousLinearMap.fst ℝ E F).hasFDerivAt.comp_hasDerivAt x h)

/-- Projection of a differentiable curve to the second component. -/
private theorem hasDerivAt_snd' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → E × F} {f' : E × F} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).2) f'.2 x := by
  simpa [Function.comp_def] using
    ((ContinuousLinearMap.snd ℝ E F).hasFDerivAt.comp_hasDerivAt x h)

/-- `symp` is a bilinear form, so it satisfies the product rule: differentiating
`symp (u y) (v y)` gives `symp u' (v x) + symp (u x) v'`. -/
theorem hasDerivAt_symp {u v : ℝ → PS} {u' v' : PS} {x : ℝ}
    (hu : HasDerivAt u u' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun y => symp (u y) (v y)) (symp u' (v x) + symp (u x) v') x := by
  have h11u : HasDerivAt (fun y => (u y).1.1) u'.1.1 x := hasDerivAt_fst' (hasDerivAt_fst' hu)
  have h12u : HasDerivAt (fun y => (u y).1.2) u'.1.2 x := hasDerivAt_snd' (hasDerivAt_fst' hu)
  have h21u : HasDerivAt (fun y => (u y).2.1) u'.2.1 x := hasDerivAt_fst' (hasDerivAt_snd' hu)
  have h22u : HasDerivAt (fun y => (u y).2.2) u'.2.2 x := hasDerivAt_snd' (hasDerivAt_snd' hu)
  have h11v : HasDerivAt (fun y => (v y).1.1) v'.1.1 x := hasDerivAt_fst' (hasDerivAt_fst' hv)
  have h12v : HasDerivAt (fun y => (v y).1.2) v'.1.2 x := hasDerivAt_snd' (hasDerivAt_fst' hv)
  have h21v : HasDerivAt (fun y => (v y).2.1) v'.2.1 x := hasDerivAt_fst' (hasDerivAt_snd' hv)
  have h22v : HasDerivAt (fun y => (v y).2.2) v'.2.2 x := hasDerivAt_snd' (hasDerivAt_snd' hv)
  have hA := h21u.mul h11v
  have hB := h22u.mul h12v
  have hC := h11u.mul h21v
  have hD := h12u.mul h22v
  have h := ((hA.add hB).sub hC).sub hD
  simp only [symp]
  convert h using 1
  ring

end Work.RPA3
