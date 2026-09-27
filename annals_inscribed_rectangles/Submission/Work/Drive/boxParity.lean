import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.BoxParityDefs
import Submission.Work.Drive.BoxParityAux
import Submission.Work.Drive.bdyZeros_finite
import Submission.Work.Drive.even_ncard_of_involution
import Submission.Work.Drive.BoxParityPair

/-!
# Mod-2 boundary parity of transversally cut-out zero sets on a box

`Submission.Drive.ParityProp`: if `F : ℝ^{m+1} → ℝ^m` is smooth, `0` is a regular value on the box
`[0,1]^{m+1}`, and every zero on the boundary of the box lies on exactly one face, transversally,
then the zeros of `F` on the boundary are finite in number and even in number.

The proof replaces the usual cohomological argument by an explicit mod-2 count: the compactly
supported tangential field `flowField F` (a bump function times the normalised cofactor vector of
`fderiv ℝ F`) has flow lines along which `F` is constant.  Each boundary zero `b` is the endpoint of
exactly one arc of the zero set lying in the interior of the box; following the flow line through `b`
forwards or backwards reaches the other endpoint `pairPt F hF b`.  This pairs the boundary zeros by a
fixed-point-free involution, so their number is even.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set

open Submission.Drive

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- **The pairing in the general case.**  For every boundary zero `b`, the point `pairPt F hF b` is
again a boundary zero, distinct from `b`, and `pairPt` is an involution on the boundary zeros. -/
theorem pairPt_spec {m : ℕ} {F : Amb m → Tgt m} (hF : ContDiff ℝ Ctop F)
    (hreg : ∀ x ∈ unitBox m, F x = 0 → Function.Surjective (fderiv ℝ F x))
    (hbdy : ∀ x ∈ unitBoxBdry m, F x = 0 → ∃ i : Fin (m + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb m // v i = 0} => fderiv ℝ F x v.1))
    {b : Amb m} (hb : b ∈ bdyZeros F) :
    pairPt F hF b ∈ bdyZeros F ∧ pairPt F hF b ≠ b ∧
      pairPt F hF (pairPt F hF b) = b := by
  obtain ⟨i, hbi, hbother, hsurj⟩ := hbdy b hb.1 hb.2
  have hne : flowField F b i ≠ 0 := flowField_apply_ne_zero_of_bdy hb.1.1 hsurj
  obtain ⟨ε, hε, hcase⟩ := crossing_of_deriv_ne_zero (flowCurve_hasDerivAt F hF b)
    (flowCurve_zero F hF b) i ⟨hbi, hbother⟩ hne
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact pairPt_spec_right hF hreg hbdy hb hε ⟨h1, h2⟩
  · exact pairPt_spec_left (ε := -ε) hF hreg hbdy hb (by linarith) ⟨h1, by simpa using h2⟩

/-- **Mod-2 boundary parity of transversally cut-out zero sets on a box.** -/
theorem boxParity : Submission.Drive.ParityProp := by
  intro m F hF hreg hbdy
  have hfin : (bdyZeros F).Finite := bdyZeros_finite hF hbdy
  refine ⟨hfin, ?_⟩
  refine even_ncard_of_involution hfin (pairPt F hF) ?_ ?_ ?_
  · intro x hx
    exact (pairPt_spec hF hreg hbdy hx).1
  · intro x hx
    exact (pairPt_spec hF hreg hbdy hx).2.2
  · intro x hx
    exact (pairPt_spec hF hreg hbdy hx).2.1

end

end Work.Drive
