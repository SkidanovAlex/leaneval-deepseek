import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm

namespace Work.NN.Final

open Work.CR.Flat

/-- `∂̄_j` is additive at points where both functions are real-differentiable. -/
private lemma dbarCoord_sub_aux {n : ℕ} (j : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    dbarCoord j (fun y => u y - v y) z = dbarCoord j u z - dbarCoord j v z := by
  have hfd : fderiv ℝ (fun y => u y - v y) z = fderiv ℝ u z - fderiv ℝ v z := fderiv_sub hu hv
  simp only [dbarCoord, hfd, sub_apply]
  ring

/-- `y ↦ ∂̄_j u y` is real-differentiable at `z` whenever `u` is `C²` there. -/
private lemma differentiableAt_dbarCoord_aux {n : ℕ} (j : Fin n) {u : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (hu : ContDiffAt ℝ 2 u z) :
    DifferentiableAt ℝ (fun y => dbarCoord j u y) z := by
  have h := diffAt_dbarOne (J := Work.NN.Core.JstdCn n) (w := u) (m := j) hu
    (differentiableAt_const _)
  simpa only [dbarOne_std] using h

/-- **The `(0,2)`-array `ddbar Jstd a` is always `Clos2`.**  For any `(0,1)`-array `a` and any point
`z` at which the components of `a` are `C²`, the antisymmetrised flat `∂̄`
`z ↦ (ddbar Jstd a) j l z = ∂̄_j (a l) z - ∂̄_l (a j) z`
satisfies the `(0,2)`-closedness condition `∂̄_i η_{lm} - ∂̄_l η_{im} + ∂̄_m η_{il} = 0` at `z`.

This is a purely formal consequence of the commutation `∂̄_i∂̄_l = ∂̄_l∂̄_i` of the flat operators
(`dbarCoord_comm`): all twelve terms cancel pairwise. -/
theorem clos2_ddbarStd {n : ℕ} (a : Fin n → Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n)
    (ha : ∀ p : Fin n, ContDiffAt ℝ 2 (a p) z) (i l m : Fin n) :
    Work.CR.Flat.dbarCoord i (fun z' => Work.NN.Final.ddbar (Work.NN.Core.JstdCn n) a l m z') z
      - Work.CR.Flat.dbarCoord l (fun z' => Work.NN.Final.ddbar (Work.NN.Core.JstdCn n) a i m z') z
      + Work.CR.Flat.dbarCoord m (fun z' => Work.NN.Final.ddbar (Work.NN.Core.JstdCn n) a i l z') z
      = 0 := by
  -- each `∂̄_j (a p)` is differentiable at `z`
  have hd : ∀ (j p : Fin n), DifferentiableAt ℝ (fun y : Fin n → ℂ => dbarCoord j (a p) y) z :=
    fun j p => differentiableAt_dbarCoord_aux j (ha p)
  -- expand the three `(0,2)`-arrays into their antisymmetrised components
  simp only [ddbar_std]
  -- distribute `∂̄` over the differences
  rw [dbarCoord_sub_aux i (fun y => dbarCoord l (a m) y) (fun y => dbarCoord m (a l) y) z
        (hd l m) (hd m l),
      dbarCoord_sub_aux l (fun y => dbarCoord i (a m) y) (fun y => dbarCoord m (a i) y) z
        (hd i m) (hd m i),
      dbarCoord_sub_aux m (fun y => dbarCoord i (a l) y) (fun y => dbarCoord l (a i) y) z
        (hd i l) (hd l i)]
  -- the mixed second derivatives commute, and the twelve terms cancel pairwise
  rw [Work.CR.Flat.Polydisc.dbarCoord_comm l i (a m) z (ha m),
      Work.CR.Flat.Polydisc.dbarCoord_comm m i (a l) z (ha l),
      Work.CR.Flat.Polydisc.dbarCoord_comm m l (a i) z (ha i)]
  ring

end Work.NN.Final
