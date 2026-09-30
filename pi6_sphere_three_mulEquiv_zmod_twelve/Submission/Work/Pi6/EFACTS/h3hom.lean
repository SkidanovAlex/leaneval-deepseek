import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EFACTS.Basic
import Submission.Work.Pi6.EFACTS.h3zero
import Submission.Work.Pi6.SQASM.connHomology
import Submission.Work.Serre.serreConnectedCover
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EFACTS

open CategoryTheory CategoryTheory.Limits

/-- **`H₃(S³⟨3⟩;ℤ) = 0`.**  The cover `E = Ecov g3 = hofib(g3 : S³ → P₃)` of a Postnikov section
`g3` with `PostnikovData 3 12` is `3`-connected: `Work.Serre.serreConnectedCover` applied to
`g3` (bijective on `π_i` for `i ≤ 3`, and `π_i(P₃) = 0` for `3 < i ≤ 12`) gives
`π_i(E) = 0` for `i ≤ 3`.  A `3`-connected space has vanishing integral reduced homology in
degrees `0 < i ≤ 3` (`Work.Pi6.SQASM.connHomology`, the integral range Whitehead theorem applied to
the constant map `E → PUnit`), so in particular `H₃(E;ℤ) = 0`. -/
theorem h3hom {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) (hP3 : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3) : Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 3) := by
  -- `E = S³⟨3⟩` is 3-connected
  have hconn : ∀ i : ℕ, i ≤ 3 →
      Subsingleton (HomotopyGroup (Fin i) (Work.Pi6.Ecov g3) (Work.Pi6.e0 g3)) :=
    (Work.Serre.serreConnectedCover 3 12 (by norm_num) (by norm_num) Work.Pi6.S3 Work.Pi6.s3 P3 g3
      (fun i hi => hP3.1 i hi Work.Pi6.s3) hP3.2).1
  -- connectivity gives vanishing reduced homology: `H₃(E;ℤ) = 0`
  have hZ3 : IsZero (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 3) :=
    Work.Pi6.SQASM.connHomology (Work.Pi6.e0 g3) 3 3 hconn (by norm_num) (by norm_num)
  exact ModuleCat.isZero_iff_subsingleton.mp hZ3

end Work.Pi6.EFACTS
