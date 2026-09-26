import Mathlib
import Submission.Work.PTCert.GlueDefs

namespace Work.PTCert.ldlChainSound

theorem dotZ_comm (a b : List ℤ) : Submission.PTCert.dotZ a b = Submission.PTCert.dotZ b a := by
  induction a generalizing b with
  | nil => simp [Submission.PTCert.dotZ]
  | cons x as ih =>
    cases b with
    | nil => simp [Submission.PTCert.dotZ]
    | cons y bs =>
      show x * y + Submission.PTCert.dotZ as bs = y * x + Submission.PTCert.dotZ bs as
      rw [ih bs, mul_comm]

end Work.PTCert.ldlChainSound
