import Mathlib
import Submission.Work.ORHughesFree.StarRegular

namespace Work.ORHughesFree.StarRegular

theorem isProperStar_starSubring {U : Type*} [Ring U] [StarRing U] (hU : IsProperStar U)
    (S : StarSubring U) (x : S) (h : star x * x = 0) : x = 0 := by
  apply Subtype.ext
  have h' : star (x : U) * (x : U) = 0 := by
    have := congrArg (fun y : S => (y : U)) h
    rw [show ((star x * x : S) : U) = star ((x : S) : U) * ((x : S) : U) from rfl] at this
    exact this
  exact hU (x : U) h'

end Work.ORHughesFree.StarRegular
