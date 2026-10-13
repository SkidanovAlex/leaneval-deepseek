/-
  Work.WilC4aAL.SpecAlias

  The same-namespace alias of the deliverable: area C4a-AL owns the SPEC hole
  `WilkiesDesign.CG.C4a.C4a_arcLift` (module `Submission.Work.Wilkies.CG.C4a.Spec`), and this
  module records the proof under the mandated name `<same namespace>.<hole>_proved`.

  The primary theorem lives in `Submission/Work/WilC4aAL/Main.lean` as
  `Work.WilC4aAL.C4a_arcLift_proved`, which has exactly the hole's statement
  (`example : (PuiseuxReal → ArcLift) := @Work.WilC4aAL.C4a_arcLift_proved`).
-/
import Submission.Work.WilC4aAL.Main

set_option autoImplicit false
namespace WilkiesDesign.CG.C4a

/-- The C4a hole `C4a_arcLift`, proved: sign conditions realisable for all small `s` are
realised by an analytic `ζ` along `s = r ^ N` (alias of `Work.WilC4aAL.C4a_arcLift_proved`). -/
theorem C4a_arcLift_proved (hP : PuiseuxReal) : ArcLift :=
  Work.WilC4aAL.C4a_arcLift_proved hP

end WilkiesDesign.CG.C4a
