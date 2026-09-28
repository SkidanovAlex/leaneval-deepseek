import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.detL_span_gram
import Submission.Work.HP.Lat.prim_bezout
import Submission.Work.HP.Lat.exists_int_extends
import Submission.Work.HP.FM.veronese_lat

namespace Work.HP.FM3

/-- For a primitive integer vector `c`, the orthogonal lattice `Λ_c = {y : ⟨c,y⟩ = 0}` has
covolume `‖c‖` in its real span.

This is the "free" (`ι`-generic) form of the Veronese lattice fact
`Work.HP.FM.detL_latOrth_of_prim`, restated with the bare `Work.HP` definitions. -/
theorem detL_latOrth_free {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℤ) (hc : IsPrim c) :
    detL (latOrth c) = eNorm c :=
  Work.HP.FM.detL_latOrth_of_prim c hc

end Work.HP.FM3
