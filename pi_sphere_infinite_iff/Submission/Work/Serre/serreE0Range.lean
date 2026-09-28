import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.E0Induction
import Submission.Work.Serre.e0ChainAlgebra
import Submission.Work.Stems.exists_collapsingMap
import Submission.Work.Stems.subsingleton_homotopyGroup_change_basepoint
import Submission.Work.RatHurewicz.Bridge.exists_collapse_simplex
import Submission.Work.RatHurewicz.ConnectivityBridge

namespace Work.Serre

/-- **Serre's `E0` in range form.**  If `πᵢ(X,x₀)` is trivial for every `i ≤ N` then the rational
homology of `X` vanishes in degrees `0 < j ≤ N`.

The two ingredients are `Work.Serre.exists_coneData` (cone/filler data on the singular simplicial
set, from the vanishing of the homotopy groups in range) and `Work.Serre.e0ChainAlgebra` (cone data
gives a chain contraction, hence vanishing homology). -/
theorem serreE0Range : Work.Serre.SerreE0Range :=
  fun X _ x₀ N h => e0ChainAlgebra X N (exists_coneData x₀ N h)

end Work.Serre
