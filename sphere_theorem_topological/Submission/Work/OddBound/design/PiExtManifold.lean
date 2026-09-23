import Mathlib
import Submission.Work.OddBound.PiExtChart

/-!
# Design: the smooth structure on the polygon space modelled on `Fin (N-1) → E`

`PiExtChart.lean` builds the charted space `piChartedSpaceExt` on `P = Fin (N-1) → M` out of the
`E`-valued extended charts `extChartHomeo`.  Three glue facts are needed before the mountain pass and
the index transfer can be applied:

1. **`Work.OddBound.isManifold_chartedSpaceExtChart`** — the charted space
   `chartedSpaceExtChart` on `M` (extended charts) is a `C^n` manifold for every `n`.
   Proof: the transition of two extended charts is `extChartAt I x' ∘ (extChartAt I x).symm`, which
   is `C^n` in the *standard* (Euclidean) calculus because
   `ContMDiffAt I 𝓘(ℝ,E) n (extChartAt I x)` and
   `ContMDiffOn 𝓘(ℝ,E) I n (extChartAt I x).symm` compose through the mixed-model chain rule
   (`Mathlib/Geometry/Manifold/ContMDiff/Atlas.lean`); `extChartHomeo x` is `extChartAt I x` as a
   function (`extChartHomeo_coe`), so the same holds for it.

2. **`Work.OddBound.isManifold_piChartedSpaceExt`** — the product `piChartedSpaceExt` on
   `Fin (N-1) → M` is a `C^n` manifold over `𝓘(ℝ, Fin (N-1) → E)`.
   Proof: `Work.piManifold.isManifold_pi` applied to the structure of (1), together with
   `ModelWithCorners.pi (fun _ ↦ 𝓘(ℝ,E)) = 𝓘(ℝ, Fin (N-1) → E)` (both are the identity model on the
   product).

3. **`Work.OddBound.exists_piExtChart_eq_of_mem_atlas`** — every chart of the atlas of
   `piChartedSpaceExt` is a product of *individual* extended charts, i.e. is `piExtChart x` for some
   vertex list `x`.  This is what lets a caller turn the existential `IsCriticalChart` (some chart
   with vanishing coordinate derivative) into the concrete hypotheses `hC2`, `hF0` of the index
   transfer `Work.OddBound.indexTransfer.hasNegDefPlane_of_negativeDirichletIndex`.
   Proof: `piChartedSpace`'s atlas is `OpenPartialHomeomorph.pi '' Set.pi univ (fun _ => atlas E M)`
   and `atlas E M = Set.range (extChartHomeo (I := I))` by definition of `chartedSpaceExtChart`.
-/

namespace Work.OddBound

end Work.OddBound
