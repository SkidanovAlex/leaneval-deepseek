import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.pinchedMap_nullHomotopic
import Submission.Work.RatHurewicz.attachIncl_isOpenMap_range
import Submission.Work.RatHurewicz.AttachRange.AttachInclInj
import Submission.Work.RatHurewicz.CubeToPinched
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv
import Submission.Work.RatHurewicz.CompressRelToRelPi

namespace Work.RatHurewicz

/-- **Compression of the pair `(Y', range attachIncl)` implies the vanishing of the relative
homotopy groups of the attachment.**  If every map of pairs `(I^d, ∂I^d) → (Y', range attachIncl)`
with `d ≤ n+1` is homotopic relative to `∂I^d` into the range, then the homotopy fibre of
`attachIncl n Y ι f` at `y₀` has trivial homotopy groups in degrees `≤ n`:
`Subsingleton (RelHomotopyGroup (attachIncl n Y ι f) y₀ j)` for `j ≤ n`.

Route: `attachIncl` is injective (`Work.RatHurewicz.AttachRange.attachIncl_injective`) and an
embedding onto its range (`Work.RatHurewicz.attachIncl_isOpenMap_range`,
`isInducing_attachIncl`), so `Y ≃ₜ ↥(range attachIncl)` and the homotopy fibres of `attachIncl` and
of `setIncl (range attachIncl)` are homeomorphic; homotopy groups transport along a homeomorphism by
`Work.Stems.mulEquiv_of_homotopyEquiv`.  So it suffices to show the vanishing for the pair
`A := range attachIncl ⊆ Y'`.  The compression gives that `π_k(↥A) → π_k(Y')` (induced by the
inclusion) is bijective for `k ≤ n` and surjective for `k = n+1`: compressing based `k`-cubes gives
surjectivity at degree `k ≤ n+1`, compressing based `(k+1)`-cubes gives injectivity at degree
`k ≤ n` (`Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel` supplies bijectivity for degrees
`≤ n-1`; the top cases are direct).  Then `Work.RatHurewicz.pair_les` (exactness slots of index
`≥ 2`) gives `RelHomotopyGroup ... j = 0` for `2 ≤ j ≤ n`, using injectivity at `j` and surjectivity
at `j+1`.  The low indices `j = 0, 1` and the top case `j = n` are handled by the compression at
level `j + 1 ≤ n+1` applied to the pinched cube of a relative element: the pinch dictionary
(`Work.RatHurewicz.pinchCube`) turns a based `j`-cube in the homotopy fibre into a pinched map of
pairs, the compression homotopy is fixed *pointwise* on the boundary (hence on the pinch set), and
currying it gives a homotopy of based cubes in the fibre. -/
theorem subsingleton_relPi_of_compressRel_range (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (y₀ : Y)
    (hcomp : ∀ d, d ≤ n + 1 → Work.RatHurewicz.CompressRel (Work.RatHurewicz.attachCells n Y ι f)
      (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) d) :
    ∀ j, j ≤ n → Subsingleton
      (Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.attachIncl n Y ι f) y₀ j) := by
  intro j hj
  exact subsingleton_relPi_attachIncl_of_range n Y ι f y₀ j
    (subsingleton_relPi_of_compressRel n (A := Set.range (attachIncl n Y ι f))
      ⟨attachIncl n Y ι f y₀, y₀, rfl⟩ hcomp j hj)

end Work.RatHurewicz
