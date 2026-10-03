import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.Defs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.univalentExhaustion_of_exhaustion

/-!
# A relatively compact simply connected domain of a Riemann surface admits a univalent function

Let `Ω` be an open, connected, simply connected subset of a Riemann surface `X` with compact
closure, connected frontier and `Ω ≠ X`, and let `x₀ ∈ Ω`.  Then there is a function `ψ : X → ℂ`
which is holomorphic at every point of `Ω`, injective on `Ω`, and satisfies `ψ x₀ = 0`.

The argument is a reduction to the *space* `↥Ω` (the domain, as a Riemann surface in its own
right) together with the ABS theorem that every non-compact simply connected Riemann surface admits
an injective holomorphic map into `ℂ`
(`Work.SimplyConnected.ABS.exists_injective_holomorphic_of_isSimplyConnected_noncompact`).

* `↥Ω` is a Riemann surface: an open subset of `X` carries the restricted charts
  (`TopologicalSpace.Opens.instChartedSpace`, `…instIsManifold`), which is why we work with the
  `TopologicalSpace.Opens` `U = ⟨Ω, hΩo⟩` rather than with `↥Ω` directly;
* `↥Ω` is simply connected by hypothesis (`IsSimplyConnected Ω` *is* `SimplyConnectedSpace ↥Ω`);
* `↥Ω` is non-compact: otherwise `Ω` would be a non-empty clopen subset of the connected space `X`;
* a holomorphic `f : ↥Ω → ℂ` gives a function `X → ℂ` (extended by `0` outside `Ω`) which is still
  holomorphic at every point of `Ω`, because holomorphy is a *local* statement and the chart of the
  subspace at `x ∈ Ω` is the restriction of the chart of `X` at `x` (`opensChartAt_symm_eqOn`).
-/

namespace Work.SimplyConnected.ABS

open LeanEval.Geometry
open scoped Manifold ContDiff

noncomputable section

open Filter Set Classical

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Chart bookkeeping for an open subset

The chart of the open subset `U ⊆ X` at a point `u` is the restriction of the chart of `X` at `u`:
these two lemmas are all the bookkeeping needed to move a holomorphy statement from `↥U` to `X`.
-/

/-- The chart of an open subset `U` at `u` agrees, at `u`, with the ambient chart at `u`. -/
theorem opensChartAt_apply (U : TopologicalSpace.Opens X) (u : ↥U) :
    (chartAt ℂ u) u = (chartAt ℂ (u : X)) (u : X) := by
  rw [TopologicalSpace.Opens.chartAt_eq (x := u), OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- On the target of the chart of the open subset `U` at `u`, the inverse of that chart is the
restriction of the inverse of the ambient chart at `u`. -/
theorem opensChartAt_symm_eqOn (U : TopologicalSpace.Opens X) (u : ↥U) {z : ℂ}
    (hz : z ∈ (chartAt ℂ u).target) :
    (((chartAt ℂ u).symm z : ↥U) : X) = (chartAt ℂ (u : X)).symm z := by
  have h := OpenPartialHomeomorph.subtypeRestr_symm_eqOn (chartAt ℂ (u : X)) (U := U) ⟨u⟩
  have hz' : z ∈ ((chartAt ℂ (u : X)).subtypeRestr ⟨u⟩).target := hz
  exact (h hz').symm

/-! ## Transport of holomorphy from the subspace to the ambient surface -/

/-- **Transport of holomorphy.**  If `f` is holomorphic on all of the open subset `↥U`, then any
function on `X` agreeing with `f` on `U` is holomorphic at every point of `U`. -/
theorem holomorphicOnXAt_of_eqOn_subtype {U : TopologicalSpace.Opens X} {ψ : X → ℂ}
    {f : ↥U → ℂ} (hf : Submission.HolomorphicOnX f Set.univ) {x : X} (hx : x ∈ U)
    (heq : ∀ (y : X) (hy : y ∈ U), ψ y = f ⟨y, hy⟩) : Submission.HolomorphicOnXAt ψ x := by
  set u₀ : ↥U := ⟨x, hx⟩ with hu₀
  have hchart : (chartAt ℂ u₀) u₀ = (chartAt ℂ x) x := opensChartAt_apply U u₀
  have hmem : (chartAt ℂ x) x ∈ (chartAt ℂ u₀).target := by
    rw [← hchart]
    exact (chartAt ℂ u₀).map_source (mem_chart_source ℂ u₀)
  have hana : AnalyticAt ℂ (f ∘ (chartAt ℂ u₀).symm) ((chartAt ℂ x) x) := by
    rw [← hchart]
    exact hf u₀ (Set.mem_univ u₀)
  refine hana.congr ?_
  filter_upwards [(chartAt ℂ u₀).open_target.mem_nhds hmem] with z hz
  simp only [Function.comp_apply]
  have hsymm : (((chartAt ℂ u₀).symm z : ↥U) : X) = (chartAt ℂ x).symm z :=
    opensChartAt_symm_eqOn U u₀ hz
  have hzU : (chartAt ℂ x).symm z ∈ U := hsymm ▸ ((chartAt ℂ u₀).symm z).2
  rw [heq ((chartAt ℂ x).symm z) hzU]
  congr 1
  exact Subtype.ext hsymm

/-! ## Non-compactness of a proper clopen piece -/

/-- A non-empty open subset of a connected space that is not all of the space is not compact. -/
theorem not_compactSpace_of_mem_ne_univ [ConnectedSpace X] {U : TopologicalSpace.Opens X}
    {x : X} (hx : x ∈ U) (hne : (U : Set X) ≠ Set.univ) : ¬ CompactSpace ↥U := by
  intro hcomp
  have hK : IsCompact (U : Set X) := isCompact_iff_compactSpace.mpr hcomp
  have hcl : IsClosed (U : Set X) := hK.isClosed
  have hop : IsOpen (U : Set X) := U.2
  have huniv : (U : Set X) = Set.univ := by
    rcases (isClopen_iff.mp (show IsClopen (U : Set X) from ⟨hcl, hop⟩)) with h0 | h1
    · have hx' : x ∈ (U : Set X) := hx
      rw [h0] at hx'
      exact absurd hx' (by simp)
    · exact h1
  exact hne huniv

end

/-! ## The main statement -/

end Work.SimplyConnected.ABS
