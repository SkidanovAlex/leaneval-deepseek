import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.region_with_sector_boundary

/-!
# The sector condition at a regular frontier point of a sub-level component

This module isolates the *point-set* part of the "smooth exhaustion" route to the region
`Ω` of `exists_barrier_regular_precompact_region`: if `A` is the connected component of `x₀` in the
open sub-level set `{g < C}` of a *continuous* function `g`, then

* a point of `{g < C}` lying in the closure of `A` already lies in `A`
  (`mem_connectedComponentIn_of_mem_closure`, local connectedness of `X` supplying a connected
  neighbourhood);
* hence every frontier point of `A` satisfies `g p = C`
  (`eq_of_mem_frontier_connectedComponentIn`), so that at a frontier point at which the chart
  pull-back of `g` is differentiable with non-zero derivative the *sector condition* holds for `A`
  (`hasSectorBoundary_of_regular_level_component`), by `hasSectorBoundary_of_local_sublevel`.

Consequently the target `exists_barrier_regular_precompact_region` of this directory follows from the
existence of a smooth exhaustion function `g` of `X` and a level `C` which is **not a critical value**
of `g` (Sard's lemma for a function of two variables, absent from Mathlib): take `A` for the level
component containing `K ∪ {x₀}` and `Ω := A`.  This is the route used by Anghel–Bruin–Stan,
*Uniformization of Riemann surfaces revisited* (arXiv:2008.12189), and the reason this file is
stated separately. -/

open Set Filter
open scoped Topology Manifold ContDiff

set_option linter.unusedSectionVars false

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **A point of an open set lying in the closure of a connected component lies in it.**

Local connectedness supplies a connected neighbourhood `V` of `y` inside the open set `U`; since `y`
lies in the closure of the component, `V` meets the component, so `V ∪ component` is a preconnected
subset of `U` containing the base point, hence is contained in the component. -/
lemma mem_connectedComponentIn_of_mem_closure [LocallyConnectedSpace X] {U : Set X} (hUo : IsOpen U)
    {x₀ y : X} (hx₀U : x₀ ∈ U) (hyU : y ∈ U) (hy : y ∈ closure (connectedComponentIn U x₀)) :
    y ∈ connectedComponentIn U x₀ := by
  obtain ⟨V, ⟨hVopen, hyV, hVconn⟩, hVsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis y).mem_iff.mp (hUo.mem_nhds hyU)
  obtain ⟨z, hzV, hzA⟩ := mem_closure_iff.mp hy V hVopen hyV
  have hpre : IsPreconnected (V ∪ connectedComponentIn U x₀) :=
    IsPreconnected.union' ⟨z, hzV, hzA⟩ hVconn.isPreconnected
      isPreconnected_connectedComponentIn
  have hsub : V ∪ connectedComponentIn U x₀ ⊆ U := by
    rintro w (hw | hw)
    · exact hVsub hw
    · exact connectedComponentIn_subset U x₀ hw
  exact hpre.subset_connectedComponentIn (Or.inr (mem_connectedComponentIn hx₀U)) hsub (Or.inl hyV)

/-- **A frontier point of a connected component of an open sub-level set realises the level.** -/
lemma eq_of_mem_frontier_connectedComponentIn [LocallyConnectedSpace X] {g : X → ℝ}
    (hgcont : Continuous g) {C : ℝ} {x₀ p : X}
    (hx₀ : x₀ ∈ connectedComponentIn {x : X | g x < C} x₀)
    (hp : p ∈ frontier (connectedComponentIn {x : X | g x < C} x₀)) : g p = C := by
  have hUo : IsOpen {x : X | g x < C} := isOpen_lt hgcont continuous_const
  have hAle : closure (connectedComponentIn {x : X | g x < C} x₀) ⊆ {x : X | g x ≤ C} :=
    closure_minimal (fun y hy => show g y ≤ C from
      le_of_lt (connectedComponentIn_subset {x : X | g x < C} x₀ hy))
      (isClosed_le hgcont continuous_const)
  refine le_antisymm (hAle hp.1) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hAopen : IsOpen (connectedComponentIn {x : X | g x < C} x₀) := hUo.connectedComponentIn
  have hpA : p ∉ connectedComponentIn {x : X | g x < C} x₀ := by
    have h := hp
    rw [hAopen.frontier_eq] at h
    exact h.2
  exact hpA (mem_connectedComponentIn_of_mem_closure hUo
    (connectedComponentIn_subset {x : X | g x < C} x₀ hx₀) hcon hp.1)

/-- **The sector condition at a regular frontier point of a sub-level component.**

If `p` is a frontier point of the connected component `A` of `x₀` in `{g < C}` and the chart
pull-back of `g` at `p` is differentiable with non-zero derivative, then `A` satisfies the sector
condition at `p`: `A` is locally the sub-level set `{g < C}`, whose complement contains a half-plane
through `p`. -/
theorem hasSectorBoundary_of_regular_level_component [LocallyConnectedSpace X] [ConnectedSpace X]
    [SecondCountableTopology X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [SimplyConnectedSpace X]
    {g : X → ℝ}
    (hgcont : Continuous g) {C : ℝ} {x₀ p : X}
    (hx₀ : x₀ ∈ connectedComponentIn {x : X | g x < C} x₀)
    (hp : p ∈ frontier (connectedComponentIn {x : X | g x < C} x₀))
    (hdiff : DifferentiableAt ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p))
    (hfd : fderiv ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ≠ 0) :
    HasSectorBoundary (connectedComponentIn {x : X | g x < C} x₀) p := by
  refine hasSectorBoundary_of_local_sublevel (W := connectedComponentIn {x : X | g x < C} x₀)
    (u := g) (L := fderiv ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p))
    hdiff.hasFDerivAt hfd ?_
  refine Filter.Eventually.of_forall fun y hy => ?_
  rw [eq_of_mem_frontier_connectedComponentIn hgcont hx₀ hp]
  exact not_lt.mpr (le_of_lt (connectedComponentIn_subset {x : X | g x < C} x₀ hy))

/-- **The sector condition at every frontier point of a level component of a regular level.**

If `C` is a *regular* level of the (merely continuous, on the level set) function `g` - more
precisely, at every point where `g = C` the chart pull-back of `g` is differentiable with non-zero
derivative - then every frontier point of the connected component `A` of `x₀` in `{g < C}` carries
the sector condition.  Together with `barriers_of_sector_or_ray` (in
`green_reduction/exists_barrier_regular_precompact_region.lean`) this proves the target as soon as
`K ∪ {x₀} ⊆ A` for some regular level `C`.

Producing such a level for a `C^inf` exhaustion function is Sard's lemma for a function of two
variables; the workspace's `Work.CriticalSet` supplies it for *harmonic* functions (isolated
critical points, hence countably many critical values), which is why the Green-function route to the
target works. -/
theorem hasSectorBoundary_of_regular_level [LocallyConnectedSpace X] [ConnectedSpace X]
    [SecondCountableTopology X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] [SimplyConnectedSpace X]
    {g : X → ℝ} {C : ℝ} {x₀ : X}
    (hx₀ : x₀ ∈ connectedComponentIn {x : X | g x < C} x₀) (hcont : Continuous g)
    (hreg : ∀ p : X, g p = C →
      DifferentiableAt ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ∧
      fderiv ℝ (fun z : ℂ => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ≠ 0) :
    ∀ p ∈ frontier (connectedComponentIn {x : X | g x < C} x₀),
      HasSectorBoundary (connectedComponentIn {x : X | g x < C} x₀) p := by
  intro p hp
  have hgp : g p = C := eq_of_mem_frontier_connectedComponentIn hcont hx₀ hp
  exact hasSectorBoundary_of_regular_level_component hcont hx₀ hp (hreg p hgp).1 (hreg p hgp).2

end Work.SimplyConnected.ABS
