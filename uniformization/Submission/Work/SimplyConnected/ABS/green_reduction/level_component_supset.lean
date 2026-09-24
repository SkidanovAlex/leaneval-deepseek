import Mathlib

/-!
# A large sub-level component contains every compact set

Assembly brick for the "Sard-lite" route to
`Work.SimplyConnected.ABS.green_reduction.exists_barrier_regular_precompact_region`.

**If `g : X → ℝ` is continuous on a connected, locally path connected space `X` and `K` is compact,
then for all large enough `C` the connected component of `x₀` in the sub-level set `{g < C}`
contains `K ∪ {x₀}`.**

The argument is the one used in Anghel–Bruin–Stan's exhaustion (arXiv:2008.12189, proof of
Theorem 12), in its cleanest form: the family `C ↦ A_C := connectedComponentIn {g < C} x₀` is an
increasing family of open sets; `⋃_C A_C = X` because `X` is path connected (a path from `x₀` to `y`
has compact image, on which `g` is bounded); hence the `A_C` cover the compact `K ∪ {x₀}`, finitely
many of them suffice, and monotonicity reduces the finite family to one member.  In particular `K`
need not be connected.
-/

open Set Metric Filter
open scoped Topology

namespace Work.SimplyConnected.ABS.green_reduction

/-- **A large sub-level component contains every compact set.** -/

theorem exists_component_sublevel_supset {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {g : X → ℝ} (hg : Continuous g) {K : Set X} (hK : IsCompact K) (x₀ : X) :
    ∃ C : ℝ, K ∪ {x₀} ⊆ connectedComponentIn {x : X | g x < C} x₀ := by
  classical
  haveI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace ℂ X
  haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  haveI : PathConnectedSpace X := (pathConnectedSpace_iff_connectedSpace).mpr inferInstance
  set A : ℝ → Set X := fun C => connectedComponentIn {x : X | g x < C} x₀ with hA
  have hAopen : ∀ C : ℝ, IsOpen (A C) := fun C =>
    (isOpen_lt hg continuous_const).connectedComponentIn
  have hAmono : Monotone A := fun C C' hCC' =>
    connectedComponentIn_mono x₀ fun x hx => lt_of_lt_of_le hx hCC'
  have hcover : ∀ y : X, ∃ C : ℝ, y ∈ A C := by
    intro y
    obtain ⟨γ⟩ := PathConnectedSpace.joined x₀ y
    obtain ⟨z, hz, hzmax⟩ := (isCompact_range γ.continuous).exists_isMaxOn
      ⟨x₀, ⟨0, γ.source⟩⟩ hg.continuousOn
    refine ⟨g z + 1, ?_⟩
    have hsub : Set.range γ ⊆ {x : X | g x < g z + 1} := by
      rintro w ⟨s, rfl⟩
      exact lt_of_le_of_lt (isMaxOn_iff.mp hzmax (γ s) ⟨s, rfl⟩) (lt_add_one _)
    have hpre : IsPreconnected (Set.range γ) := isPreconnected_range γ.continuous
    have hx0 : x₀ ∈ Set.range γ := ⟨0, γ.source⟩
    exact hpre.subset_connectedComponentIn hx0 hsub ⟨1, γ.target⟩
  choose C hC using hcover
  have hKc : IsCompact (K ∪ {x₀}) := hK.union (isCompact_singleton (x := x₀))
  obtain ⟨T, hT⟩ := hKc.elim_finite_subcover A hAopen fun y _ => Set.mem_iUnion.mpr ⟨C y, hC y⟩
  obtain ⟨C₀, hC₀T, -⟩ := Set.mem_iUnion₂.mp (hT (Or.inr rfl))
  refine ⟨T.sup' ⟨C₀, hC₀T⟩ id, fun y hy => ?_⟩
  obtain ⟨C', hC'T, hyC'⟩ := Set.mem_iUnion₂.mp (hT hy)
  exact hAmono (Finset.le_sup' (f := id) hC'T) hyC'

end Work.SimplyConnected.ABS.green_reduction
