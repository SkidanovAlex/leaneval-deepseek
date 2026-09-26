import Submission.Work.BoxShrink.Pinch.LatticePath
import Mathlib.Topology.Order.ProjIcc

/-!
# The planarity criterion, first half: the pieces of a rank-`0` region lift to the plane

The analysis of README §10.3 uses the following consequence of `WindingSpan P X = ⊥`: the components
of `X` are not wrapped around the torus — equivalently, every component of the preimage
`Φ⁻¹ X` maps *injectively* into `X`, so that each component of `X` lifts to the universal cover and
is therefore planar.

This module proves the form in which the analysis consumes it, and which needs no new topology: **no
path-connected subset of `Φ⁻¹ X` contains two points differing by a nonzero lattice shift.**  The
path is turned into an essential loop by `LatticePath.containsEssentialLoop_of_path_shift`, so the
statement is the contrapositive of the dictionary, with `IsPathConnected` supplying the path (the
components of an *open* region are path-connected, so this is exactly the "components lift"
statement for the open pieces occurring in the pinch: `boxRegion`, `upperRegion`, `lowerRegion`).

* `Work.BoxShrink.Pinch.not_containsEssentialLoop_of_isPathConnected_period` — the criterion;
* `Work.BoxShrink.Pinch.not_containsEssentialLoop_of_period_of_path` — the same with a path of
  `[0,1]` given explicitly;
* `Work.BoxShrink.Pinch.isPathConnected_periodFree` — the "components lift" corollary.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The planarity criterion (path form).**  If `X` carries no essential loop, then no continuous
path of the preimage `Φ⁻¹ X` joins two points differing by a nonzero lattice shift. -/
theorem not_containsEssentialLoop_of_period_of_path {X : Set R3}
    (hX : ¬ P.ContainsEssentialLoop X) {k l : ℤ} (hne : (k, l) ≠ 0) {q : ℝ → ℝ × ℝ}
    (hq : Continuous q) (h1 : q 1 = q 0 + Work.TorusCover.periodShift (k, l))
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, q t ∈ planePreimage P X) : False :=
  hX (containsEssentialLoop_of_path_shift (P := P) hq h1 hne fun t ht => (hmem t ht : Phi P (q t) ∈ X))

/-- **The planarity criterion (path-connected form).**  No path-connected subset of the preimage of
an inessential region contains two points differing by a nonzero lattice shift.  Equivalently: the
components of `Φ⁻¹ X` are *injective* over `X`, i.e. every component of `X` lifts to the universal
cover. -/
theorem not_containsEssentialLoop_of_isPathConnected_period {X : Set R3}
    (hX : ¬ P.ContainsEssentialLoop X) {W : Set (ℝ × ℝ)} (hW : IsPathConnected W)
    (hWsub : W ⊆ planePreimage P X) {k l : ℤ} (hne : (k, l) ≠ 0) {q : ℝ × ℝ} (hq : q ∈ W)
    (hq' : q + Work.TorusCover.periodShift (k, l) ∈ W) : False := by
  obtain ⟨γ, hγ⟩ := hW.joinedIn q hq (q + Work.TorusCover.periodShift (k, l)) hq'
  have hq1 : γ 1 = q + Work.TorusCover.periodShift (k, l) := γ.target
  have hq0 : γ 0 = q := γ.source
  refine not_containsEssentialLoop_of_period_of_path (P := P) (q := fun t =>
    γ (Set.projIcc (0 : ℝ) 1 (by norm_num) t)) hX hne ?_ ?_ ?_
  · exact γ.continuous.comp (continuous_projIcc)
  · have e1 : (Set.projIcc (0 : ℝ) 1 (by norm_num) 1 : Set.Icc (0 : ℝ) 1) = 1 := by
      rw [Set.projIcc_right]
      exact Subtype.ext rfl
    have e0 : (Set.projIcc (0 : ℝ) 1 (by norm_num) 0 : Set.Icc (0 : ℝ) 1) = 0 := by
      rw [Set.projIcc_left]
      exact Subtype.ext rfl
    show γ (Set.projIcc (0 : ℝ) 1 (by norm_num) 1) =
      γ (Set.projIcc (0 : ℝ) 1 (by norm_num) 0) + Work.TorusCover.periodShift (k, l)
    rw [e1, e0, hq1, hq0]
  · intro t _
    exact hWsub (hγ _)

/-- **The components of an inessential region lift to the plane.**  Restatement of the criterion:
a *path-connected* subset of the preimage of an inessential region cannot meet its own translate by
a nonzero period. -/
theorem isPathConnected_periodFree {X : Set R3} (hX : ¬ P.ContainsEssentialLoop X)
    {W : Set (ℝ × ℝ)} (hW : IsPathConnected W) (hWsub : W ⊆ planePreimage P X) {k l : ℤ}
    (hne : (k, l) ≠ 0) :
    Disjoint W (W.image fun z => z + Work.TorusCover.periodShift (k, l)) := by
  rw [Set.disjoint_left]
  rintro q hq ⟨q', hq'W, hq'eq⟩
  have hqv : q' + Work.TorusCover.periodShift (k, l) ∈ W := by
    rw [show q' + Work.TorusCover.periodShift (k, l) = q from hq'eq]
    exact hq
  exact not_containsEssentialLoop_of_isPathConnected_period (P := P) hX hW hWsub hne hq'W hqv

end

end Work.BoxShrink.Pinch
