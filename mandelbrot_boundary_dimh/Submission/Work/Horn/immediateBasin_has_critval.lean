import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Main
import Submission.Work.Horn.localBiholo_source_subset
import Submission.Work.Horn.isLocalHomeomorphOn_subtypeMap
import Submission.Work.Horn.isCoveringMap_subtypeMap

/-!
# A non-injective immediate parabolic basin has a critical point over `B`

Shishikura, *The Hausdorff dimension of the boundary of the Mandelbrot set* (arXiv math/9201282),
Lemma 5.2 (`q = 1` case), first half.

Let `f` be a parabolic germ (`Work.FatouCoord.ParabolicBounds`), holomorphic on an open set `D`,
and let `B` be an immediate basin of the parabolic point `0` (`MandelDim.IsImmediateBasin f D B`).
If `B` is simply connected and `f` is *not* injective on `B`, then `f` has a critical point whose
value lies in `B`: there is `z ∈ D` with `f z ∈ B` and `deriv f z = 0`.

The argument is topological.  Since `B ⊆ ParabolicBasin f D ⊆ D`, the map `f` is holomorphic on a
neighbourhood of `B`, and `IsImmediateBasin` gives that `f|_B : B → B` is proper and maps `B` into
itself.  If `deriv f` did not vanish on `B`, then `f|_B` would be a local homeomorphism, hence (being
proper) a covering map, and a covering self-map of a path connected, simply connected space is
injective — contradiction.  So some `c ∈ B` is critical, and then `f c ∈ B` by forward invariance
and `c ∈ B ⊆ D`.

The covering self-map argument is pure topology and is proved here as
`injective_of_isCoveringMap_self`.  The two steps that turn `f|_B` into a covering map are the
analytic lemma `localBiholo_source_subset` (a nonzero derivative gives a local biholomorphism with
source inside `B`) and the topological lemmas `isLocalHomeomorphOn_subtypeMap` (this makes the
subtype self-map a local homeomorphism) and `isCoveringMap_subtypeMap` (proper + local
homeomorphism implies covering).
-/

namespace Work.Horn

open Set Metric Filter Topology
open MandelDim

noncomputable section

set_option linter.unusedVariables false

/-- Every point of the parabolic basin of `0` lies in the domain `D`: the defining neighbourhood
`U ∈ 𝓝 z` is mapped into `D` by `f^[0] = id`. -/
lemma parabolicBasin_subset_D {f : ℂ → ℂ} {D : Set ℂ} : MandelDim.ParabolicBasin f D ⊆ D := by
  intro z hz
  obtain ⟨U, hU, hUD, -⟩ := hz
  have hzU : z ∈ U := mem_of_mem_nhds hU
  have := hUD 0 hzU
  simpa using this

/-- A covering self-map of a path connected, simply connected space is injective.

Indeed, if `u v` lie in a common fibre of `p` and `γ : u → v` is a path, the projected path
`p ∘ γ` is a loop at `p v`; since the base is simply connected its homotopy class is that of the
constant loop, so the monodromy of `p ∘ γ` is the identity, and the image of `u` under it is `v`. -/
theorem injective_of_isCoveringMap_self {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    [SimplyConnectedSpace X] {p : X → X} (hcov : IsCoveringMap p) : Function.Injective p := by
  intro u v huv
  have : Subsingleton (Path.Homotopic.Quotient (p u) (p v)) := inferInstance
  have hgoal : hcov.monodromy (Path.Homotopic.Quotient.refl (p v))
      (⟨u, huv⟩ : p ⁻¹' {p v}) = ⟨v, rfl⟩ := by
    refine hcov.monodromy_eq_of_map_eq (γ := Path.Homotopic.Quotient.refl (p v))
      (Γ := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath u v)) ?_
    exact Subsingleton.elim _ _
  rw [hcov.monodromy_refl] at hgoal
  exact Subtype.ext_iff.mp hgoal

theorem immediateBasin_has_critval {f : ℂ → ℂ} {D : Set ℂ} {h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hD : IsOpen D) (hr : Metric.ball 0 r ⊆ D)
    (hfD : DifferentiableOn ℂ f D)
    (B : Set ℂ) (hB : MandelDim.IsImmediateBasin f D B) (hBne : B.Nonempty)
    (hsc : SimplyConnectedSpace B) (hnotinj : ¬ Set.InjOn f B) :
    ∃ z : ℂ, z ∈ D ∧ f z ∈ B ∧ deriv f z = 0 := by
  obtain ⟨hBopen, hBconn, hBsub, hmax, hmap, hsurj, hprop⟩ := hB
  have hBD : B ⊆ D := fun z hz => parabolicBasin_subset_D (hBsub hz)
  -- Assume that no critical value of `f` lies in `B`.
  by_contra hcon
  have hcrit : ∀ z, z ∈ D → f z ∈ B → deriv f z ≠ 0 := by
    intro z hzD hzB hz0
    exact hcon ⟨z, hzD, hzB, hz0⟩
  -- Then `f` is a local biholomorphism at every point of `B` (`D` is open, `B ⊆ D`).
  have hfold : ∀ c ∈ B, ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e.source ⊆ B ∧
      (⇑e : ℂ → ℂ) = f :=
    fun c hc => localBiholo_source_subset hD hBopen hBD hfD hc (hcrit c (hBD hc) (hmap hc))
  -- Hence `f|_B` is a local homeomorphism, and being proper it is a covering map.
  have hlo := isLocalHomeomorphOn_subtypeMap hBopen hmap hfold
  have hcov := isCoveringMap_subtypeMap hBopen hmap hprop hlo
  -- A covering self-map of a simply connected, path connected space is injective, and `B` is
  -- both (it is open and connected in `ℂ`).
  haveI : SimplyConnectedSpace B := hsc
  haveI : PathConnectedSpace B :=
    isPathConnected_iff_pathConnectedSpace.mp ((hBopen.isConnected_iff_isPathConnected).mp hBconn)
  have hinj : Function.Injective (fun x : B => (⟨f x.1, hmap x.2⟩ : B)) :=
    injective_of_isCoveringMap_self hcov
  -- Contradiction with the assumption that `f` is not injective on `B`.
  apply hnotinj
  intro u hu v hv huv
  have h1 : (fun x : B => (⟨f x.1, hmap x.2⟩ : B)) ⟨u, hu⟩ =
      (fun x : B => (⟨f x.1, hmap x.2⟩ : B)) ⟨v, hv⟩ := Subtype.ext huv
  have h2 : (⟨u, hu⟩ : B) = ⟨v, hv⟩ := hinj h1
  exact congrArg (fun w : B => (w : ℂ)) h2

end

end Work.Horn
