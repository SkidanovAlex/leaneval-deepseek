import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.immediateBasin_has_critval

/-!
# A non-injective immediate basin has a critical value inside the basin (no germ hypotheses)

Same topological argument as `Work.Horn.immediateBasin_has_critval`, but the statement carries only
the hypotheses actually used: `D` open, `f` holomorphic on `D`, `B` an immediate basin of `f`
w.r.t. `D` (`MandelDim.IsImmediateBasin`), `B` simply connected, and `f` not injective on `B`.

`B ⊆ ParabolicBasin f D ⊆ D` follows from the definition of `IsImmediateBasin` alone, so no
`ParabolicBounds`/ball hypothesis is needed.  If `deriv f` did not vanish at any point mapping into
`B`, then `f|_B : B → B` would be a proper local homeomorphism, hence a covering self-map of a path
connected, simply connected space, hence injective — contradiction.
-/

namespace Work.Horn

open Set Metric Filter Topology
open MandelDim

noncomputable section

set_option linter.unusedVariables false

theorem immediateBasin_has_critval_free {f : ℂ → ℂ} {D B : Set ℂ}
    (hD : IsOpen D) (hfD : DifferentiableOn ℂ f D)
    (hB : MandelDim.IsImmediateBasin f D B) (hsc : SimplyConnectedSpace B)
    (hnotinj : ¬ Set.InjOn f B) :
    ∃ z : ℂ, z ∈ D ∧ f z ∈ B ∧ deriv f z = 0 := by
  obtain ⟨hBopen, hBconn, hBsub, hmax, hmap, hsurj, hprop⟩ := hB
  have hBD : B ⊆ D := fun z hz => parabolicBasin_subset_D (hBsub hz)
  -- Assume no critical value of `f` lies in `B`.
  by_contra hcon
  have hcrit : ∀ z, z ∈ D → f z ∈ B → deriv f z ≠ 0 := by
    intro z hzD hzB hz0
    exact hcon ⟨z, hzD, hzB, hz0⟩
  -- `f` is then a local biholomorphism at every point of `B`.
  have hfold : ∀ c ∈ B, ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e.source ⊆ B ∧
      (⇑e : ℂ → ℂ) = f :=
    fun c hc => localBiholo_source_subset hD hBopen hBD hfD hc (hcrit c (hBD hc) (hmap hc))
  -- Hence `f|_B` is a local homeomorphism, and being proper it is a covering map.
  have hlo := isLocalHomeomorphOn_subtypeMap hBopen hmap hfold
  have hcov := isCoveringMap_subtypeMap hBopen hmap hprop hlo
  -- A covering self-map of a path connected, simply connected space is injective.
  haveI : SimplyConnectedSpace B := hsc
  haveI : PathConnectedSpace B :=
    isPathConnected_iff_pathConnectedSpace.mp ((hBopen.isConnected_iff_isPathConnected).mp hBconn)
  have hinj : Function.Injective (fun x : B => (⟨f x.1, hmap x.2⟩ : B)) :=
    injective_of_isCoveringMap_self hcov
  -- Contradiction with non-injectivity of `f` on `B`.
  apply hnotinj
  intro u hu v hv huv
  have h1 : (fun x : B => (⟨f x.1, hmap x.2⟩ : B)) ⟨u, hu⟩ =
      (fun x : B => (⟨f x.1, hmap x.2⟩ : B)) ⟨v, hv⟩ := Subtype.ext huv
  have h2 : (⟨u, hu⟩ : B) = ⟨v, hv⟩ := hinj h1
  exact congrArg (fun w : B => (w : ℂ)) h2

end

end Work.Horn
