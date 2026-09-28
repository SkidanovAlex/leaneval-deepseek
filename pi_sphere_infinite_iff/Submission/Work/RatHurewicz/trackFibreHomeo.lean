import Mathlib
import Submission.Work.RatHurewicz.trackSetup

/-!
# The fibre of the mapping track is the homotopy fibre

`Work.RatHurewicz.trackSetup` introduces the **mapping track** `Track inc` of a map `inc : X → Z`
(the space of pairs `(x, γ)` with `γ` a path in `Z` *ending* at `inc x`) together with the "track
fibration" `trackMap inc : Track inc → Z`, `(x, γ) ↦ γ 0`.

The fibre `trackFibre inc (inc x₀)` is the space of pairs `(x, γ)` with `γ` a path from `inc x₀` to
`inc x`.  This is exactly the homotopy fibre `homotopyFibre inc x₀ = bundlePullback Z (inc x₀) X inc`
of `inc` (the pullback of the path–loop fibration `evalOne Z (inc x₀) : PathSpace Z (inc x₀) → Z`
over `inc`): an element of the homotopy fibre is a pair `(x, γ)` with `γ 0 = inc x₀` (the condition
carried by `PathSpace`) and `γ 1 = inc x` (the condition of the pullback), and an element of the
track fibre is the same pair with the two conditions interchanged — the path itself being the same.
So the two spaces are canonically identified by re-associating the two proofs, and this is a
homeomorphism since it only moves data around inside subtypes of `X × C(I, Z)`.

This file records the homeomorphism (`Work.RatHurewicz.trackFibreHomeo`), that it sends the base
point `homotopyFibreBasepoint inc x₀ = (x₀, const path)` to the track base point `trackBase inc x₀`,
and that it does not move the `X`-coordinate (`e y` projects to `homotopyFibreFst inc x₀ y`).
-/

namespace Work.RatHurewicz

open scoped Topology unitInterval

noncomputable section

variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]

/-- The canonical map from the homotopy fibre of `inc` to the fibre of its mapping track: the pair
`(x, γ)` (with `γ 0 = inc x₀` and `γ 1 = inc x`) is sent to the same pair, read as an element of
`Track inc` — whose defining condition is `γ 1 = inc x` — lying over `inc x₀` (which is `γ 0`). -/
def homotopyFibreToTrackFibre (inc : C(X, Z)) (x₀ : X) :
    homotopyFibre inc x₀ → ↥(trackFibre inc (inc x₀)) :=
  fun p => ⟨⟨(p.1.1, p.1.2.1), p.2⟩, p.1.2.2⟩

/-- The inverse of `homotopyFibreToTrackFibre`: the two proofs attached to `(x, γ)` are swapped
back. -/
def trackFibreToHomotopyFibre (inc : C(X, Z)) (x₀ : X) :
    ↥(trackFibre inc (inc x₀)) → homotopyFibre inc x₀ :=
  fun q => ⟨(q.1.1.1, ⟨q.1.1.2, q.2⟩), q.1.2⟩

@[simp]
theorem trackFibreToHomotopyFibre_homotopyFibreToTrackFibre (inc : C(X, Z)) (x₀ : X)
    (p : homotopyFibre inc x₀) :
    trackFibreToHomotopyFibre inc x₀ (homotopyFibreToTrackFibre inc x₀ p) = p := rfl

@[simp]
theorem homotopyFibreToTrackFibre_trackFibreToHomotopyFibre (inc : C(X, Z)) (x₀ : X)
    (q : ↥(trackFibre inc (inc x₀))) :
    homotopyFibreToTrackFibre inc x₀ (trackFibreToHomotopyFibre inc x₀ q) = q := rfl

/-- **The fibre of the mapping track of `inc` is the homotopy fibre of `inc`.**  The homeomorphism
is the reassociation of the two defining conditions on a pair `(x, γ)`, so it fixes the base point
and the `X`-coordinate. -/
theorem trackFibreHomeo {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (inc : C(X, Z)) (x₀ : X) :
    ∃ e : Work.RatHurewicz.homotopyFibre inc x₀ ≃ₜ ↥(Work.RatHurewicz.trackFibre inc (inc x₀)),
      e (Work.RatHurewicz.homotopyFibreBasepoint inc x₀)
        = ⟨Work.RatHurewicz.trackBase inc x₀, Work.RatHurewicz.trackBase_mem_trackFibre inc x₀⟩ ∧
      (∀ y, (e y).1.1.1 = Work.RatHurewicz.homotopyFibreFst inc x₀ y) := by
  refine ⟨{ toFun := homotopyFibreToTrackFibre inc x₀
            invFun := trackFibreToHomotopyFibre inc x₀
            left_inv := fun p => rfl
            right_inv := fun q => rfl
            continuous_toFun := by unfold homotopyFibreToTrackFibre; fun_prop
            continuous_invFun := by unfold trackFibreToHomotopyFibre; fun_prop }, ?_, ?_⟩
  · rfl
  · intro y
    rfl

end

end Work.RatHurewicz
