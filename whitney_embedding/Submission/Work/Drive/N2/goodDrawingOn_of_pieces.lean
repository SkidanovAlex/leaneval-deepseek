import Mathlib
import Submission.Work.Drive.N2.GoodDrawingFamily

/-!
# Pasting two good drawings along the frontier of an open set

`Work.Drive.N2.goodDrawing_of_family` pastes good drawings defined on *value bands*: the pieces are
indexed by the value of `f` and each piece is responsible for a band of values.

The construction of the window/large-scale blocks of `Work.Drive.N2.levelSeparatingMap` needs the
other kind of pasting: two candidate drawings of the *same* value band, one used on a set `D` of
points (the model region) and one on its complement (the transported drawing), with the two formulas
glued along `frontier D`.  This file records that pasting, once and for all:

* `goodDrawingOn_of_pieces`: given an open `D`, drawings `gm` (used on `D`) and `gb` (used off `D`),
  each satisfying the three `GoodDrawingOn` rows on its own side of the band `A`, agreeing *to all
  orders* (`=ᶠ[𝓝 x]`) at every interface point `x ∈ frontier D` with `f x ∈ A`, and with no
  cross-collisions across the interface, the hybrid `x ↦ if x ∈ D then gm x else gb x` is a
  `GoodDrawingOn f A`.

The two cross-collision rows are combined into one hypothesis (`hcross`): the same statement applied
to the pair `(y, x)` covers the other order, because the conclusion `gm y ≠ gb x` is the contrapositive
of what the injectivity row needs on the other side.

Nothing here is geometric: it is the *mechanism* by which a "model block pasted to a transported
drawing" is assembled, and the hypotheses `hagree`/`hcross` are exactly the two obligations that the
geometry has to supply at the seam.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Filter Set

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

open Classical in
/-- **Pasting two drawings along the frontier of an open set.**

`gm` is the drawing used on the open set `D`, `gb` the one used off `D`; both satisfy the three
`GoodDrawingOn` rows on their own side of the value band `A` (smoothness, injectivity of the
differential on `ker df`, and injectivity on the `f`-levels inside `A`).  If the two formulas agree
to all orders at every point of the interface `frontier D` at which `f` takes its value in `A`, and
if no point of `D` and point off `D` with the same `f`-value in `A` are drawn to the same point, then
the hybrid is a `GoodDrawingOn f A`. -/
theorem goodDrawingOn_of_pieces (f : M → ℝ) (A : Set ℝ) (D : Set M) (hD : IsOpen D)
    (gm gb : M → EuclideanSpace ℝ (Fin 3))
    (hmsm : ∀ x ∈ D, f x ∈ A → ContMDiffAt (𝓡 2) (𝓡 3) ∞ gm x)
    (hbsm : ∀ x, x ∉ D → f x ∈ A → ContMDiffAt (𝓡 2) (𝓡 3) ∞ gb x)
    (hagree : ∀ x ∈ frontier D, f x ∈ A → gm =ᶠ[𝓝 x] gb)
    (hmimm : ∀ x ∈ D, f x ∈ A → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) gm x v = 0 → v = 0)
    (hbimm : ∀ x, x ∉ D → f x ∈ A → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) gb x v = 0 → v = 0)
    (hminj : ∀ x ∈ D, ∀ y ∈ D, f x ∈ A → f y ∈ A → f x = f y → gm x = gm y → x = y)
    (hbinj : ∀ x, x ∉ D → ∀ y, y ∉ D → f x ∈ A → f y ∈ A → f x = f y → gb x = gb y → x = y)
    (hcross : ∀ x, x ∈ D → ∀ y, y ∉ D → f x ∈ A → f y ∈ A → f x = f y → gm x ≠ gb y) :
    GoodDrawingOn f A (fun x => if x ∈ D then gm x else gb x) := by
  -- the hybrid is eventually `gm` at a point of `D`
  have hGgm : ∀ x ∈ D, (fun x => if x ∈ D then gm x else gb x) =ᶠ[𝓝 x] gm :=
    fun x hx => Filter.eventually_of_mem (hD.mem_nhds hx) fun y hy => if_pos hy
  -- the hybrid is eventually `gb` off `D` on the band: at a frontier point by `hagree`, on the
  -- interior of the complement because that interior is a neighbourhood
  have hGgb : ∀ x, x ∉ D → f x ∈ A → (fun x => if x ∈ D then gm x else gb x) =ᶠ[𝓝 x] gb := by
    intro x hxD hxA
    by_cases hxfr : x ∈ frontier D
    · filter_upwards [hagree x hxfr hxA] with y hy
      by_cases hyD : y ∈ D
      · rw [if_pos hyD]; exact hy
      · rw [if_neg hyD]
    · have hsub : Dᶜ ⊆ interior Dᶜ ∪ frontier D := by
        intro y hy
        have h1 : y ∈ interior Dᶜ ∪ frontier Dᶜ := by
          rw [← closure_eq_interior_union_frontier Dᶜ]
          exact subset_closure hy
        rcases h1 with h | h
        · exact Or.inl h
        · exact Or.inr (by rwa [frontier_compl] at h)
      have hxint : x ∈ interior Dᶜ := by
        rcases hsub hxD with h | h
        · exact h
        · exact absurd h hxfr
      filter_upwards [isOpen_interior.mem_nhds hxint] with y hy
      exact if_neg (interior_subset hy)
  refine ⟨?_, ?_, ?_⟩
  · intro x hxA
    by_cases hxD : x ∈ D
    · exact (hmsm x hxD hxA).congr_of_eventuallyEq (hGgm x hxD)
    · exact (hbsm x hxD hxA).congr_of_eventuallyEq (hGgb x hxD hxA)
  · intro x hxA v hv hGv
    by_cases hxD : x ∈ D
    · have h1 : mfderiv (𝓡 2) (𝓡 3) (fun x => if x ∈ D then gm x else gb x) x
          = mfderiv (𝓡 2) (𝓡 3) gm x := (hGgm x hxD).mfderiv_eq
      rw [h1] at hGv
      exact hmimm x hxD hxA v hv hGv
    · have h1 : mfderiv (𝓡 2) (𝓡 3) (fun x => if x ∈ D then gm x else gb x) x
          = mfderiv (𝓡 2) (𝓡 3) gb x := (hGgb x hxD hxA).mfderiv_eq
      rw [h1] at hGv
      exact hbimm x hxD hxA v hv hGv
  · intro x y hxA hyA hfxy hGxy
    by_cases hxD : x ∈ D
    · by_cases hyD : y ∈ D
      · refine hminj x hxD y hyD hxA hyA hfxy ?_
        simpa only [if_pos hxD, if_pos hyD] using hGxy
      · exact absurd (by simpa only [if_pos hxD, if_neg hyD] using hGxy)
          (hcross x hxD y hyD hxA hyA hfxy)
    · by_cases hyD : y ∈ D
      · have h1 : gm y = gb x := by
          have h2 : gb x = gm y := by simpa only [if_neg hxD, if_pos hyD] using hGxy
          exact h2.symm
        exact absurd h1 (hcross y hyD x hxD hyA hxA hfxy.symm)
      · refine hbinj x hxD y hyD hxA hyA hfxy ?_
        simpa only [if_neg hxD, if_neg hyD] using hGxy

end Work.Drive.N2
