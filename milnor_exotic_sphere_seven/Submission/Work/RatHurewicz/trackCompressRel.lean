import Mathlib
import Submission.Work.RatHurewicz.trackSetup
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.isHurewiczFibration_trackMap
import Submission.Work.StemsB.exists_lift_rel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.RatHurewicz

open scoped Topology unitInterval

/-- The compression property of the pair `(Track inc, trackFibre inc (inc x₀))` in dimensions where the range model `Z` has vanishing `π`: for `d ≤ 2k-1` with `d ≠ k`, every map of pairs `(I^d, ∂I^d) → (Track inc, trackFibre inc (inc x₀))` is homotopic, relative to the boundary, into the fibre. -/
theorem trackCompressRel {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) (x₀ : X) (k d : ℕ)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (2 * k - 1) (inc x₀))
    (hd : d ≤ 2 * k - 1) (hdk : d ≠ k) :
    Work.RatHurewicz.CompressRel (Work.RatHurewicz.Track inc)
      (Work.RatHurewicz.trackFibre inc (inc x₀)) d := by
  -- The track fibration `trackMap inc : Track inc → Z` has the fibre `trackFibre inc (inc x₀)`,
  -- so a map of pairs `(I^d, ∂I^d) → (Track inc, trackFibre inc (inc x₀))` composes with
  -- `trackMap inc` to a *based* map `(I^d, ∂I^d) → (Z, inc x₀)`.  The range model hypothesis
  -- `IsRangeKModel k (2k-1) (inc x₀)` together with `d ≤ 2k-1`, `d ≠ k` makes that based map
  -- null-homotopic relative to `∂I^d`; the relative homotopy lifting property of the (Serre)
  -- fibration `trackMap inc` then lifts the null-homotopy to the required homotopy of `f` into
  -- the fibre, relative to `∂I^d`.
  intro f hf
  -- the composite is a `d`-cube loop in `Z` based at `inc x₀`
  have hsub : Subsingleton (HomotopyGroup (Fin d) Z (inc x₀)) := hmodel d hd hdk
  have hbdry : ∀ y ∈ Cube.boundary (Fin d), (trackMap inc).comp f y = inc x₀ :=
    fun y hy => hf y hy
  let g : GenLoop (Fin d) Z (inc x₀) := ⟨(trackMap inc).comp f, hbdry⟩
  -- it is null-homotopic relative to the boundary
  have hhom : GenLoop.Homotopic g (GenLoop.const (N := Fin d) (X := Z) (x := inc x₀)) :=
    Quotient.exact (@Subsingleton.elim (HomotopyGroup (Fin d) Z (inc x₀)) hsub
      ⟦g⟧ ⟦(GenLoop.const (N := Fin d) (X := Z) (x := inc x₀))⟧)
  obtain ⟨F0⟩ := hhom
  -- the null-homotopy, in the argument order of the relative HLP
  let H : C((Fin d → I) × I, Z) :=
    ⟨fun p => F0 (p.2, p.1), ContinuousMap.HomotopyWith.continuous F0 |>.comp (by fun_prop)⟩
  have hH0 : ∀ x : Fin d → I, H (x, 0) = trackMap inc (f x) := by
    intro x
    show F0 (0, x) = trackMap inc (f x)
    rw [ContinuousMap.HomotopyWith.apply_zero]
    rfl
  have hH1 : ∀ x : Fin d → I, H (x, 1) = inc x₀ := by
    intro x
    show F0 (1, x) = inc x₀
    rw [ContinuousMap.HomotopyWith.apply_one]
    rfl
  have hHbd : ∀ (x : Fin d → I) (t : I), x ∈ Cube.boundary (Fin d) → H (x, t) = inc x₀ := by
    intro x t hx
    show F0 (t, x) = inc x₀
    rw [ContinuousMap.HomotopyRel.eq_fst F0 t hx]
    exact hbdry x hx
  -- the relative homotopy lifting property of the track fibration
  have hserre : Work.StemsB.IsSerreFibration (trackMap inc) :=
    (isHurewiczFibration_trackMap inc).isSerreFibration
  have hfp : (trackMap inc).comp f = H.comp (Work.StemsB.zeroIncl d) := by
    ext y
    exact (hH0 y).symm
  let gl : C(Work.StemsB.CubeBdry d × I, Track inc) :=
    f.comp ⟨fun p => p.1.1, by fun_prop⟩
  have hgl : (trackMap inc).comp gl = H.comp (Work.StemsB.bdryIncl d) := by
    ext p
    obtain ⟨⟨x, hx⟩, t⟩ := p
    show trackMap inc (f x) = H (x, t)
    rw [hHbd x t hx]
    exact hbdry x hx
  have hgl0 : ∀ x : Work.StemsB.CubeBdry d, gl (x, 0) = f x.1 := fun x => rfl
  obtain ⟨G, hGp, hG0, hGbd⟩ :=
    Work.StemsB.exists_lift_rel (trackMap inc) hserre d H f hfp gl hgl hgl0
  -- `G` covers `H`, hence ends in the fibre, and it is constant on `∂I^d × I`
  refine ⟨G, hG0, ?_, ?_⟩
  · intro x hx t
    exact hGbd ⟨x, hx⟩ t
  · intro x
    have h1 := ContinuousMap.congr_fun hGp (x, 1)
    rw [ContinuousMap.comp_apply] at h1
    show trackMap inc (G (x, 1)) = inc x₀
    rw [h1, hH1 x]

end Work.RatHurewicz
