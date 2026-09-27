import Mathlib

/-!
# A smooth positive minorant of a continuous positive function

Given a continuous positive function `φ : ℝ → ℝ`, there is a smooth positive function `R`
with `R ≤ φ` pointwise.

The construction is the standard one: the sets `t y = Ioo 0 (φ y)` are convex, and around every
point `x` the constant `φ x / 2` lies in `t y` for all `y` close to `x` (by continuity of `φ` and
positivity at `x`).  Mathlib's `exists_contMDiffMap_forall_mem_convex_of_local_const` (which
builds a global smooth function by patching local data with a smooth partition of unity) then
produces a smooth `R` with `R y ∈ Ioo 0 (φ y)` for all `y`.
-/

open Filter
open scoped Topology Manifold ContDiff

namespace Work.Noncompact.CompressionTube

/-- A continuous positive function on `ℝ` admits a smooth positive minorant. -/
theorem smooth_minorant {φ : ℝ → ℝ} (hcont : Continuous φ) (hpos : ∀ s, 0 < φ s) :
    ∃ R : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R ∧ (∀ s, 0 < R s) ∧ ∀ s, R s ≤ φ s := by
  -- Around each point, the constant `φ x / 2` is a local smooth (`C^∞`) witness for the convex
  -- sets `Ioo 0 (φ ·)`.
  have hloc : ∀ x : ℝ, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, c ∈ Set.Ioo (0 : ℝ) (φ y) := fun x => by
    refine ⟨φ x / 2, ?_⟩
    filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds
      (show φ x / 2 < φ x by linarith [hpos x])] with y hy
    exact ⟨by linarith [hpos x], hy⟩
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (F := ℝ) (n := (⊤ : ℕ∞)) (t := fun y => Set.Ioo (0 : ℝ) (φ y))
    (fun y => convex_Ioo 0 (φ y)) hloc
  exact ⟨fun s => g s, by
      have h := g.contMDiff
      rw [contMDiff_iff_contDiff] at h
      simpa using h,
    fun s => (hg s).1, fun s => (hg s).2.le⟩

end Work.Noncompact.CompressionTube
