import Mathlib
import Submission.Work.Drive.N2.roundConfigPicture

/-!
# Phase patches of an embedded circle in a surface

This file sets up the vocabulary for extending a smooth family of functions on the embedded
circle `γ : ℝ → M` (`M` a surface) to a neighbourhood of the circle: a *phase patch* is an open
set `U` of `M` together with a smooth function `φ` on `U` whose value at any point `γ t` of `U`
is `t` up to an integer (the period of `γ` being `1`).

The main content — the existence of phase patches, from the inverse function theorem applied to
the coordinate representation of the immersion `γ` — lives in the companion files; here we record
the vocabulary and the elementary "unwinding" lemma.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

variable {M : Type*} [TopologicalSpace M]

/-- **Unwinding a periodic curve which is injective on `[0,1)`.**  If `γ` has period `1` and is
injective on `Ico 0 1`, then two parameters with the same image differ by an integer. -/
theorem eq_add_int_of_eq_of_periodic {γ : ℝ → M} (hper : Function.Periodic γ 1)
    (hinj : Set.InjOn γ (Set.Ico 0 1)) {x y : ℝ} (h : γ x = γ y) :
    ∃ k : ℤ, x = y + k := by
  have hx : γ (Int.fract x) = γ x := by
    have h1 := (hper.zsmul ⌊x⌋ (Int.fract x)).symm
    simp only [zsmul_one] at h1
    rw [Int.fract_add_floor] at h1
    exact h1
  have hy : γ (Int.fract y) = γ y := by
    have h1 := (hper.zsmul ⌊y⌋ (Int.fract y)).symm
    simp only [zsmul_one] at h1
    rw [Int.fract_add_floor] at h1
    exact h1
  have hxy : Int.fract x = Int.fract y :=
    hinj ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩ ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩
      (by rw [hx, hy, h])
  refine ⟨⌊x⌋ - ⌊y⌋, ?_⟩
  have h1 := Int.fract_add_floor x
  have h2 := Int.fract_add_floor y
  push_cast
  linarith

variable [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- **A finite family of phase patches covering the circle.** -/
structure CirclePhaseCover (γ : ℝ → M) (ι : Type*) [Fintype ι] where
  /-- the open sets of the cover -/
  U : ι → Set M
  /-- the phase functions -/
  φ : ι → M → ℝ
  isOpen_U : ∀ i, IsOpen (U i)
  contMDiff_φ : ∀ i, ContMDiffOn (𝓡 2) (𝓘(ℝ,ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) (φ i) (U i)
  cover : Set.range γ ⊆ ⋃ i, U i
  phase : ∀ i, ∀ y ∈ U i, ∀ t : ℝ, γ t = y → ∃ k : ℤ, φ i y = t + k

end Work.Drive.N2C
