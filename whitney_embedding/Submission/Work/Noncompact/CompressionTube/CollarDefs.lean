import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# Collar pieces

This file sets up the notion of a *collar piece* used in the construction of a two-sided collar
along a properly embedded line `γ : ℝ → M`.  A collar piece is a smooth map
`Ψ : ℝ^{n-1} × ℝ → M` which, on a slab `{‖u‖ < δ} × J` of the parameter space, has the level sets
of a fixed height function `g : M → ℝ` (with `g ∘ γ = id`) as its second coordinate, has core `γ`,
and is injective and immersive in the transverse direction.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function Metric

noncomputable section

/-- The parameter space of a collar: transverse coordinate times the parameter of the core. -/
abbrev CollarParam (n : ℕ) := EuclideanSpace ℝ (Fin (n - 1)) × ℝ

/-- The slab `{‖u‖ < δ} × J` of the parameter space. -/
def slab (n : ℕ) (δ : ℝ) (J : Set ℝ) : Set (CollarParam n) := {p | ‖p.1‖ < δ ∧ p.2 ∈ J}

theorem isOpen_slab (n : ℕ) {δ : ℝ} {J : Set ℝ} (hJ : IsOpen J) : IsOpen (slab n δ J) := by
  unfold slab
  exact (isOpen_lt continuous_fst.norm continuous_const).inter (hJ.preimage continuous_snd)

/-- A **collar piece** for a height function `g` and a curve `γ`. -/
structure CollarPiece (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] (g : M → ℝ) (γ : ℝ → M) where
  /-- the underlying map -/
  Ψ : CollarParam n → M
  /-- the parameter interval on which the piece is a collar -/
  J : Set ℝ
  J_open : IsOpen J
  /-- the transverse radius of the collar -/
  δ : ℝ
  δ_pos : 0 < δ
  smooth : ContMDiffOn (MCprod n) (MC n) smoothOrder Ψ (slab n δ J)
  level : ∀ p : CollarParam n, ‖p.1‖ < δ → p.2 ∈ J → g (Ψ p) = p.2
  core : ∀ s : ℝ, s ∈ J → Ψ ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) = γ s
  injOn : ∀ s : ℝ, s ∈ J →
    Set.InjOn (fun u : EuclideanSpace ℝ (Fin (n - 1)) => Ψ (u, s)) (ball 0 δ)
  immersion : ∀ p : CollarParam n, ‖p.1‖ < δ → p.2 ∈ J →
    Function.Injective (mfderiv (MCprod n) (MC n) Ψ p)

end

end Work.Noncompact.CompressionTube
