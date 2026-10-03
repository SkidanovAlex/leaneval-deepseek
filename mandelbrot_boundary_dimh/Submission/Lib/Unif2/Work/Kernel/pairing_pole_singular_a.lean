import Mathlib
import Submission.Lib.Unif2.Work.Kernel.pairing_pole_singular
import Submission.Lib.Unif2.Work.Drive.greenCoverSwap

/-!
# The pole identity at the *second* pole `a` (`a ↔ b` mirror of `pairing_pole_singular`)

`Work.Kernel.pairing_pole_singular` is the pole identity for the test function `χ · gA`, singular at
`a`, integrated against the Green function `gB` with pole at `b`: it returns `2π χ b gA b`.

The lemma here is the mirror image: the test function `χ · gB` is singular at `b`, the integrating
Green function is `gA` with pole at `a`, and the value returned is `2π χ a gB a`.

The proof is the observation of `Submission/Work/Drive/greenCoverSwap.lean`: the two distinguished
charts of a `GreenCover` can be relabelled (`E.swap`), with the *same* chart data, radii, weights and
bumps, and the same pairing (`Work.Kernel.pairing_swap_eq`).  Hence substituting
`(a, b, E, gA, gB) ↦ (b, a, E.swap, gB, gA)` into `pairing_pole_singular` gives the statement below
verbatim.
-/

open scoped Topology
open Set Metric Filter

namespace Work.Kernel

open scoped Manifold Topology in
theorem pairing_pole_singular_a {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (hab : a ≠ b)
    (E : Work.Kernel.GreenCover ι Ω K a b)
    (hKc : IsCompact K) (haK : a ∈ K) (hbK : b ∈ K) (hΩo : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {gA gB : X → ℝ} (hgA : Work.SimplyConnected.ABS.IsGreenOn Ω a gA)
    (hgB : Work.SimplyConnected.ABS.IsGreenOn Ω b gB)
    {H : ℂ → ℝ} {r : ℝ} (hrpos : 0 < r) (hrρ : r ≤ E.ρ E.ia)
    (hpmem : (chartAt ℂ (E.y E.ia)) a ∈
      Metric.ball ((chartAt ℂ (E.y E.ia)) (E.y E.ia)) (E.ρ E.ia))
    (hH : InnerProductSpace.HarmonicOnNhd H (Metric.ball ((chartAt ℂ (E.y E.ia)) a) r))
    (hueq : ∀ z ∈ Metric.ball ((chartAt ℂ (E.y E.ia)) a) r,
      gA ((chartAt ℂ (E.y E.ia)).symm z)
        = -Real.log ‖z - (chartAt ℂ (E.y E.ia)) a‖ + H z)
    (hgAdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) gA (Ω \ ({a, b} : Set X)))
    (hψc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.ψ i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hβc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.β i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    {χ : X → ℝ}
    (hχdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) χ Ω)
    (hχc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (χ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hχK : tsupport χ ⊆ K) (hχΩ : tsupport χ ⊆ Ω) (hχ1 : χ =ᶠ[𝓝 b] 1) :
    Work.Drive.pairing E.y E.ρ E.σ E.ψ gA (fun x : X => χ x * gB x)
      = 2 * Real.pi * (χ a * gB a) := by
  have hba : b ≠ a := fun h => hab h.symm
  -- the differentiability of `gA` away from `{a, b}`, in the order the swapped statement wants
  have hgd : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.swap.y k)) gA (Ω \ ({b, a} : Set X)) := by
    intro k
    have h1 := hgAdiff k
    have h2 : ({b, a} : Set X) = {a, b} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [h2]
    exact h1
  -- `pairing_pole_singular` with `(a, b, E, gA, gB) ↦ (b, a, E.swap, gB, gA)`
  have hmain := Work.Kernel.pairing_pole_singular (X := X) (ι := ι) (Ω := Ω) (K := K)
    (a := b) (b := a) hba E.swap hKc hbK haK hΩo hKΩ hgB hgA hrpos hrρ hpmem hH hueq hgd
    hψc1 hβc1 hχdiff hχc1 hχK hχΩ hχ1
  -- the swapped objects are definitionally the originals
  exact hmain

end Work.Kernel
