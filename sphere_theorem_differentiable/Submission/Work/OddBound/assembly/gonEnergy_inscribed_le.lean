import Mathlib
import Submission.Work.OddBound.AssemblyKit
import Submission.Work.OddBound.indexTransfer.gonEnergy_le_integral_curveSpeed_sq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.assembly

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

/-- **The inscribed polygon of a unit-speed closed curve has energy at most `L²/2`.**

Let `γ : ℝ → M` be a closed (`γ L = γ 0`) curve of class `C^∞` whose speed on `[0, L]` is
constantly `1`, and let `N ≥ 2`.  The `N`-gon inscribed in `γ` at the equally spaced times
`0, L/N, …, N·L/N = L` has energy

`gonEnergy (γ 0) (γ (L/N), …, γ ((N-1)·L/N)) ≤ L²/2`.

This is the sharp value: for the unit-speed parametrisation of `γ` each side is *traversed in time*
`L/N`, hence has length at most `L/N`, and summing `(N/2)·Σ (L/N)²` gives `(N/2)·N·(L/N)² = L²/2`.

The proof is a direct instantiation of the general energy bound
`gonEnergy_le_integral_curveSpeed_sq` (distance ≤ length per side, then Cauchy–Schwarz, then
telescoping the partition integrals) combined with the vanishing of `∫₀^L ‖γ'‖² = ∫₀^L 1 = L`. -/
theorem gonEnergy_inscribed_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {N : ℕ} (hN : 2 ≤ N) {L : ℝ} (hL : 0 < L) {γ : ℝ → M}
    (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) L, Submission.Length.curveSpeed (I := I) γ t = 1)
    (hcl : γ L = γ 0) :
    Work.OddBound.gonEnergy (I := I) (γ 0) (fun i : Fin (N - 1) => γ (L * ((i : ℕ) + 1) / N))
      ≤ L ^ 2 / 2 := by
  have hNpos : 0 < N := by omega
  -- `γ` is in particular `C¹` on `[0, L]`.
  have hγ1 : ContMDiff 𝓘(ℝ) I 1 γ := by
    refine hγsm.of_le ?_
    exact_mod_cast le_top
  have hγOn : ContMDiffOn 𝓘(ℝ) I 1 γ (Set.Icc (0 : ℝ) L) := hγ1.contMDiffOn
  -- The general energy bound for the inscribed polygon of a closed `C¹` curve.
  have hkey := Work.OddBound.indexTransfer.gonEnergy_le_integral_curveSpeed_sq
    (I := I) (Φ := γ) (T := L) hL (p := γ 0) rfl hcl hγOn hNpos
  -- The vertex list of the gon is the sampled list of the lemma.
  have hverts : (fun i : Fin (N - 1) => γ (L * ((i : ℕ) + 1) / N))
      = (fun i : Fin (N - 1) => γ ((((i : ℕ) : ℝ) + 1) * L / N)) := by
    funext i
    congr 1
    ring
  -- Unit speed on `[0, L]` makes the energy of the loop equal to `L`.
  have hint : ∫ s in (0 : ℝ)..L, (Submission.Length.curveSpeed (I := I) γ s) ^ 2 = L := by
    rw [intervalIntegral.integral_congr (μ := MeasureTheory.volume)
      (f := fun s => (Submission.Length.curveSpeed (I := I) γ s) ^ 2) (g := fun _ => (1 : ℝ))
      (fun s hs => by
        have hs' : s ∈ Set.Icc (0 : ℝ) L := by rwa [Set.uIcc_of_le hL.le] at hs
        show Submission.Length.curveSpeed (I := I) γ s ^ 2 = 1
        rw [hunit s hs', one_pow])]
    rw [intervalIntegral.integral_const]
    simp
  calc Work.OddBound.gonEnergy (I := I) (γ 0) (fun i : Fin (N - 1) => γ (L * ((i : ℕ) + 1) / N))
      = Work.OddBound.gonEnergy (I := I) (γ 0)
          (fun i : Fin (N - 1) => γ ((((i : ℕ) : ℝ) + 1) * L / N)) := by rw [hverts]
    _ ≤ L / 2 * ∫ s in (0 : ℝ)..L, (Submission.Length.curveSpeed (I := I) γ s) ^ 2 := hkey
    _ = L / 2 * L := by rw [hint]
    _ = L ^ 2 / 2 := by ring

end Work.OddBound.assembly
