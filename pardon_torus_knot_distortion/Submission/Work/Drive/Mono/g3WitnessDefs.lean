import Mathlib
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Mono.Band.HeightGoodDefs
import Submission.Work.Drive.Mono.geom3Extra

/-!
# The witness bundle of the single-level `Geom3Data` producer

`Work.Drive.Mono.WitnessData3` is the conclusion of the witness
`Work.Drive.Mono.geom3_witnessData` (`Submission/Work/Drive/Mono/geom3_witnessData.lean`) with the
existentials pulled out as explicit parameters, so that it can serve as the *interface* between

* its `Q`-provenance version `Work.Drive.Mono.geom3_witnessData_Q` (the same witness, but drawing its
  tilt direction `V` from a prescribed countable family of height directions, which is what makes the
  one-event slice nullity of `Work.Drive.Mono.G3OneEv` applicable to the datum), and
* the assembly `Work.Drive.Mono.g3_geom3Data_of_witness` (which turns the witness data plus
  `Work.Drive.Mono.G3Pointwise` into `Work.Drive.Mono.Geom3Data`).

Nothing here is proved; the bundle is a verbatim copy of the conclusion of
`Work.Drive.Mono.geom3_witnessData`, whose clauses the two consumers share.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped RealInnerProductSpace

noncomputable section

/-- **The witness bundle `WitnessData3`**: a tilt direction `V` off the coordinate axes, close to the
flat direction `shiftVσ σ 1`, a kernel direction `n` with `V ⊥ n` and `HeightGood ψ n`, an adapted
orthonormal basis `(a₀, b₀)` of `V^⊥`, the half-width window `(A, B)`, the trace arcs `γ : Fin N → ℝ
→ R3` of the box sphere at the level `u` near the slab with their branch/cover/genericity clauses and
the height parameter `η`, and the flat margins `δg` (no-grazing) and `mE` (vertical edges) which the
window has to respect. -/
def WitnessData3 (ψ : Submission.Diffeo) (K : Knot) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (V n a₀ b₀ : R3) (ρ A B : ℝ) (N : ℕ) (γ : Fin N → ℝ → R3) (η m δg mE : ℝ) : Prop :=
  ‖V‖ = 1 ∧
  (∀ (i : Fin 3) (a : ℝ), EuclideanSpace.single (σ i) (1 : ℝ) ≠ a • V) ∧
  ‖V - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8 ∧
  ‖n‖ = 1 ∧ inner ℝ V n = 0 ∧ Work.Drive.Mono.Band.HeightGood ψ n ∧
  ‖a₀‖ = 1 ∧ ‖b₀‖ = 1 ∧ inner ℝ a₀ b₀ = 0 ∧ inner ℝ V a₀ = 0 ∧ inner ℝ V b₀ = 0 ∧
  n = (Real.sqrt 2)⁻¹ • (a₀ + b₀) ∧
  0 < ρ ∧ 0 < A ∧ A < B ∧
  A = ‖V - Work.BoxShrink.shiftVσ σ 1‖ * (5 / 2 * s) ∧
  B ≤ Work.Drive.Mono.boxWidth s σ V - |u| ∧
  B ≤ δg ∧ B ≤ mE / 2 ∧ B ≤ (Submission.boxSide 2 * s - |u|) / 2 ∧
  (∀ h ∈ Set.Ioo A B, ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
    h ≤ |Work.Drive.Final.slabFn c u V (K.curve t)|) ∧
  (∀ h ∈ Set.Ioo A B, ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
    deriv (fun r : ℝ => inner ℝ V (K.curve r)) t = 0 →
    h ≤ |Work.Drive.Final.slabFn c u V (K.curve t)|) ∧
  (∀ h ∈ Set.Ioo A B, ∀ nn : R3, ‖nn‖ = 1 → ‖nn - n‖ < ρ → ∀ t : ℝ,
    K.curve t ∈ Submission.PBox s c σ →
    |Work.Drive.Final.slabFn c u V (K.curve t)| ≤ h →
    deriv (fun r : ℝ => inner ℝ nn (K.curve r)) t ≠ 0) ∧
  (∀ h ∈ Set.Ioo A B, ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
    |Work.Drive.Final.slabFn c u V (K.curve t)| = h →
    deriv (fun r : ℝ => inner ℝ V (K.curve r)) t ≠ 0) ∧
  0 < η ∧ 0 < m ∧ B ≤ m / 2 ∧
  (∀ k, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η)) ∧
  (∀ k, ∀ t ∈ Set.Icc (-η) η, (γ k t) (σ 2) = c (σ 2) + u + t) ∧
  (∀ k, ∃ i : Fin 3, i ≠ 2 ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ β : ℝ → ℝ × ℝ,
    ContDiffOn ℝ 3 β (Set.Icc (-η) η) ∧ ∀ t ∈ Set.Icc (-η) η,
      Work.BoxShrink.Pinch.par ψ (β t) = γ k t ∧
      (γ k t) (σ i) = c (σ i) + ε * Submission.boxSide i * s) ∧
  (∀ h ∈ Set.Ioo A B, ∀ z : R3,
    z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
    |Work.Drive.Final.slabFn c u V z| ≤ h →
    (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
      ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
         |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
    ∃ k, ∃ t ∈ Set.Ioo (-η) η, z = γ k t ∧ |t| ≤ 2 * h) ∧
  (∀ h ∈ Set.Ioo A B, ∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
    ∀ nn : R3, ‖nn‖ = 1 → ‖nn - n‖ < ρ →
    inner ℝ nn (deriv (γ k) t) ≠ 0) ∧
  (∀ h ∈ Set.Ioo A B, ∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
    (1 / 2 : ℝ) ≤ inner ℝ V (deriv (γ k) t)) ∧
  (∃ ε₀ : ℝ, 0 < ε₀ ∧
    (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u V (K.curve t) - ((K.curve t) (σ 2) - (c (σ 2) + u))| < ε₀) ∧
    (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 →
      ε₀ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)|) ∧
    (∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
      ε₀ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)|) ∧
    (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |(K.curve t) (σ 2) - (c (σ 2) + u)| < ε₀ →
      deriv (fun r : ℝ => inner ℝ V (K.curve r)) t ≠ 0))

end

end Work.Drive.Mono
