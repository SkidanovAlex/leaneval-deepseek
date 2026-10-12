import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.LatticeParsevalDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatticeParsevalSumSq`

The coordinate/Parseval identity for the box-lattice momentum of a mode label:
for any finite set `K` of labels of the periodic cube `Lab N` and any weight
`a : Lab N → ℝ`, the sum of the *coordinate* squares of `kmomLab ℓ N k`,
weighted by `a k`, equals the sum of the *Euclidean* square norms `‖kmomLab ℓ N k‖²`
weighted by `a k`:

  `∑ᵢ ∑_{k∈K} a k · (kmomLab ℓ N k)ᵢ²  =  ∑_{k∈K} ‖kmomLab ℓ N k‖² · a k`.

The content is the interchange of the two finite sums together with the L² norm
identity `‖x‖² = ∑ᵢ xᵢ²` on `ℝ³ = EuclideanSpace ℝ (Fin 3)`
(`Submission.BoseGases.shell_sq_norm3`).
-/

namespace Work.BoseFixR

theorem LatticeParsevalSumSq {ℓ : ℝ} (N : ℕ) (K : Finset (Work.BoseBoxFock.Lab N))
    (a : Work.BoseBoxFock.Lab N → ℝ) :
    (∑ i : Fin 3, ∑ k ∈ K, a k * ((Work.BoseBoxFock.kmomLab ℓ N k i) ^ 2))
      = ∑ k ∈ K, ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2 * a k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have h : (∑ i : Fin 3, ((Work.BoseBoxFock.kmomLab ℓ N k) i) ^ 2)
      = ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2 :=
    (Submission.BoseGases.shell_sq_norm3 _).symm
  rw [← Finset.mul_sum, h, mul_comm]

end Work.BoseFixR
