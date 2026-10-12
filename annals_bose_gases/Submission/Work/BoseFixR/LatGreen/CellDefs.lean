import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.ChiR0Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.CellDefs` — periodisation and the finite lattice cosine kernel

The two definitions entering the **cell-Parseval identity** (F2) of
`FINDING_farLatRow_sharp.md` §4/§7: the `ℓ`-periodisation `P` of a charge `W`, and the finite
cosine kernel `K_S` of a set `S` of `Lab N` modes.

The identity to be proved about them (delegated) is

  `Σ_{k∈S} Ŵ(q_k)²/‖q_k‖² = ∬_{cell ℓ × cell ℓ} P(x)P(y) · (1/2)(K_S(x+y) + K_S(x−y))`,

`q_k = kmomLab ℓ N k`, which is finite-sum bookkeeping: the Fourier-coefficient identity
`Ŵ(q_k) = ∫_{cell ℓ} P(x) cos⟨q_k,x⟩ dx` (the phase `⟨q_k, ℓn⟩ = 2π(k·n)` drops out), Fubini for
the finite sum over `S`, and the product-to-sum formula `cos a cos b = (cos(a+b)+cos(a−b))/2`.
-/

noncomputable section

open scoped Real BigOperators RealInnerProductSpace
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

/-- The `ℓ`-periodisation of a charge `W`: `P(x) = Σ_{n∈ℤ³} W(x − ℓ n)`. -/
noncomputable def period (W : EuclideanSpace ℝ (Fin 3) → ℝ) (ℓ : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑' n : Fin 3 → ℤ, W (x - Work.BoseFixR.lat ℓ n)

/-- The finite cosine kernel of the mode set `S`: `K_S(z) = Σ_{k∈S} cos⟨q_k,z⟩/‖q_k‖²`. -/
noncomputable def cosKer (ℓ : ℝ) (N : ℕ) (S : Finset (Work.BoseBoxFock.Lab N))
    (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ k ∈ S, Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z)
    / ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2

end Work.BoseFixR.LatGreen
