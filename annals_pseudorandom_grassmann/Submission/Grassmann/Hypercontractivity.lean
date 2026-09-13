import Submission.Grassmann.PairSum
import Submission.Grassmann.SpectralSSE

/-!
# The conditional hypercontractive inequality and its corollary

This file completes the logical chain from the deep hypercontractive inequality of
arXiv:2209.04243 to the small-set expansion theorem for the shortcode graph:

  `HypHyper` (Theorem 1.5, `thm:Hypercontractivity in the Bilinear scheme`)
    ⟹ `HypCor4` (Corollary `cor:Corollary of hypercontractivity`)
    ⟹ `HypSSE` (Theorem 1.6, `thm:sses`, in `Submission.Grassmann.SpectralSSE`),

and, in parallel, `HypCor4 ⟹ HypBSglob` (Corollary `cor:atmostd`, in
`Submission.Grassmann.HypBSglob`).

`HypHyper` is the paper's Theorem 1.5 in the form in which its proof is used: for a function
`f` of degree at most `d`,

  `‖f‖₄⁴ ≤ q^{100d²} Σ_{V₁ ≤ V, W₁ ≤ W : dim V₁ + codim W₁ ≤ d} E_T ‖D_{V₁,W₁,T}[f]‖₂⁴`,

and each averaged fourth power is bounded by `ε` times the averaged square, where `ε` bounds
all the generalised influences `I_{V₁,W₁,T}[f] = ‖D_{V₁,W₁,T}[f]‖₂²` (the small-influence
hypothesis `SmallInfl d ε f`).  Since `E_T ‖D_{V₁,W₁,T}[f]‖₂² = ‖L_{V₁,W₁}[f]‖₂²`
(`ShiftAverage.sum_inflBS2_eq`), the sum becomes the pair sum `pairSum d f` of
`Submission.Grassmann.PairSum`, and `HypHyper` is stated in that combined form (this is exactly
the displayed chain in the paper's proof of `cor:Corollary of hypercontractivity`, the first
two `≤`'s being Theorem 1.5 and the pointwise influence bound respectively).

The passage from `HypHyper` to `HypCor4` is the *counting step*: `pairSum_le`
(`Submission.Grassmann.PairSum`) says `pairSum d f ≤ q^{10d²}‖f‖₂²` for functions of degree
at most `d`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-- **Theorem 1.5 of arXiv:2209.04243** (`thm:Hypercontractivity in the Bilinear scheme`),
combined with the pointwise small-influence bound and the shift average
`E_T ‖D_{V₁,W₁,T}[f]‖₂² = ‖L_{V₁,W₁}[f]‖₂²`: for a function `f` of degree at most `d` whose
generalised influences of order at most `d` are all at most `ε`,

  `‖f‖₄⁴ ≤ q^{Cd²} · ε · Σ_{V₁,W₁ : dim V₁ + codim W₁ ≤ d} ‖L_{V₁,W₁}[f]‖₂²`. -/
def HypHyper : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (m n : ℕ) (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (ε : ℝ),
    0 ≤ ε → DegLe d f → SmallInfl d ε f →
      l4q f ≤ (2 : ℝ) ^ (C * d ^ 2) * ε * pairSum d f

/-- **The paper's `cor:Corollary of hypercontractivity`**: a function of degree at most `d` with
`(d,ε)`-small generalised influences satisfies `‖f‖₄⁴ ≤ q^{O(d²)} ε ‖f‖₂²`. -/
theorem HypCor4_of_HypHyper (H : HypHyper) : HypCor4 := by
  obtain ⟨C, _hC, h⟩ := H
  refine ⟨C + 10, by omega, ?_⟩
  intro m n d f ε hε hdeg hSI
  calc l4q f ≤ (2 : ℝ) ^ (C * d ^ 2) * ε * pairSum d f := h m n d f ε hε hdeg hSI
    _ ≤ (2 : ℝ) ^ (C * d ^ 2) * ε * ((2 : ℝ) ^ (10 * d ^ 2) * l2sq f) :=
        mul_le_mul_of_nonneg_left (pairSum_le hdeg) (mul_nonneg (by positivity) hε)
    _ = (2 : ℝ) ^ ((C + 10) * d ^ 2) * ε * l2sq f := by
        have hp : (2 : ℝ) ^ (C * d ^ 2) * (2 : ℝ) ^ (10 * d ^ 2) =
            (2 : ℝ) ^ ((C + 10) * d ^ 2) := by
          rw [← pow_add]
          congr 1
          ring
        calc (2 : ℝ) ^ (C * d ^ 2) * ε * ((2 : ℝ) ^ (10 * d ^ 2) * l2sq f)
            = ((2 : ℝ) ^ (C * d ^ 2) * (2 : ℝ) ^ (10 * d ^ 2)) * (ε * l2sq f) := by ring
          _ = (2 : ℝ) ^ ((C + 10) * d ^ 2) * ε * l2sq f := by rw [hp]; ring

/-- The paper's Theorem 1.6 (`thm:sses`, small-set expansion for the shortcode graph) follows
from the deep hypercontractive inequality of Theorem 1.5. -/
theorem HypSSE_of_HypHyper (H : HypHyper) : HypSSE :=
  hypSSE_of_HypCor4 (HypCor4_of_HypHyper H)

end

end Submission.Grassmann
