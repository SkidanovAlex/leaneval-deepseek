/-
# `sivSecondClaim_of_structIiiSecondClaim`  (LEMMA `siv-second` of Krause--Mirek--Tao §5.2)

Corollary `siv-second`: the `ℓ²` bound for the minor-arc part of the second dual function
`(1 - Π_{≤l,≤d(l-Log N)}) Ã_N^{**}(f,h)`, for **arbitrary** `f ∈ ℓ²(ℤ)` and `‖h‖_∞ ≤ 1`, deduced
from Corollary `struct-iii-second` (the same bound under support hypotheses) by means of the
off-diagonal decay `(off-decay)` of the Ionescu--Wainger projections.

The proof is the paper's §5.2 argument, with the partition of `ℤ` into the blocks
`I_i = {x : x / N^d = i}`:

* `SivLocal.lean`, `SivGeom.lean`, `SivL2.lean`, `SivOff.lean` — the block decomposition, the
  local bound `localBoundAll` (from `struct-iii-second`, after translating the window `suppWin`),
  the `ℓ²`-bookkeeping and the definitions of the two remaining inputs;
* `offBlockBd.lean` — the blockwise form `OffBlockBd` of the off-decay, *with the explicit
  exponential gain* `2^{-8 d l}` (block distance `≥ coeffSum P + 3 + 2^{deg P}`);
* `pairingFarBd.lean` — the almost-orthogonality `PairingFarBd` of the minor-arc parts of two
  blocks, by Cauchy--Schwarz blockwise and the kernel estimate `kernel_sum_le`;
* `transOp_blockSum.lean` — linearity of `T = (1-Π)Ã_N^{**}(·,h)` over block sums;
* `tendsto_l2norm_blockRemainder.lean` — exhaustion of `f` by block sums;
* `sqrt_kappa_le.lean` — the arithmetic of the Schur kernel;
* `SivMainCore.lean` — the assembly: Schur's test over the blocks (`schur_finite`,
  `kernel_sum_le`) followed by the limiting argument.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.offBlockBd
import Submission.Work.KMTAreas.A4Z.pairingFarBdSelf
import Submission.Work.KMTAreas.A4Z.transOp_blockSum
import Submission.Work.KMTAreas.A4Z.tendsto_l2norm_blockRemainder
import Submission.Work.KMTAreas.A4Z.sqrt_kappa_le

set_option autoImplicit false

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4Z

theorem sivSecondClaim_of_structIiiSecondClaim (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hOff : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → Work.KMTAreas.A4Z.OffDecayHyp ρ) (h : Work.KMTAreas.A4Z.StructIiiSecondClaim P) : Work.KMTAreas.A4Z.SivSecondClaim P :=
  Work.KMTAreas.A4Z.sivSecondClaim_of_children P hP h
    (fun (ρ : ℝ) (N l : ℕ) {f h : ℤ → ℂ} (hN : 1 ≤ N) (hf : MemLp f 2 Measure.count)
        (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (S : Finset ℤ) =>
      Work.KMTAreas.A4Z.transOp_blockSum P ρ N l hN hf hh S)
    (fun {L : ℤ} (hL : 0 < L) {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) =>
      Work.KMTAreas.A4Z.tendsto_l2norm_blockRemainder hL hf)
    (fun ρ hρ0 hρ1 => Work.KMTAreas.A4Z.offBlockBd P ρ (hOff ρ hρ0 hρ1))
    (fun ρ hρ0 hρ1 Cρ₀ Koff hK0 hBd => Work.KMTAreas.A4Z.pairingFarBdSelf P hP ρ hK0 hBd)
    (fun K Cc hK hC d hd D hD c₀ c hc hc₀ hcc hc1 =>
      Work.KMTAreas.A4Z.sqrt_kappa_le K Cc hK hC d hd D hD c₀ c hc hc₀ hcc hc1)

end Work.KMTAreas.A4Z
