import ChallengeDeps
import Submission.Work.BoseBoxFock.PB3Rhs
import Submission.Work.BoseBoxFock.pb3_b3SlotSum_re_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **Block III, first half** (the `Q₂`-row slot sum against the condensate mass word): the
constant-weight `K1exp` frame sum of the box state, summed over the distinct-index pairs of slots,
is bounded by the `n₀`-mass word.

The proof is the chain

* `pb3_b3SlotSum_re_eq` — expand `b3SlotSum` into the per-pair, per-label `pinQ` double sum
  (`K1exp v μ N 1 = Σ_k pinQ_k ⊗ conj pinQ_k`, `K1exp_one_eq`);
* `pb3_pairBound` — Bessel in the label plus the `χ²`-mass identity `pb3_mass_ident`, the
  commutation `aQC_aPC_comm` and the square identity `pb3_weighted_sq`, giving the `(i,j)`-term of
  the mass word;
* `pb3_pairSet_eq_n0MassWord` — the `pairSet`-sum of those terms is the whole `n0MassWord`, the
  diagonal `i = j` vanishing by `pb3_aP_aQ_self`. -/
theorem PB3FirstHalf {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))} (N : ℕ) :
    (Work.BoseBoxFock.b3SlotSum (Work.BoseBoxFock.ellH v μ)
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
        (Work.BoseBoxFock.K1exp v μ N (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)))).re
      ≤ Work.BoseBoxFock.n0MassWord (Work.BoseBoxFock.ellH v μ)
          (Φ : Submission.BoseGases.X n → ℝ) := by
  rw [pb3_b3SlotSum_re_eq (n := n) (N := N) (v := v) (μ := μ) (Φ := Φ)]
  refine le_trans (Finset.sum_le_sum (fun p hp => ?_))
    (le_of_eq (pb3_pairSet_eq_n0MassWord (n := n) (v := v) (μ := μ) (Φ := Φ)))
  exact pb3_pairBound (N := N) (v := v) (μ := μ) p.1 p.2
    (by simpa [Submission.BoseGases.pairSet] using hp)

end

end Work.BoseBoxFock
