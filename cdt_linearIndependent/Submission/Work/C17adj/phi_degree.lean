import Mathlib
import Submission.Work.C17adj.divisor_defs
import Submission.Work.C17adj.phi_defs
import Submission.Work.C17adj.phi_lead_facts
import Submission.Work.C17adj.phi_UZ_facts
import Submission.Work.C17adj.deriv_mul_le
import Submission.Work.C17adj.deriv2_mul_le

/-!
# Degree and leading coefficient of the cleared adjoint numerator `PhiNum`

`PhiNum a b W = D³·(P₂·β'' + A·β' + C·β)` for `β = W/D`, `D = DadjL` (see
`Work.C17adj.divisor_defs`).  Collecting in `W`, `W'`, `W''` (`Work.C17adj.PhiNum_eq`),

`PhiNum a b W = W·PhiU + W'·PhiV + W''·PhiZ`

with `natDegree PhiU ≤ 25`, `natDegree PhiV ≤ 26`, `natDegree PhiZ ≤ 27` and top coefficients

* `coeff 25 PhiU = 25`,  * `coeff 26 PhiV = −9`,  * `coeff 27 PhiZ = 1`.

Since `W` has degree `n`, `W'·PhiV` has degree `≤ (n−1)+26 = n+25` and `W''·PhiZ` has degree
`≤ (n−2)+27 = n+25`, and on the top coefficient the three terms contribute
`lc W·(25 + n·(−9) + n(n−1)) = lc W·(n−5)²`.  This is the statement of `phi_degree`.
-/

namespace Work.C17adj

open Polynomial

noncomputable section

theorem phi_degree (a b : ℚ) (W : Polynomial ℂ) (hW : W ≠ 0) :
    (Work.C17adj.PhiNum a b W).natDegree ≤ W.natDegree + 25 ∧
      (Work.C17adj.PhiNum a b W).coeff (W.natDegree + 25)
        = W.leadingCoeff * ((W.natDegree : ℂ) - 5) ^ 2 := by
  obtain ⟨hP2nd, hP2c, hP1nd, hP1c, hP0nd, hP0c,
    hAnd, hAc, hCnd, hCc, hDnd, hDc, hD1nd, hD1c, hD2nd, hD2c⟩ :=
    phi_lead_facts a b
  obtain ⟨hUnd, hUc, hVnd, hVc, hZnd, hZc⟩ :=
    phi_UZ_facts a b ⟨hP2nd, hP2c⟩ ⟨hAnd, hAc⟩ ⟨hCnd, hCc⟩
      ⟨hDnd, hDc⟩ ⟨hD1nd, hD1c⟩ ⟨hD2nd, hD2c⟩
  rw [PhiNum_eq]
  have hd1 : (W * PhiU a b).natDegree ≤ W.natDegree + 25 := by
    calc (W * PhiU a b).natDegree ≤ W.natDegree + (PhiU a b).natDegree := natDegree_mul_le
      _ ≤ W.natDegree + 25 := by omega
  have hd2 : (W.derivative * PhiV a b).natDegree ≤ W.natDegree + 25 :=
    (deriv_mul_le W (PhiV a b) hVnd).1
  have hd3 : (W.derivative.derivative * PhiZ a b).natDegree ≤ W.natDegree + 25 :=
    (deriv2_mul_le W (PhiZ a b) hZnd).1
  constructor
  · calc (W * PhiU a b + W.derivative * PhiV a b + W.derivative.derivative * PhiZ a b).natDegree
        ≤ max (W * PhiU a b + W.derivative * PhiV a b).natDegree
            (W.derivative.derivative * PhiZ a b).natDegree := natDegree_add_le _ _
      _ ≤ W.natDegree + 25 :=
          max_le (le_trans (natDegree_add_le _ _) (max_le hd1 hd2)) hd3
  · rw [coeff_add, coeff_add,
      coeff_mul_natDegree_le W (PhiU a b) W.natDegree 25 le_rfl hUnd,
      hUc, (deriv_mul_le W (PhiV a b) hVnd).2, hVc,
      (deriv2_mul_le W (PhiZ a b) hZnd).2, hZc, coeff_natDegree]
    ring

end

end Work.C17adj
