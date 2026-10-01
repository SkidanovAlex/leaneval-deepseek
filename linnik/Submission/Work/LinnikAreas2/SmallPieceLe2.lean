/-
# `LinnikAreas2.SmallPieceLe2` — the range `n ≤ ⌊U⌋` of the HB (11.14) Abel kernel sum

A copy of `Submission/Work/LinnikAreas/Density4/small_piece_le.lean` moved into the
`Work.LinnikAreas2` namespace (with the `ψ`-vocabulary of `LinnikAreas2.PsiDefs2`), so that the
`(D1)` assembly of this area keeps the module `Work.LinnikAreas.Density4.psi_defs` — and with it
the colliding module name `Work.LinnikAreas.Density4.sum_log_div_le` — out of its import cone.
-/

import Mathlib
import Submission.Work.LinnikAreas2.PsiDefs2

namespace Work.LinnikAreas2

open Work.LinnikAreas.Density4

/-- **The range `n ≤ ⌊U⌋` of the Abel kernel sum of HB (11.14).**
Hypotheses: `0 < U`, `0 < X`, `1 ≤ U`, `U ≤ V` and the case hypothesis `U ≤ L² X`
(which makes `φ(n) = (e^{-n/X}-e^{-nL²/U})/n` nonincreasing).  Then for every `M ≤ ⌊U⌋+1` this
part of the sum is at most `L²/U`: on `1 ≤ n ≤ ⌊U⌋` one has `A(n) = Ψ(n)² = 1`
(HB (11.10), `psSum_eq_one`), the `φ`-differences telescope (`phiW_telescope`) and
`φ(1) = wt 1 ≤ L²/U` (`wt_le_mul`). -/
theorem small_piece_le {L U V X : ℝ} (hU : 0 < U) (hX : 0 < X) (hU1 : 1 ≤ U) (hUV : U ≤ V)
    (hcase : U ≤ L^2 * X) (M : ℕ) (hM : M ≤ Nat.floor U + 1) :
    ∑ n ∈ Finset.Ico 1 M, psSum U V n * (phiW L U X n - phiW L U X (n+1)) ≤ L^2/U := by
  by_cases hM1 : 1 ≤ M
  · -- Every `psSum U V n` in the range equals `1`.
    have hterm : ∀ n ∈ Finset.Ico 1 M,
        psSum U V n * (phiW L U X n - phiW L U X (n+1))
          = (phiW L U X n - phiW L U X (n+1)) := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      have hnle : n ≤ Nat.floor U := by omega
      have hfloor : (Nat.floor U : ℝ) ≤ U := Nat.floor_le hU.le
      have hnU : (n : ℝ) ≤ U := by
        have hcast : (n : ℝ) ≤ (Nat.floor U : ℝ) := by exact_mod_cast hnle
        linarith
      rw [psSum_eq_one hU1 hUV hn.1 hnU, one_mul]
    rw [Finset.sum_congr rfl hterm, phiW_telescope hM1]
    have hphi1 : phiW L U X 1 = wt L U X 1 := by rw [phiW, Nat.cast_one, div_one]
    have hnonneg : 0 ≤ phiW L U X M := phiW_nonneg hU hX hcase M
    have hwt1 : wt L U X 1 ≤ L^2/U := by
      have := wt_le_mul (L := L) (U := U) (X := X) hU hX 1
      simpa using this
    linarith
  · -- The range is empty.
    have hempty : Finset.Ico 1 M = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    rw [hempty, Finset.sum_empty]
    exact div_nonneg (sq_nonneg L) hU.le

end Work.LinnikAreas2
