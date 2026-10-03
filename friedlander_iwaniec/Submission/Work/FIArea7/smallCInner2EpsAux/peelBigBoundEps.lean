import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.defs
import Submission.Work.FIArea7.smallCInner2EpsAux.smoothBilinEps
import Submission.Work.FIArea7.smallCInner2EpsAux.peelBigEpsDefs
import Submission.Work.FIArea7.smallCInner2EpsAux.peelBigFinalArith
import Submission.Work.FIArea7.smallCInner2EpsAux.peelBig2_eq_bilin_sub_diag
import Submission.Work.FIArea7.smallCInner2EpsAux.peelDiagSumBound

set_option maxHeartbeats 2000000

namespace Work.FIArea7.smallCInner2EpsAux

theorem peelBigBoundEps (h31 : Work.FIArea7.Prop231) :
    ∀ ε : ℝ, 0 < ε → ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (k : ℤ) (c u z : ℕ)
        (P : ℝ → ℝ) (a b K : ℝ),
        1 ≤ c → 1 ≤ z → z ≤ u →
        (∀ z', ‖chi z'‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        ContDiff ℝ 1 P → 0 ≤ a → (∀ u, 0 ≤ P u) → (∀ u, P u ≤ 1) →
        (∀ u, P u ≠ 0 → a < u ∧ u ≤ b) → (∀ u, |deriv P u| ≤ K) →
        ‖Work.FIArea7.smallCInner2EpsAux.peelBig2 u z (Work.FIArea7.smallCInner2EpsAux.cTerm Pa chi k c P)‖
          ≤ C * ((c.divisors.card : ℕ) : ℝ) * (u : ℝ) * ((z : ℝ) ^ (-(1 : ℝ) / 12))
              * (Real.log ((u : ℝ) + 2)) ^ A
              * (((u : ℝ) + (c : ℝ) + 2) ^ ε)
              * (K * |b - a| + 1) := by
  intro ε hε
  obtain ⟨C1, A1, hC1, hA1, hsm⟩ := smoothBilinEps h31 ε hε
  obtain ⟨C, A, hC, hA, hfin⟩ := peelBigFinalArith C1 100 A1 1 ε hC1 (by norm_num) hA1 (by norm_num) hε
  refine ⟨C, A, hC, hA, ?_⟩
  intro Pa chi k c u z P a b K hc hz hzu hchi hmul hPcd ha hP0 hP1 hPsupp hPder
  have hK0 : (0:ℝ) ≤ K := le_trans (abs_nonneg _) (hPder 0)
  have hW1 : 1 ≤ K * |b - a| + 1 := by
    have : 0 ≤ K * |b - a| := mul_nonneg hK0 (abs_nonneg _)
    linarith
  have hPabs : ∀ t, |P t| ≤ 1 := fun t => abs_le.mpr ⟨by linarith [hP0 t], hP1 t⟩
  have hτ0 : (0:ℝ) ≤ ((c.divisors.card : ℕ) : ℝ) := by positivity
  have hB : ‖peelBilinSum Pa chi k c u z P‖
      ≤ C1 * (((c.divisors.card : ℕ) : ℝ))
        * (((peelBigM u z : ℝ) + (peelBigM u z : ℝ)) ^ ((1:ℝ)/12)) * (u : ℝ) ^ ((11:ℝ)/12)
        * (Real.log ((u : ℝ) + 2)) ^ A1 * (((u : ℝ) + (c : ℝ) + 2) ^ ε)
        * (K * |b - a| + 1) := by
    have h := hsm chi k c (peelBigM u z) (peelBigM u z) u (peelA Pa c z) (peelB Pa c u z) P a b K
      hc hchi hmul (fun m _ => norm_peelA_le Pa c z m) (fun n _ => norm_peelB_le Pa c u z n)
      hPcd ha hP0 hP1 hPsupp hPder
    simpa only [peelBilinSum, peelT] using h
  have hD : ‖peelDiagSum Pa chi k c u z P‖
      ≤ 100 * (((c.divisors.card : ℕ) : ℝ)) * (u : ℝ)
        * (Real.log ((u : ℝ) + 2)) / (z : ℝ) :=
    peelDiagSumBound Pa chi k c u z P hchi hPabs hz
  have hXeq : ((peelBigM u z : ℝ) + (peelBigM u z : ℝ)) ^ ((1:ℝ)/12)
      = (2 * ((u / (z+1) : ℕ) : ℝ)) ^ ((1:ℝ)/12) := by
    rw [peelBigM]; congr 1; ring
  rw [peelBig2_eq_bilin_sub_diag Pa chi k c u z P hz]
  have hfin' := hfin u z c hz
  rw [Real.rpow_one] at hfin'
  calc ‖peelBilinSum Pa chi k c u z P - peelDiagSum Pa chi k c u z P‖
      ≤ ‖peelBilinSum Pa chi k c u z P‖ + ‖peelDiagSum Pa chi k c u z P‖ := norm_sub_le _ _
    _ ≤ (C1 * (((c.divisors.card : ℕ) : ℝ))
          * (((peelBigM u z : ℝ) + (peelBigM u z : ℝ)) ^ ((1:ℝ)/12)) * (u : ℝ) ^ ((11:ℝ)/12)
          * (Real.log ((u : ℝ) + 2)) ^ A1 * (((u : ℝ) + (c : ℝ) + 2) ^ ε)
          * (K * |b - a| + 1))
        + (100 * (((c.divisors.card : ℕ) : ℝ)) * (u : ℝ)
          * (Real.log ((u : ℝ) + 2)) / (z : ℝ)) := add_le_add hB hD
    _ ≤ (((c.divisors.card : ℕ) : ℝ)) * (K * |b - a| + 1)
          * (C1 * (2 * ((u / (z+1) : ℕ) : ℝ)) ^ ((1:ℝ)/12) * (u : ℝ) ^ ((11:ℝ)/12)
              * (((u : ℝ) + (c : ℝ) + 2) ^ ε) * (Real.log ((u : ℝ) + 2)) ^ A1
            + 100 * (u : ℝ) * (Real.log ((u : ℝ) + 2)) / (z : ℝ)) := by
        rw [hXeq]
        have hZ2nn : (0:ℝ) ≤ 100 * (u : ℝ) * (Real.log ((u : ℝ) + 2)) / (z : ℝ) :=
          div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg u))
            (Real.log_nonneg (by have h : (0:ℝ) ≤ (u:ℝ) := Nat.cast_nonneg u; linarith))) (Nat.cast_nonneg z)
        have hZ : (100:ℝ) * (((c.divisors.card : ℕ) : ℝ)) * (u : ℝ)
              * (Real.log ((u : ℝ) + 2)) / (z : ℝ)
            ≤ (((c.divisors.card : ℕ) : ℝ)) * (K * |b - a| + 1)
              * (100 * (u : ℝ) * (Real.log ((u : ℝ) + 2)) / (z : ℝ)) := by
          calc (100:ℝ) * (((c.divisors.card : ℕ) : ℝ)) * (u : ℝ) * (Real.log ((u : ℝ) + 2)) / (z : ℝ)
              = (((c.divisors.card : ℕ) : ℝ))
                  * (100 * (u : ℝ) * (Real.log ((u : ℝ) + 2)) / (z : ℝ)) := by ring
            _ ≤ (((c.divisors.card : ℕ) : ℝ)) * (100 * (u : ℝ) * (Real.log ((u : ℝ) + 2)) / (z : ℝ))
                  * (K * |b - a| + 1) := le_mul_of_one_le_right (mul_nonneg hτ0 hZ2nn) hW1
            _ = (((c.divisors.card : ℕ) : ℝ)) * (K * |b - a| + 1)
                  * (100 * (u : ℝ) * (Real.log ((u : ℝ) + 2)) / (z : ℝ)) := by ring
        nlinarith [hZ]
    _ ≤ (((c.divisors.card : ℕ) : ℝ)) * (K * |b - a| + 1)
          * (C * (u : ℝ) * ((z : ℝ) ^ (-(1 : ℝ) / 12)) * (((u : ℝ) + (c : ℝ) + 2) ^ ε)
              * (Real.log ((u : ℝ) + 2)) ^ A) := by
        apply mul_le_mul_of_nonneg_left hfin'
        positivity
    _ = C * ((c.divisors.card : ℕ) : ℝ) * (u : ℝ) * ((z : ℝ) ^ (-(1 : ℝ) / 12))
          * (Real.log ((u : ℝ) + 2)) ^ A * (((u : ℝ) + (c : ℝ) + 2) ^ ε)
          * (K * |b - a| + 1) := by ring

end Work.FIArea7.smallCInner2EpsAux
