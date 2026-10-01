import Mathlib
import Submission.Work.ZeroDensity.Jutila.mixedSelbergDefs
import Submission.Work.ZeroDensity.Jutila.BzFormSharp
import Submission.Work.ZeroDensity.Jutila.grahamCrossAssembly
import Submission.Work.ZeroDensity.Jutila.MulBzAux
import Submission.Work.ZeroDensity.Jutila.LzAux.HEasyReal
import Submission.Work.ZeroDensity.Jutila.LzAux.CzSoftCrossAux
import Submission.Work.ZeroDensity.Jutila.LzAux.CzSigMul
import Submission.Work.ZeroDensity.Jutila.LzAux.CzLogSqLe
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzAbelHard
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzModelContHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRIBoundHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.ModelBHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.KappaMertensHere
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.SumInvPowLeHere
import Submission.Work.ZeroDensity.Jutila.MertensMuDecay
import Submission.Work.ZeroDensity.Jutila.MsqAux.CzRIISumBounds
import Submission.Work.ZeroDensity.Jutila.BzCross.czInSum_bound2
import Submission.Work.ZeroDensity.Jutila.BzCross.FloorError
import Submission.Work.ZeroDensity.Jutila.BzCross.Reindex

/-!
# The sharp lower bound for the mixed Selberg cross sum

`MsqSharpCrossLower` is the lower half of the mixed two-parameter Selberg evaluation
`Σ_{n ≤ N} Lz w n · Lz y n = N·Msq w y + O(N)` for `1 < w ≤ y ≤ N`.  It follows from the sharp
two-sided mixed estimate (`Σ_{n ≤ N} Lz w n · Lz y n = N·log w + O(N)`) together with the sharp
bound `|Msq w y − log w| ≤ C` (`BzFormSharp.msq_le_log_add_const`).

The sharp two-sided mixed estimate is assembled here from the workspace's four analytic inputs
(`grahamCrossAssembly.grahamCrossTwoSided_of`) using the easy-range Barban–Vehov estimate
(`LzAux.HEasyReal`), `Σ Λ² = N log N + O(N)` (`grahamCrossAssembly.vonMangoldtSqEval_here`),
`Σ Λ·B_z = −N log(N/z) + O(N)` (`MulBzAux`) and the `S₃`-cross estimate
`Σ B_z·B_y = N log(N/y) + O(N)` (`bzCross_est` below).

The last one is Graham's deep estimate; it is re-assembled here from the workspace's `S₃` pieces
(`BzCross.Reindex`, `LzAux.CzSoftCrossAux`, `LzDiffAux.cz_abel_hard_of`, `BzCross.FloorError`,
`LzDiffAux.CzModelContHere`) with the pointwise boundary bound `czModelB_bound`, which rests on the
two region estimates `LzDiffAux.CzRIBoundHere` (`czRI`) and `czRII_bound` (`czRII`).  The region-II
integral estimate is assembled from the `czInSum` estimate `BzCross.czInSum_bound2` and the four
Region-II sum bounds `MsqAux.CzRIISumBounds`.
-/

namespace Work.ZeroDensity.Jutila.MsqSharpCrossAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.BzCross

noncomputable section

/-! ## Region II of the `S₃` boundary term -/

lemma r_div_kap_le_one_sf {r : ℕ} (hr : Squarefree r) : (r:ℝ)/kap r ≤ 1 := by
  rw [div_le_one (kap_pos r), kap.eq_def]
  have h : (r:ℝ) = ∏ p ∈ r.primeFactors, (p:ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  rw [h]
  exact Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p _ => by linarith)

lemma one_div_sqrt_nonneg (d : ℕ) : (0:ℝ) ≤ 1/Real.sqrt (d:ℝ) := by
  rw [one_div]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma sum_div_sqrt_nonneg (r : ℕ) : (0:ℝ) ≤ ∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ) :=
  Finset.sum_nonneg (fun d _ => one_div_sqrt_nonneg d)

theorem czRII_bound : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ),
    1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y → |Work.ZeroDensity.Jutila.BzCross.czRII w y N| ≤ C * (N : ℝ) := by
  obtain ⟨Ci, ci, hCi, hci, hIn⟩ := Work.ZeroDensity.Jutila.BzCross.czInSum_bound2 Work.ZeroDensity.Jutila.LzDiffAux.KappaMertensHere
  obtain ⟨Cm, cm, hCm, hcm, hM⟩ := MertensMuDecay
  obtain ⟨C1, hC1, hS1R, hS1T, hS2, hS3⟩ := Work.ZeroDensity.Jutila.MsqAux.CzRIISumBounds ci hci
  obtain ⟨C2, hC2, hS1R2, hS1T2, hS2b, hS3b⟩ := Work.ZeroDensity.Jutila.MsqAux.CzRIISumBounds cm hcm
  obtain ⟨hcube, hsq⟩ := Work.ZeroDensity.Jutila.LzDiffAux.SumInvPowLeHere
  refine ⟨(Real.pi^2/6)*Cm*C2 + Ci*C1 + Ci*C1*C1 + 2*Ci*C1 + 1, by positivity, ?_⟩
  intro w y N hw hwy hyN hNwy
  have hwpos : (0:ℝ) < w := by linarith
  have hy0 : (0:ℝ) ≤ y := by linarith
  have hypos : (0:ℝ) < y := by linarith
  rw [czRII_reindex N hw hy0]
  set Q := czQ y N with hQ
  have hsplit : ∀ q : ℕ,
      (∑ r ∈ Finset.Icc 1 (czR w N q),
          ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r) * czInSum w y N q r)
    = -(w * (Real.pi^2/6)) * (∑ r ∈ Finset.Icc 1 (czR w N q),
          (ArithmeticFunction.moebius r : ℝ))
      + ∑ r ∈ Finset.Icc 1 (czR w N q), ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
          * (czInSum w y N q r + w * (Real.pi^2/6) * (kap r / r)) := by
    intro q
    have hterm : ∀ r ∈ Finset.Icc 1 (czR w N q),
        ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r) * czInSum w y N q r
          = ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
              * (czInSum w y N q r + w * (Real.pi^2/6) * (kap r / r))
            - w * (Real.pi^2/6) * (ArithmeticFunction.moebius r : ℝ) := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      have hr1 : 1 ≤ r := hr.1
      have hr0 : (r:ℝ) ≠ 0 := by
        have : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr1
        exact ne_of_gt this
      have hk0 : kap r ≠ 0 := kap_ne_zero r
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    have hfac : (∑ r ∈ Finset.Icc 1 (czR w N q),
          w * (Real.pi^2/6) * (ArithmeticFunction.moebius r : ℝ))
        = w * (Real.pi^2/6) * (∑ r ∈ Finset.Icc 1 (czR w N q),
            (ArithmeticFunction.moebius r : ℝ)) := by
      rw [Finset.mul_sum]
    rw [hfac]
    ring
  have hsum : (∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 1 (czR w N q),
        ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r) * czInSum w y N q r)
      = (∑ q ∈ Finset.Icc 1 Q, -(w * (Real.pi^2/6))
            * (∑ r ∈ Finset.Icc 1 (czR w N q), (ArithmeticFunction.moebius r : ℝ)))
        + (∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 1 (czR w N q),
            ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
              * (czInSum w y N q r + w * (Real.pi^2/6) * (kap r / r))) := by
    rw [Finset.sum_congr rfl (fun q _ => hsplit q), Finset.sum_add_distrib]
  rw [hsum]
  have hb1 : |∑ q ∈ Finset.Icc 1 Q, -(w * (Real.pi^2/6))
        * (∑ r ∈ Finset.Icc 1 (czR w N q), (ArithmeticFunction.moebius r : ℝ))|
      ≤ (Real.pi^2/6) * Cm * C2 * (N:ℝ) := by
    have hMq : ∀ q, |∑ r ∈ Finset.Icc 1 (czR w N q), (ArithmeticFunction.moebius r : ℝ)|
        ≤ Cm * (czR w N q : ℝ) * Dc cm (czR w N q) := by
      intro q
      rcases Nat.eq_zero_or_pos (czR w N q) with h0 | hp
      · rw [h0]; simp
      · simpa only [Dc] using hM (czR w N q) hp
    have hs1 : (∑ q ∈ Finset.Icc 1 Q, (czR w N q : ℝ) * Dc cm (czR w N q))
        ≤ ((N:ℝ)/w) * C2 := by
      calc (∑ q ∈ Finset.Icc 1 Q, (czR w N q : ℝ) * Dc cm (czR w N q))
          ≤ ∑ q ∈ Finset.Icc 1 Q, ((N:ℝ)/((q:ℝ)*w)) * Dc cm (czR w N q) := by
            apply Finset.sum_le_sum; intro q _
            have : ((czR w N q : ℕ) : ℝ) ≤ (N:ℝ)/((q:ℝ)*w) := by
              rw [czR]; exact Nat.floor_le (by positivity)
            exact mul_le_mul_of_nonneg_right this (Dc_pos cm _).le
        _ = ((N:ℝ)/w) * ∑ q ∈ Finset.Icc 1 Q, (1/(q:ℝ)) * Dc cm (czR w N q) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
        _ ≤ ((N:ℝ)/w) * C2 :=
            mul_le_mul_of_nonneg_left (hS1R2 w y N hw hwy hyN hNwy) (by positivity)
    have hcong : (∑ q ∈ Finset.Icc 1 Q, Cm * (czR w N q : ℝ) * Dc cm (czR w N q))
        = Cm * ∑ q ∈ Finset.Icc 1 Q, (czR w N q : ℝ) * Dc cm (czR w N q) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
    calc |∑ q ∈ Finset.Icc 1 Q, -(w * (Real.pi^2/6))
            * (∑ r ∈ Finset.Icc 1 (czR w N q), (ArithmeticFunction.moebius r : ℝ))|
        = w * (Real.pi^2/6) * |∑ q ∈ Finset.Icc 1 Q,
            (∑ r ∈ Finset.Icc 1 (czR w N q), (ArithmeticFunction.moebius r : ℝ))| := by
          rw [show (∑ q ∈ Finset.Icc 1 Q, -(w * (Real.pi^2/6))
                * (∑ r ∈ Finset.Icc 1 (czR w N q), (ArithmeticFunction.moebius r : ℝ)))
              = -(w * (Real.pi^2/6)) * ∑ q ∈ Finset.Icc 1 Q,
                  (∑ r ∈ Finset.Icc 1 (czR w N q), (ArithmeticFunction.moebius r : ℝ)) by
                rw [Finset.mul_sum]]
          rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < w * (Real.pi^2/6))]
      _ ≤ w * (Real.pi^2/6) * ∑ q ∈ Finset.Icc 1 Q,
            |∑ r ∈ Finset.Icc 1 (czR w N q), (ArithmeticFunction.moebius r : ℝ)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ w * (Real.pi^2/6) * ∑ q ∈ Finset.Icc 1 Q,
            Cm * (czR w N q : ℝ) * Dc cm (czR w N q) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => hMq q)) (by positivity)
      _ = w * (Real.pi^2/6) * Cm * (∑ q ∈ Finset.Icc 1 Q,
            (czR w N q : ℝ) * Dc cm (czR w N q)) := by
          rw [hcong]; ring
      _ ≤ w * (Real.pi^2/6) * Cm * (((N:ℝ)/w) * C2) :=
          mul_le_mul_of_nonneg_left hs1 (by positivity)
      _ = (Real.pi^2/6) * Cm * C2 * (N:ℝ) := by
          field_simp
          try ring
  have hb2 : |∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 1 (czR w N q),
        ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
          * (czInSum w y N q r + w * (Real.pi^2/6) * (kap r / r))|
      ≤ (Ci*C1 + Ci*C1*C1 + 2*Ci*C1) * (N:ℝ) := by
    have hsig_nn : ∀ (q r : ℕ), (0:ℝ) ≤ (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
        * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2) := by
      intro q r
      exact mul_nonneg (sum_div_sqrt_nonneg r)
        (add_nonneg (Dc_pos ci _).le (sq_nonneg _))
    have hEq : ∀ q ∈ Finset.Icc 1 Q,
        |∑ r ∈ Finset.Icc 1 (czR w N q), ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
            * (czInSum w y N q r + w*(Real.pi^2/6)*(kap r/r))|
        ≤ Ci*w*(C1*(y/w + (czR w N q:ℝ)*Dc ci (czT y N q)) + C1*((czR w N q:ℝ)^3/y^2)) := by
      intro q _
      have h1 : |∑ r ∈ Finset.Icc 1 (czR w N q), ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
            * (czInSum w y N q r + w*(Real.pi^2/6)*(kap r/r))|
          ≤ ∑ r ∈ (Finset.Icc 1 (czR w N q)).filter (fun r => Squarefree r),
              |((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
                * (czInSum w y N q r + w*(Real.pi^2/6)*(kap r/r))| := by
        calc |∑ r ∈ Finset.Icc 1 (czR w N q), ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
              * (czInSum w y N q r + w*(Real.pi^2/6)*(kap r/r))|
            ≤ ∑ r ∈ Finset.Icc 1 (czR w N q),
                |((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
                  * (czInSum w y N q r + w*(Real.pi^2/6)*(kap r/r))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ r ∈ (Finset.Icc 1 (czR w N q)).filter (fun r => Squarefree r),
                |((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
                  * (czInSum w y N q r + w*(Real.pi^2/6)*(kap r/r))| := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl; intro r _
              by_cases hs : Squarefree r
              · rw [if_pos hs]
              · rw [if_neg hs, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
                simp
      have h2 : ∀ r ∈ (Finset.Icc 1 (czR w N q)).filter (fun r => Squarefree r),
          |((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
              * (czInSum w y N q r + w*(Real.pi^2/6)*(kap r/r))|
          ≤ ((r:ℝ)/kap r) * Ci * w * (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2) := by
        intro r hr
        rw [Finset.mem_filter, Finset.mem_Icc] at hr
        obtain ⟨⟨hr1, hr2⟩, hrsf⟩ := hr
        have hle : |((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)| ≤ (r:ℝ)/kap r := by
          have hb : |((ArithmeticFunction.moebius r : ℝ))| ≤ 1 := by
            rw [← Int.cast_abs]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r)
          have hkap : (0:ℝ) < kap r := kap_pos r
          have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
          calc |((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)|
              = |((ArithmeticFunction.moebius r : ℝ))| * (r:ℝ) / kap r := by
                rw [abs_div, abs_mul, abs_of_nonneg hr0, abs_of_pos hkap]
            _ ≤ 1 * (r:ℝ) / kap r := by
                apply div_le_div_of_nonneg_right _ hkap.le
                exact mul_le_mul_of_nonneg_right hb hr0
            _ = (r:ℝ)/kap r := by ring
        rw [abs_mul]
        calc |((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)|
                * |czInSum w y N q r + w * (Real.pi^2/6) * (kap r / r)|
            ≤ ((r:ℝ)/kap r) * (Ci * w * (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2)) :=
              mul_le_mul hle (hIn w y N q r hw hwy hNwy hrsf hr1 hr2)
                (abs_nonneg _) (div_nonneg (Nat.cast_nonneg r) (kap_pos r).le)
          _ = ((r:ℝ)/kap r) * Ci * w * (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2) := by ring
      have h3 : (∑ r ∈ (Finset.Icc 1 (czR w N q)).filter (fun r => Squarefree r),
              |((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
                  * (czInSum w y N q r + w*(Real.pi^2/6)*(kap r/r))|)
          ≤ Ci*w*(C1*(y/w + (czR w N q:ℝ)*Dc ci (czT y N q)) + C1*((czR w N q:ℝ)^3/y^2)) := by
        calc (∑ r ∈ (Finset.Icc 1 (czR w N q)).filter (fun r => Squarefree r),
              |((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
                  * (czInSum w y N q r + w*(Real.pi^2/6)*(kap r/r))|)
            ≤ ∑ r ∈ (Finset.Icc 1 (czR w N q)).filter (fun r => Squarefree r),
                ((r:ℝ)/kap r) * Ci * w * (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                  * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2) :=
              Finset.sum_le_sum h2
          _ ≤ ∑ r ∈ (Finset.Icc 1 (czR w N q)).filter (fun r => Squarefree r),
                Ci*w*((∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                  * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2)) := by
              apply Finset.sum_le_sum; intro r hr
              rw [Finset.mem_filter] at hr
              have hle : (r:ℝ)/kap r ≤ 1 := r_div_kap_le_one_sf hr.2
              have hX : (0:ℝ) ≤ (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                    * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2) :=
                hsig_nn q r
              have hcw : (0:ℝ) ≤ Ci*w := by positivity
              calc ((r:ℝ)/kap r) * Ci * w * (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                    * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2)
                  = (((r:ℝ)/kap r) * (Ci*w)) * ((∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                    * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2)) := by ring
                _ ≤ (1 * (Ci*w)) * ((∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                    * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2)) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hcw) hX
                _ = Ci*w*((∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                    * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2)) := by ring
          _ ≤ ∑ r ∈ Finset.Icc 1 (czR w N q),
                Ci*w*((∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                  * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2)) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.filter_subset _ _
              · intro r _ _
                exact mul_nonneg (mul_nonneg hCi.le hwpos.le) (hsig_nn q r)
          _ = Ci*w*(∑ r ∈ Finset.Icc 1 (czR w N q),
                (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                  * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2)) := by
              rw [Finset.mul_sum]
          _ ≤ Ci*w*(C1*(y/w + (czR w N q:ℝ)*Dc ci (czT y N q)) + C1*((czR w N q:ℝ)^3/y^2)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have hS2q := hS2 w y N q hw hwy hNwy
              have hS3q := hS3 w y N q hw hwy hNwy
              have hsplitr : (∑ r ∈ Finset.Icc 1 (czR w N q),
                    (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ))
                      * (Dc ci (czTmax w y N q r) + (((czTmax w y N q r : ℕ):ℝ)/w)^2))
                  = (∑ r ∈ Finset.Icc 1 (czR w N q),
                      (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ)) * Dc ci (czTmax w y N q r))
                    + (∑ r ∈ Finset.Icc 1 (czR w N q),
                      (∑ d ∈ r.divisors, 1/Real.sqrt (d:ℝ)) * (((czTmax w y N q r : ℕ):ℝ)/w)^2) := by
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl; intro r _; ring
              rw [hsplitr]
              linarith [hS2q, hS3q]
      exact le_trans h1 h3
    calc |∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 1 (czR w N q),
          ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
            * (czInSum w y N q r + w*(Real.pi^2/6)*(kap r/r))|
        ≤ ∑ q ∈ Finset.Icc 1 Q, |∑ r ∈ Finset.Icc 1 (czR w N q),
          ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
            * (czInSum w y N q r + w*(Real.pi^2/6)*(kap r/r))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Finset.Icc 1 Q, Ci*w*(C1*(y/w + (czR w N q:ℝ)*Dc ci (czT y N q))
            + C1*((czR w N q:ℝ)^3/y^2)) := Finset.sum_le_sum hEq
      _ ≤ (Ci*C1 + Ci*C1*C1 + 2*Ci*C1) * (N:ℝ) := by
          have hdec : (∑ q ∈ Finset.Icc 1 Q, Ci*w*(C1*(y/w + (czR w N q:ℝ)*Dc ci (czT y N q))
                + C1*((czR w N q:ℝ)^3/y^2)))
              = (∑ q ∈ Finset.Icc 1 Q, (Ci*w*C1*(y/w)
                    + Ci*w*C1*((czR w N q:ℝ)*Dc ci (czT y N q))))
                + (∑ q ∈ Finset.Icc 1 Q, Ci*w*C1*((czR w N q:ℝ)^3/y^2)) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl; intro q _; ring
          rw [hdec]
          have e1 : (∑ q ∈ Finset.Icc 1 Q, (Ci*w*C1*(y/w)
                + Ci*w*C1*((czR w N q:ℝ)*Dc ci (czT y N q))))
              = Ci*w*C1*(y/w)*(Q:ℝ)
                + Ci*w*C1*(∑ q ∈ Finset.Icc 1 Q, (czR w N q:ℝ)*Dc ci (czT y N q)) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
                ← Finset.mul_sum]
              simp only [Nat.add_sub_cancel]
              ring
          have e2 : (∑ q ∈ Finset.Icc 1 Q, Ci*w*C1*((czR w N q:ℝ)^3/y^2))
              = Ci*w*C1*(∑ q ∈ Finset.Icc 1 Q, (czR w N q:ℝ)^3/y^2) := by
              rw [← Finset.mul_sum]
          rw [e1, e2]
          have hQle : (Q:ℝ) ≤ (N:ℝ)/y := by
            rw [hQ, czQ]; exact Nat.floor_le (by positivity)
          have hT1 : Ci*w*C1*(y/w)*(Q:ℝ) ≤ Ci*C1*(N:ℝ) := by
            have hwyw : w*(y/w) = y := by
              field_simp
              try ring
            have he : Ci*w*C1*(y/w)*(Q:ℝ) = Ci*C1*(y*(Q:ℝ)) := by
              rw [show Ci*w*C1*(y/w)*(Q:ℝ) = Ci*C1*(w*(y/w))*(Q:ℝ) by ring, hwyw]
              ring
            rw [he]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc y*(Q:ℝ) ≤ y*((N:ℝ)/y) := mul_le_mul_of_nonneg_left hQle hypos.le
              _ = (N:ℝ) := by field_simp
          have hS1 : Ci*w*C1*(∑ q ∈ Finset.Icc 1 Q, (czR w N q:ℝ)*Dc ci (czT y N q))
              ≤ Ci*C1*C1*(N:ℝ) := by
            have hsum2 : (∑ q ∈ Finset.Icc 1 Q, (czR w N q:ℝ)*Dc ci (czT y N q))
                ≤ ((N:ℝ)/w)*C1 := by
              calc (∑ q ∈ Finset.Icc 1 Q, (czR w N q:ℝ)*Dc ci (czT y N q))
                  ≤ ∑ q ∈ Finset.Icc 1 Q, ((N:ℝ)/((q:ℝ)*w)) * Dc ci (czT y N q) := by
                    apply Finset.sum_le_sum; intro q _
                    have : ((czR w N q : ℕ) : ℝ) ≤ (N:ℝ)/((q:ℝ)*w) := by
                      rw [czR]; exact Nat.floor_le (by positivity)
                    exact mul_le_mul_of_nonneg_right this (Dc_pos ci _).le
                _ = ((N:ℝ)/w) * ∑ q ∈ Finset.Icc 1 Q, (1/(q:ℝ)) * Dc ci (czT y N q) := by
                    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
                _ ≤ ((N:ℝ)/w) * C1 :=
                    mul_le_mul_of_nonneg_left (hS1T w y N hw hwy hyN hNwy) (by positivity)
            calc Ci*w*C1*(∑ q ∈ Finset.Icc 1 Q, (czR w N q:ℝ)*Dc ci (czT y N q))
                ≤ Ci*w*C1*(((N:ℝ)/w)*C1) := mul_le_mul_of_nonneg_left hsum2 (by positivity)
              _ = Ci*C1*C1*(N:ℝ) := by field_simp
          have hS3 : Ci*w*C1*(∑ q ∈ Finset.Icc 1 Q, (czR w N q:ℝ)^3/y^2)
              ≤ 2*Ci*C1*(N:ℝ) := by
            have hsum3 : (∑ q ∈ Finset.Icc 1 Q, (czR w N q:ℝ)^3/y^2)
                ≤ 2*(N:ℝ)^3/(w^3*y^2) := by
              calc (∑ q ∈ Finset.Icc 1 Q, (czR w N q:ℝ)^3/y^2)
                  ≤ ∑ q ∈ Finset.Icc 1 Q, ((N:ℝ)/((q:ℝ)*w))^3/y^2 := by
                    apply Finset.sum_le_sum; intro q _
                    apply div_le_div_of_nonneg_right _ (by positivity)
                    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
                    rw [czR]; exact Nat.floor_le (by positivity)
                _ = ((N:ℝ)^3/(w^3*y^2)) * ∑ q ∈ Finset.Icc 1 Q, (1/(q:ℝ)^3) := by
                    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
                _ ≤ ((N:ℝ)^3/(w^3*y^2)) * 2 :=
                    mul_le_mul_of_nonneg_left (hcube Q) (by positivity)
                _ = 2*(N:ℝ)^3/(w^3*y^2) := by ring
            have hNw : ((N:ℝ)/(w*y))^2 ≤ 1 := by
              rw [div_pow, div_le_one (by positivity)]
              nlinarith [hNwy, hwpos, hypos]
            calc Ci*w*C1*(∑ q ∈ Finset.Icc 1 Q, (czR w N q:ℝ)^3/y^2)
                ≤ Ci*w*C1*(2*(N:ℝ)^3/(w^3*y^2)) := mul_le_mul_of_nonneg_left hsum3 (by positivity)
              _ = 2*Ci*C1*(N:ℝ)*(((N:ℝ)/(w*y))^2) := by field_simp; try ring
              _ ≤ 2*Ci*C1*(N:ℝ)*1 := mul_le_mul_of_nonneg_left hNw (by positivity)
              _ = 2*Ci*C1*(N:ℝ) := by ring
          have hR : (Ci*C1 + Ci*C1*C1 + 2*Ci*C1) * (N:ℝ)
              = Ci*C1*(N:ℝ) + Ci*C1*C1*(N:ℝ) + 2*Ci*C1*(N:ℝ) := by ring
          rw [hR]
          linarith [hT1, hS1, hS3]
  calc |(∑ q ∈ Finset.Icc 1 Q, -(w * (Real.pi^2/6))
          * (∑ r ∈ Finset.Icc 1 (czR w N q), (ArithmeticFunction.moebius r : ℝ)))
        + (∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 1 (czR w N q),
            ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
              * (czInSum w y N q r + w * (Real.pi^2/6) * (kap r / r)))|
      ≤ |∑ q ∈ Finset.Icc 1 Q, -(w * (Real.pi^2/6))
          * (∑ r ∈ Finset.Icc 1 (czR w N q), (ArithmeticFunction.moebius r : ℝ))|
        + |∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.Icc 1 (czR w N q),
            ((ArithmeticFunction.moebius r : ℝ) * (r:ℝ) / kap r)
              * (czInSum w y N q r + w * (Real.pi^2/6) * (kap r / r))| := abs_add_le _ _
    _ ≤ (Real.pi^2/6)*Cm*C2*(N:ℝ) + (Ci*C1 + Ci*C1*C1 + 2*Ci*C1)*(N:ℝ) := add_le_add hb1 hb2
    _ ≤ ((Real.pi^2/6)*Cm*C2 + Ci*C1 + Ci*C1*C1 + 2*Ci*C1 + 1) * (N:ℝ) := by
        have hNnneg : (0:ℝ) ≤ (N:ℝ) := by positivity
        nlinarith [hNnneg]

end

end Work.ZeroDensity.Jutila.MsqSharpCrossAux

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- **Boundary term of the two-sided `S₃` model.**  `|czModelB w y N| ≤ C·N` in the hard range
`1 ≤ w ≤ y ≤ N < w·y`: the two region estimates `czRI` (`LzDiffAux.CzRIBoundHere`) and `czRII`
(`MsqSharpCrossAux.czRII_bound`) give the claim through the exact split `czModelB_split`. -/
lemma czModelB_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y →
      |czModelB w y N| ≤ C * (N : ℝ) := by
  obtain ⟨C₁, hC₁, h₁⟩ := LzDiffAux.CzRIBoundHere
  obtain ⟨C₂, hC₂, h₂⟩ := MsqSharpCrossAux.czRII_bound
  refine ⟨(Real.pi ^ 2 / 6)⁻¹ * (C₁ + C₂), by positivity, ?_⟩
  intro w y N hw hwy hyN hNwy
  have hsplit := LzDiffAux.czModelB_split w y N hw hwy hyN hNwy
  have hζpos : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
  have h1 := h₁ w y N hw hwy hyN hNwy
  have h2 := h₂ w y N hw hwy hyN hNwy
  rw [hsplit, abs_mul, abs_of_pos (inv_pos.mpr hζpos)]
  calc (Real.pi ^ 2 / 6)⁻¹ * |BzCross.czRI w y N + BzCross.czRII w y N|
      ≤ (Real.pi ^ 2 / 6)⁻¹ * (|BzCross.czRI w y N| + |BzCross.czRII w y N|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (le_of_lt (inv_pos.mpr hζpos))
    _ ≤ (Real.pi ^ 2 / 6)⁻¹ * (C₁ * (N : ℝ) + C₂ * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (le_of_lt (inv_pos.mpr hζpos))
    _ = (Real.pi ^ 2 / 6)⁻¹ * (C₁ + C₂) * (N : ℝ) := by ring

/-- `|A + B + C − D| ≤ |A| + |B| + |C| + |D|`. -/
private lemma abs_chain4 (a b c d : ℝ) : |a + b + c - d| ≤ |a| + |b| + |c| + |d| := by
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b, le_abs_self c,
      neg_abs_le c, le_abs_self d, neg_abs_le d]

/-- **Graham's `S₃` cross estimate for the Möbius corrections.**  For `1 ≤ w ≤ y ≤ N`,
`|Σ_{n ≤ N} B_z(n)·B_y(n) − N·log(N/y)| ≤ C·N`. -/
theorem bzCross_est :
    ∃ C : ℝ, 0 < C ∧ ∀ w y : ℝ, 1 ≤ w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) - (N : ℝ) * Real.log ((N : ℝ) / y)|
        ≤ C * (N : ℝ) := by
  obtain ⟨C₁, hC₁, hsoft⟩ := LzAux.CzSoftCrossAux
  have heasy : ∀ w y : ℝ, 1 ≤ w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) → w * y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) - (N : ℝ) * Real.log ((N : ℝ) / y)|
        ≤ C₁ * (N : ℝ) := by
    intro w y hw hwy N hyN hcase
    rw [BzCross.Reindex w y N hw hwy hyN]
    exact hsoft w y N hw hwy hyN hcase
  obtain ⟨Ca, hCa, hAbel⟩ := LzDiffAux.cz_abel_hard_of LzAux.CzSigMul LzAux.CzLogSqLe
  obtain ⟨Cf, hCf, hFloor⟩ := BzCross.FloorError
  obtain ⟨Cc, hCc, hCont⟩ := LzDiffAux.CzModelContHere
  obtain ⟨Cb, hCb, hBound⟩ := czModelB_bound
  have hhard : ∀ w y : ℝ, 1 ≤ w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) → (N : ℝ) < w * y →
      |(∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) - (N : ℝ) * Real.log ((N : ℝ) / y)|
        ≤ (Ca + Cf + Cc + Cb) * (N : ℝ) := by
    intro w y hw hwy N hyN hNwy
    have e0 := BzCross.Reindex w y N hw hwy hyN
    have e1 := hAbel w y N hw hwy hyN hNwy
    have e2 := hFloor w y N hw hwy hyN hNwy
    have e3 := hCont w y N hw hwy hyN
    have e4 := hBound w y N hw hwy hyN hNwy
    rw [e0]
    have hsplit : czCross w y N - (N : ℝ) * Real.log ((N : ℝ) / y)
        = (czCross w y N - (czModelFloor w y N - czModelB w y N))
          + (czModelFloor w y N - czModelCont w y N)
          + (czModelCont w y N - (N : ℝ) * Real.log ((N : ℝ) / y))
          - czModelB w y N := by ring
    rw [hsplit]
    refine le_trans (abs_chain4 _ _ _ _) ?_
    have h1 := abs_le.mp e1
    have h2 := abs_le.mp e2
    have h3 := abs_le.mp e3
    have h4 := abs_le.mp e4
    have hring : Ca * (N : ℝ) + Cf * (N : ℝ) + Cc * (N : ℝ) + Cb * (N : ℝ)
        = (Ca + Cf + Cc + Cb) * (N : ℝ) := by ring
    linarith [h1.2, h2.2, h3.2, h4.2, hring]
  refine ⟨max C₁ (Ca + Cf + Cc + Cb), lt_max_of_lt_left hC₁, ?_⟩
  intro w y hw hwy N hyN
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  by_cases hcase : w * y ≤ (N : ℝ)
  · exact le_trans (heasy w y hw hwy N hyN hcase)
      (mul_le_mul_of_nonneg_right (le_max_left C₁ (Ca + Cf + Cc + Cb)) hNnn)
  · exact le_trans (hhard w y hw hwy N hyN (lt_of_not_ge hcase))
      (mul_le_mul_of_nonneg_right (le_max_right C₁ (Ca + Cf + Cc + Cb)) hNnn)

/-- **The sharp two-sided mixed estimate** `Σ_{n ≤ N} Lz w n · Lz y n = N·log w + O(N)`
for `1 < w ≤ y ≤ N`. -/
theorem lzCross_est :
    ∃ C : ℝ, 0 < C ∧ ∀ w y : ℝ, 1 < w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Lz w n * Lz y n) - (N : ℝ) * Real.log w| ≤ C * (N : ℝ) :=
  grahamCrossTwoSided_of LzAux.HEasyReal vonMangoldtSqEval_here MulBzAux bzCross_est

/-- **Sharp lower bound for the mixed Selberg cross sum.**  There is an absolute constant `C > 0`
with
  `N·Msq w y − C·N ≤ Σ_{n ≤ N} Lz w n · Lz y n`
for all real `1 < w ≤ y` and all `N ≥ y`. -/
theorem MsqSharpCrossLower :
    ∃ C : ℝ, 0 < C ∧ ∀ w y : ℝ, 1 < w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      (N : ℝ) * Msq w y - C * (N : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, Lz w n * Lz y n := by
  obtain ⟨C₁, hC₁pos, hS⟩ := lzCross_est
  obtain ⟨C₂, hC₂pos, hM⟩ := msq_le_log_add_const
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro w y hw hwy N hyN
  have hw1 : (1 : ℝ) ≤ w := le_of_lt hw
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : (N : ℝ) * Real.log w - C₁ * (N : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 N, Lz w n * Lz y n := by
    have h := hS w y hw hwy N hyN
    have hl := (abs_le.mp h).1
    linarith
  have h2 : (N : ℝ) * Msq w y ≤ (N : ℝ) * Real.log w + C₂ * (N : ℝ) := by
    have h := (abs_le.mp (hM w y hw1 hwy)).2
    nlinarith [hNnn, h]
  linarith [h1, h2]

end

end Work.ZeroDensity.Jutila
