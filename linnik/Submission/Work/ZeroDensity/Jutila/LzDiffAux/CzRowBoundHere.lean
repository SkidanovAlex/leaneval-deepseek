import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.CzRIAux
import Submission.Work.ZeroDensity.Jutila.BzCross.ModelBDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAuxDefs
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowBoundAux
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux.rowMain_decomp
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux.rowCoef_abs_le
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux.rowFI_abs_le
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux.rowSum_abs_log_le
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux.czEps_compare
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux.rowX_bound
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux.rowT2_bound
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux.rowT3_bound
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux.kap_div_le_czSig

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila.BzCross
open Work.ZeroDensity.Jutila.LzDiffAux.CzRowAux

set_option maxHeartbeats 1000000

noncomputable section


/-!
# The `(q,t)`-row bound of Region I (`CzRowBoundHere`)

`czRowSum w y N q t` (`BzCross/CzRIAux.lean`) is the `(q,t)`-row of the Region I boundary sum
`czRI` of the two-sided `S₃` model.  This file proves that, for squarefree `t`,

`|czRowSum w y N q t + y·ζ(2)·μ(t)| ≤ C·(t/κ(t))·(y·σ_{-1/2}(t)·e^{−c√(log Y_t)} + Y_t)`,
`Y_t = y·t/w`, `σ_{-1/2}(t) = Σ_{d|t} d^{-1/2}`,

under the Mertens-type input `KappaMertensInput` (Graham's (11)+(12), An's Lemmas 11ing/12ing).

ROUTE.  With `r₁ = min ⌊N/(qw)⌋ (czD w y t)`, `C_r = ⌊y/r⌋`, `X_r = y − r C_r ∈ [0,r)`,
`γ_r = log(C_r r/y) ∈ [−log 2,0]`, `P_r = [r⟂t]μ(r)/κ(r)` and `log(C_r t/w) = log(Y_t/r) + γ_r`
(`rowFI_split`), the row factors as `czRowSum = (t/κ(t))·μ(t)·rowMain` with
`rowMain = Σ_{r≤r₁} P_r·(r C_r)·czFI w y r t`, and `r C_r = y − X_r` together with

`czFI = -(log(Y_t/r)−1) + (log(Y_t/r)−1)γ_r + (γ_r²−γ_r) + 1`

splits it as `rowMain = y·(−rowS1 + rowT2 + rowT3 + rowS0) − rowX` (`rowMain_decomp`), where
`rowS1`, `rowS0` are exactly the two Mertens sums of `KappaMertensInput`.  Clause 1 at `R = r₁`
(and `Y = 2Y_t`, since `r₁ ≤ 2Y_t`) gives the cancellation `rowS1 = ζ(2)κ(t)/t + log(Y_t/r₁)·S₀ + E`
with `|E| ≤ C₀σ(t)e^{−c₀√log r₁}`, clause 2 bounds `S₀`, and the elementary estimates
`|X_r| ≤ r`, `|γ_r| ≤ 2r/y`, `Σ_{r≤r₁}(|log(Y_t/r)|+1) ≤ 10 Y_t` (`rowSum_abs_log_le`) give
`|y·rowT2| ≤ 20Y_t`, `|y·rowT3| ≤ 20Y_t`, `|rowX| ≤ 50Y_t`.  Finally `r₁ ≥ Y_t − 1` converts
`e^{−c₀√log r₁}` into `e^{−(c₀/2)√log Y_t}` (`czEps_compare`).  The degenerate case `r₁ = 1`
(`Y_t ≤ 2`) is handled directly with `rowMain = ⌊y⌋·czFI w y 1 t` and `κ(t)/t ≤ σ_{-1/2}(t)`
(`kap_div_le_czSig`).
-/

theorem CzRowBoundHere (h : Work.ZeroDensity.Jutila.KappaMertensInput) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {w y : ℝ} {N q t : ℕ}, 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y →
        1 ≤ q → q ≤ Work.ZeroDensity.Jutila.czQ y N →
        t ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czT y N q) → Squarefree t →
        |Work.ZeroDensity.Jutila.BzCross.czRowSum w y N q t
            + y * (Real.pi ^ 2 / 6) * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|
          ≤ C * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t)
              * (y * Work.ZeroDensity.Jutila.BzCross.czSig t
                  * Work.ZeroDensity.Jutila.BzCross.czEps c
                      (Work.ZeroDensity.Jutila.BzCross.czY w y t)
                + Work.ZeroDensity.Jutila.BzCross.czY w y t) := by
  obtain ⟨C0, c0, hC0, hc0, hcl1, hcl2⟩ := h
  set eta : ℝ := min c0 1 with heta_def
  have heta_pos : 0 < eta := lt_min hc0 one_pos
  have heta_le_c0 : eta ≤ c0 := min_le_left _ _
  have heta_le_one : eta ≤ 1 := min_le_right _ _
  set cf : ℝ := eta / 2 with hcf_def
  have hcf_pos : 0 < cf := by rw [hcf_def]; linarith
  have hcf_le_half : cf ≤ c0 / 2 := by rw [hcf_def]; linarith
  have hcfle1 : cf ≤ 1 := by rw [hcf_def]; linarith
  have hCfin_pos : 0 < max 100 (max (8 * C0 + 2) (30 / czEps cf 2)) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 100) (le_max_left _ _)
  refine ⟨max 100 (max (8 * C0 + 2) (30 / czEps cf 2)), cf, hCfin_pos, hcf_pos, ?_⟩
  intro w y N q t hw1 hwy hyN hNwy hq1 hqQ ht hsq
  have hw : 0 < w := by linarith
  have hy : 0 < y := by linarith
  have hy1 : (1 : ℝ) ≤ y := le_trans hw1 hwy
  have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  have htT : (t : ℝ) ≤ ((czT y N q : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp ht).2
  have htw : (t : ℝ) ≤ w := cz_t_le_w hy hNwy hq1 htT
  have hY1 : 1 ≤ czY w y t := czY_one_le hw hwy ht1
  have hYpos : 0 < czY w y t := czY_pos hw hy ht1
  have hYy : czY w y t ≤ y := czY_le_y hw hy.le htw
  set r1 : ℕ := min (czR w N q) (czD w y t) with hr1_def
  have hr1le : ((r1 : ℕ) : ℝ) ≤ 2 * czY w y t := by
    rw [hr1_def]; exact cz_r1_le hw hy htw ht1
  have hr1ge : czY w y t - 1 ≤ ((r1 : ℕ) : ℝ) := by
    rw [hr1_def, Nat.cast_min]
    exact le_min (czR_ge hw hy hq1 htT) (czD_ge hw hy htw ht1)
  have hr1pos : 1 ≤ r1 := by
    rw [hr1_def]
    exact le_min (czR_pos hw hwy hy hq1 hqQ) (czD_pos hw hwy hy ht1 htw)
  have hry : ∀ r ∈ Finset.Icc 1 r1, (r : ℝ) ≤ y := by
    intro r hr
    have hrle : r ≤ czR w N q := by
      have h1 : r ≤ r1 := (Finset.mem_Icc.mp hr).2
      rw [hr1_def] at h1
      exact le_trans h1 (min_le_left _ _)
    exact le_of_lt (cz_r_lt_y hw hy hNwy hq1 hrle)
  have hry' : ∀ r ∈ Finset.Icc 1 r1, 1 ≤ r ∧ (r : ℝ) ≤ y := fun r hr =>
    ⟨(Finset.mem_Icc.mp hr).1, hry r hr⟩
  have hS : ∑ r ∈ Finset.Icc 1 r1, (|Real.log (czY w y t / (r : ℝ))| + 1) ≤ 10 * czY w y t :=
    rowSum_abs_log_le hY1 hr1le
  have hfac : czRowSum w y N q t
      = ((t : ℝ) / kap t) * ((ArithmeticFunction.moebius t : ℤ) : ℝ) * rowMain w y t r1 := by
    rw [czRowSum_eq w y N q t, ← hr1_def]
  have hμ1 : |((ArithmeticFunction.moebius t : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have htknn : 0 ≤ (t : ℝ) / kap t := by
    have h1 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
    have h2 : 0 < kap t := kap_pos t
    positivity
  have hkey : czRowSum w y N q t
        + y * (Real.pi ^ 2 / 6) * ((ArithmeticFunction.moebius t : ℤ) : ℝ)
      = ((t : ℝ) / kap t) * ((ArithmeticFunction.moebius t : ℤ) : ℝ)
          * (rowMain w y t r1 + y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))) := by
    rw [hfac]
    have htne : (t : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (by omega : 0 < t))
    have hkne : kap t ≠ 0 := (kap_pos t).ne'
    field_simp
  have hbracket : |rowMain w y t r1 + y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))|
      ≤ (max 100 (max (8 * C0 + 2) (30 / czEps cf 2)))
          * (y * czSig t * czEps cf (czY w y t) + czY w y t) := by
    by_cases hsmall : r1 ≤ 1
    · -- degenerate case `r1 = 1`
      have hr1one : r1 = 1 := le_antisymm hsmall hr1pos
      have hYle2 : czY w y t ≤ 2 := by
        have h2 : ((r1 : ℕ) : ℝ) ≤ 1 := by rw [hr1one]; norm_num
        linarith [hr1ge, h2]
      have hmain1 : rowMain w y t r1 = (⌊y⌋₊ : ℝ) * czFI w y 1 t := by
        rw [hr1one]; exact rowMain_one w y t
      have hFI : |czFI w y 1 t| ≤ 5 * (Real.log 2 + 1) := by
        have hy1' : ((1 : ℕ) : ℝ) ≤ y := by exact_mod_cast hy1
        have h1 := rowFI_abs_le (w := w) (y := y) (r := 1) (t := t) hw le_rfl hy1' ht1
        have h2 : czY w y t / ((1 : ℕ) : ℝ) = czY w y t := by
          rw [Nat.cast_one, div_one]
        rw [h2] at h1
        have h3 : |Real.log (czY w y t)| ≤ Real.log 2 := by
          rw [abs_of_nonneg (Real.log_nonneg hY1)]
          exact Real.log_le_log hYpos hYle2
        linarith [h1]
      have hrowMain : |rowMain w y t r1| ≤ y * (5 * (Real.log 2 + 1)) := by
        rw [hmain1, abs_mul, abs_of_nonneg (Nat.cast_nonneg (⌊y⌋₊ : ℕ))]
        have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy.le
        have h3 : 0 ≤ 5 * (Real.log 2 + 1) := by
          have h4 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          linarith
        exact mul_le_mul h1 hFI (abs_nonneg _) hy.le
      have hbracket_small :
          |rowMain w y t r1 + y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))|
            ≤ y * czSig t * (5 * (Real.log 2 + 1) + Real.pi ^ 2 / 6) := by
        have h1 := abs_add_le (rowMain w y t r1) (y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ)))
        have h2 : |y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))|
            = y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ)) := by
          rw [abs_of_nonneg]
          have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
          have hk0 : 0 < kap t := kap_pos t
          positivity
        have hkap : kap t / (t : ℝ) ≤ czSig t := kap_div_le_czSig hsq ht1
        have hsig1 : 1 ≤ czSig t := czSig_one_le ht1
        have hsig0 : 0 ≤ czSig t := czSig_nonneg t
        have hpi0 : 0 ≤ Real.pi ^ 2 / 6 := by positivity
        have hkap0 : 0 ≤ kap t / (t : ℝ) := by
          have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
          have hk0 : 0 < kap t := kap_pos t
          positivity
        have h5 : 0 ≤ 5 * (Real.log 2 + 1) := by
          have h4 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          linarith
        have hyj : 0 ≤ y * (Real.pi ^ 2 / 6) := by positivity
        have h3 : y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
            ≤ y * czSig t * (Real.pi ^ 2 / 6) := by
          calc y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
              ≤ y * (Real.pi ^ 2 / 6) * czSig t := mul_le_mul_of_nonneg_left hkap hyj
            _ = y * czSig t * (Real.pi ^ 2 / 6) := by ring
        have h4 : y * (5 * (Real.log 2 + 1)) ≤ y * czSig t * (5 * (Real.log 2 + 1)) := by
          have h6 : y * 1 ≤ y * czSig t := mul_le_mul_of_nonneg_left hsig1 hy.le
          calc y * (5 * (Real.log 2 + 1)) = (y * 1) * (5 * (Real.log 2 + 1)) := by ring
            _ ≤ (y * czSig t) * (5 * (Real.log 2 + 1)) := mul_le_mul_of_nonneg_right h6 h5
            _ = y * czSig t * (5 * (Real.log 2 + 1)) := by ring
        linarith [h1, h2, hrowMain, h3, h4, hsig0, hYpos.le, hpi0, h5]
      have hC1 : 5 * (Real.log 2 + 1) + Real.pi ^ 2 / 6 ≤ 12 := by
        have h1 : Real.log 2 ≤ 1 := by
          have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        have h2 : Real.pi ^ 2 / 6 ≤ 2 := by
          have hp := Real.pi_lt_d2
          have hp0 := Real.pi_pos
          nlinarith [hp, hp0]
        linarith
      have hepsmin : czEps cf 2 ≤ czEps cf (czY w y t) := czEps_antitone hcf_pos.le hYpos hYle2
      have hbr2 : y * czSig t * (5 * (Real.log 2 + 1) + Real.pi ^ 2 / 6)
          ≤ (30 / czEps cf 2) * (y * czSig t * czEps cf (czY w y t) + czY w y t) := by
        have hsig0 : 0 ≤ czSig t := czSig_nonneg t
        have hεmin : 0 < czEps cf 2 := czEps_pos cf 2
        have hε : 0 < czEps cf (czY w y t) := czEps_pos cf _
        have hratio : 1 ≤ czEps cf (czY w y t) / czEps cf 2 := by
          rw [le_div_iff₀ hεmin]
          linarith [hepsmin]
        have hnn : 0 ≤ y * czSig t := by positivity
        have hA : y * czSig t * (5 * (Real.log 2 + 1) + Real.pi ^ 2 / 6)
            ≤ 12 * (y * czSig t) := by
          calc y * czSig t * (5 * (Real.log 2 + 1) + Real.pi ^ 2 / 6)
              ≤ (y * czSig t) * 12 := mul_le_mul_of_nonneg_left hC1 hnn
            _ = 12 * (y * czSig t) := by ring
        have hB : 12 * (y * czSig t) ≤ 30 * (y * czSig t) :=
          mul_le_mul_of_nonneg_right (by norm_num) hnn
        have hCc : 30 * (y * czSig t) ≤ 30 * ((y * czSig t) * (czEps cf (czY w y t) / czEps cf 2)) := by
          have h6 := mul_le_mul_of_nonneg_left hratio hnn
          linarith [h6]
        have hD : 30 * ((y * czSig t) * (czEps cf (czY w y t) / czEps cf 2))
            = (30 / czEps cf 2) * (y * czSig t * czEps cf (czY w y t)) := by
          field_simp
        have hE : (30 / czEps cf 2) * (y * czSig t * czEps cf (czY w y t))
            ≤ (30 / czEps cf 2) * (y * czSig t * czEps cf (czY w y t) + czY w y t) := by
          have h1 : 0 ≤ 30 / czEps cf 2 := by positivity
          have h2 : 0 ≤ czY w y t := hYpos.le
          exact mul_le_mul_of_nonneg_left (by linarith) h1
        linarith [hA, hB, hCc, hD, hE]
      have hCfge : (30 / czEps cf 2) ≤ max 100 (max (8 * C0 + 2) (30 / czEps cf 2)) :=
        le_trans (le_max_right (8 * C0 + 2) (30 / czEps cf 2)) (le_max_right 100 _)
      calc |rowMain w y t r1 + y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))|
          ≤ y * czSig t * (5 * (Real.log 2 + 1) + Real.pi ^ 2 / 6) := hbracket_small
        _ ≤ (30 / czEps cf 2) * (y * czSig t * czEps cf (czY w y t) + czY w y t) := hbr2
        _ ≤ (max 100 (max (8 * C0 + 2) (30 / czEps cf 2)))
              * (y * czSig t * czEps cf (czY w y t) + czY w y t) := by
            apply mul_le_mul_of_nonneg_right hCfge
            have h4 : 0 ≤ y * czSig t := mul_nonneg hy.le (czSig_nonneg t)
            exact add_nonneg (mul_nonneg h4 (czEps_pos cf _).le) hYpos.le
    · -- main case `r1 ≥ 2`
      have hr1ge2 : 2 ≤ r1 := by omega
      have hdec := rowMain_decomp (w := w) (y := y) (t := t) (r1 := r1) hw ht1 hr1pos hry
      have hA1 : |rowS1 t r1 (2 * czY w y t) - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
            - Real.log (2 * czY w y t / (r1 : ℝ)) * rowS0 t r1|
          ≤ C0 * czSig t * czEps c0 r1 := by
        have h := hcl1 t r1 (2 * czY w y t) hsq hr1ge2 (by linarith [hr1le])
        simpa only [rowS1, rowS0, rowCoef, czSig, czEps] using h
      have hA2 : |rowS0 t r1| ≤ C0 * czSig t * czEps c0 r1 := by
        have h := hcl2 t r1 hsq hr1ge2
        simpa only [rowS0, rowCoef, czSig, czEps] using h
      have hlog2 : Real.log (2 * czY w y t / (r1 : ℝ))
          = Real.log 2 + Real.log (czY w y t / (r1 : ℝ)) := by
        have h : 2 * czY w y t / (r1 : ℝ) = 2 * (czY w y t / (r1 : ℝ)) := by ring
        rw [h, Real.log_mul (by norm_num) (by positivity)]
      have hS1rel : rowS1 t r1 (czY w y t)
          = rowS1 t r1 (2 * czY w y t) - Real.log 2 * rowS0 t r1 := by
        have h1 : Real.log 2 * rowS0 t r1 = ∑ i ∈ Finset.Icc 1 r1, Real.log 2 * rowCoef t i := by
          rw [rowS0, Finset.mul_sum]
        rw [h1]
        unfold rowS1
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun r hr => ?_)
        have hr1' : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
        have h2Y : (0 : ℝ) < 2 * czY w y t := by linarith
        rw [Real.log_div h2Y.ne' hr0.ne', Real.log_div hYpos.ne' hr0.ne',
          Real.log_mul (by norm_num) hYpos.ne']
        ring
      have hrepr : rowS1 t r1 (czY w y t) = (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
          + Real.log (czY w y t / (r1 : ℝ)) * rowS0 t r1
          + (rowS1 t r1 (2 * czY w y t) - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
              - Real.log (2 * czY w y t / (r1 : ℝ)) * rowS0 t r1) := by
        rw [hS1rel, hlog2]
        ring
      have hmain : rowMain w y t r1 + y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
          = y * (-(rowS1 t r1 (2 * czY w y t) - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
                  - Real.log (2 * czY w y t / (r1 : ℝ)) * rowS0 t r1)
                + (1 - Real.log (czY w y t / (r1 : ℝ))) * rowS0 t r1
                + rowT2 y (czY w y t) t r1 + rowT3 y t r1)
              - rowX w y t r1 := by
        rw [hdec, hrepr]
        ring
      have hLbd : |Real.log (czY w y t / (r1 : ℝ))| ≤ 2 :=
        rowLog_abs_le_two hY1 hr1pos hr1ge hr1le
      have hb1 : |y * (rowS1 t r1 (2 * czY w y t) - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
            - Real.log (2 * czY w y t / (r1 : ℝ)) * rowS0 t r1)|
          ≤ y * (C0 * czSig t * czEps c0 r1) := by
        rw [abs_mul, abs_of_pos hy]
        exact mul_le_mul_of_nonneg_left hA1 hy.le
      have hb2 : |y * ((1 - Real.log (czY w y t / (r1 : ℝ))) * rowS0 t r1)|
          ≤ y * (3 * (C0 * czSig t * czEps c0 r1)) := by
        rw [abs_mul, abs_of_pos hy]
        apply mul_le_mul_of_nonneg_left _ hy.le
        rw [abs_mul]
        have h1 : |1 - Real.log (czY w y t / (r1 : ℝ))| ≤ 3 := by
          have h2 := abs_add_le (1 : ℝ) (-(Real.log (czY w y t / (r1 : ℝ))))
          rw [← sub_eq_add_neg, abs_neg, abs_one] at h2
          linarith
        have h3 : 0 ≤ C0 * czSig t * czEps c0 r1 := by
          have h4 : 0 ≤ czSig t := czSig_nonneg t
          have h5 : 0 ≤ czEps c0 r1 := (czEps_pos c0 r1).le
          positivity
        nlinarith [h1, hA2, abs_nonneg (rowS0 t r1), h3]
      have hb3 : |y * rowT2 y (czY w y t) t r1| ≤ 2 * 10 * czY w y t :=
        rowT2_bound hw hy ht1 hry' hS (by norm_num)
      have hb4 : |y * rowT3 y t r1| ≤ 20 * czY w y t := rowT3_bound hy hry' hYy hr1le
      have hb5 : |rowX w y t r1| ≤ 5 * 10 * czY w y t := rowX_bound hw ht1 hry' hS (by norm_num)
      have htri := abs_row_tri (y := y)
        (e1 := rowS1 t r1 (2 * czY w y t) - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
          - Real.log (2 * czY w y t / (r1 : ℝ)) * rowS0 t r1)
        (e2 := (1 - Real.log (czY w y t / (r1 : ℝ))) * rowS0 t r1)
        (e3 := rowT2 y (czY w y t) t r1) (e4 := rowT3 y t r1) (e5 := rowX w y t r1)
      have hbig : |rowMain w y t r1 + y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))|
          ≤ 4 * C0 * y * czSig t * czEps c0 r1 + 90 * czY w y t := by
        rw [hmain]
        linarith [htri, hb1, hb2, hb3, hb4, hb5]
      have hepsc : czEps c0 r1 ≤ 2 * czEps cf (czY w y t) := by
        have h1 := czEps_compare (c := eta) (Y := czY w y t) heta_pos heta_le_one hY1 hr1pos
          (by linarith [hr1ge])
        have h2 : czEps c0 r1 ≤ czEps eta r1 := czEps_le_of_le_rate heta_le_c0
        have h3 : czEps (eta / 2) (czY w y t) = czEps cf (czY w y t) := by rw [hcf_def]
        linarith [h1, h2, h3]
      have hσ0 : 0 ≤ czSig t := czSig_nonneg t
      have hfin1 : |rowMain w y t r1 + y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))|
          ≤ 8 * C0 * y * czSig t * czEps cf (czY w y t) + 90 * czY w y t := by
        have hcoe : 0 ≤ 4 * C0 * y * czSig t := by positivity
        have h1 := mul_le_mul_of_nonneg_left hepsc hcoe
        linarith [hbig, h1]
      have h8 : 8 * C0 ≤ max 100 (max (8 * C0 + 2) (30 / czEps cf 2)) := by
        have h1 : 8 * C0 ≤ 8 * C0 + 2 := by linarith
        have h2 : 8 * C0 + 2 ≤ max (8 * C0 + 2) (30 / czEps cf 2) := le_max_left _ _
        have h3 : max (8 * C0 + 2) (30 / czEps cf 2)
            ≤ max 100 (max (8 * C0 + 2) (30 / czEps cf 2)) := le_max_right _ _
        linarith
      have h90 : 90 ≤ max 100 (max (8 * C0 + 2) (30 / czEps cf 2)) :=
        le_trans (by norm_num) (le_max_left _ _)
      have hYe : 0 ≤ czY w y t := hYpos.le
      calc |rowMain w y t r1 + y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))|
          ≤ 8 * C0 * y * czSig t * czEps cf (czY w y t) + 90 * czY w y t := hfin1
        _ ≤ (max 100 (max (8 * C0 + 2) (30 / czEps cf 2)))
              * (y * czSig t * czEps cf (czY w y t) + czY w y t) := by
            have hε0 : 0 ≤ czEps cf (czY w y t) := (czEps_pos cf (czY w y t)).le
            have hx : 0 ≤ y * czSig t * czEps cf (czY w y t) := by
              have h1 : 0 ≤ czSig t := czSig_nonneg t
              have h2 : 0 ≤ czEps cf (czY w y t) := hε0
              positivity
            have hA := mul_le_mul_of_nonneg_right h8 hx
            have hB := mul_le_mul_of_nonneg_right h90 hYe
            rw [mul_add]
            linarith [hA, hB]
  calc |czRowSum w y N q t + y * (Real.pi ^ 2 / 6) * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|
      = |((t : ℝ) / kap t) * ((ArithmeticFunction.moebius t : ℤ) : ℝ)
          * (rowMain w y t r1 + y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ)))| := by rw [hkey]
    _ = |((t : ℝ) / kap t)| * |((ArithmeticFunction.moebius t : ℤ) : ℝ)|
          * |rowMain w y t r1 + y * (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))| := by
        rw [abs_mul, abs_mul]
    _ ≤ ((t : ℝ) / kap t) * 1
          * ((max 100 (max (8 * C0 + 2) (30 / czEps cf 2)))
              * (y * czSig t * czEps cf (czY w y t) + czY w y t)) := by
        rw [abs_of_nonneg htknn]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hμ1 htknn) hbracket
          (abs_nonneg _) (mul_nonneg htknn zero_le_one)
    _ = (max 100 (max (8 * C0 + 2) (30 / czEps cf 2))) * ((t : ℝ) / kap t)
          * (y * czSig t * czEps cf (czY w y t) + czY w y t) := by ring

end

end Work.ZeroDensity.Jutila.LzDiffAux
