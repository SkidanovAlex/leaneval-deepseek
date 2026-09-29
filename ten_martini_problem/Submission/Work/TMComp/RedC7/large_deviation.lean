import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.continuous_frob_iterC
import Submission.Work.TMC7Core.LDT
import Submission.Work.TMC7Core.Fourier.ldt_setup
import Submission.Work.TMC7Core.Fourier.ldt_moving
import Submission.Work.TMC7Core.Fourier.ldt_fourier_decay
import Submission.Work.TMComp.RedC7.arith_slack
import Submission.Work.TMComp.RedC7.lev_numeric
import Submission.Work.TMComp.RedC7.trig_own
import Submission.Work.TMC7Core.Fourier.fejer_bound
import Submission.Work.TMC7Core.Fourier.tail_L2_own
import Submission.Work.TMC7Core.Fourier.tail_L2_aux
import Submission.Work.TMC7Core.Fourier.trig_own
import Submission.Work.TMC7Core.Fourier.markov_deviation
import Submission.Work.TMC7Core.Fourier.ldt_harith

set_option maxHeartbeats 2000000

/-!
# TMC7Core: the large deviation theorem for the almost Mathieu cocycle

For every coupling `lam` and every energy `E₀` there are `c, C, r > 0` such that the
Bourgain–Jitomirskaya large deviation estimate holds uniformly for energies in a
neighbourhood of `E₀` (the "Fourier decay + Fejér average + arithmetic" input of
[BJ] Lemma 4, arXiv:math-ph/0110040).

The finite-scale exponent `uAvg` is compared with its Fejér (moving) average along the
orbit of the rotation; the moving average has Fourier multiplier the Fejér kernel, which
decays like `1/(1 + (R·dist)²)`.  Frequencies below a cutoff `K` are controlled by the
Fourier decay `|û(k)| ≤ 1/|k|` together with the arithmetic of the rational approximation
`|α - a/q| < 1/q²` (`arith_core`, assembled in `trig_own`), and the frequencies above the
cutoff by Parseval (`tail_L2_own`).  The constants come
with a large slack: `C` is huge, `c` is small.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

open Work.TMC7Core Work.TMC7Core.Fourier

noncomputable section

namespace Work.TMComp.RedC7

/-- The `0`-th interval Fourier coefficient of `uAvg` is `lyapAvg`. -/
theorem fourierCoeffOn_zero_uAvg (α lam : ℝ) (E : ℝ) (N : ℕ) :
    fourierCoeffOn (by norm_num : (0:ℝ) < 1) (fun x => ((uAvg α lam (E:ℂ) N x : ℝ) : ℂ)) 0
      = ((lyapAvg α lam (E:ℂ) N : ℝ) : ℂ) := by
  rw [show fourierCoeffOn (by norm_num : (0:ℝ) < 1)
        (fun x => ((uAvg α lam (E:ℂ) N x : ℝ) : ℂ)) 0
      = ∫ x in (0:ℝ)..1, ((uAvg α lam (E:ℂ) N x : ℝ) : ℂ) from by
    rw [fourierCoeffOn_eq_integral_exp]
    apply intervalIntegral.integral_congr
    intro x _
    simp]
  rw [intervalIntegral.integral_ofReal, Work.TMC7Core.lyapAvg_eq_integral_uAvg]

theorem large_deviation (lam E₀ : ℝ) : ∃ c C r : ℝ, 0 < c ∧ 1 ≤ C ∧ 0 < r ∧ HasLDTOn lam (Set.Icc (E₀ - r) (E₀ + r)) c C := by
  set lamE : ℝ := |E₀| + 2 * |lam| + 3 with hlamE
  have hlamE1 : 1 ≤ lamE := by rw [hlamE]; linarith [abs_nonneg E₀, abs_nonneg lam]
  have hlamElog : 0 ≤ Real.log lamE := Real.log_nonneg hlamE1
  set Cv : ℝ := 1000000 * (Real.log lamE + 2) with hCv
  have hCv1 : 1 ≤ Cv := by rw [hCv]; nlinarith
  have hCv_big : 808 * Real.log lamE ≤ Cv := by rw [hCv]; nlinarith
  have hCv_864 : 864 ≤ Cv := by rw [hCv]; nlinarith
  have hCv_9600 : 9600 ≤ Cv := by rw [hCv]; nlinarith
  refine ⟨(1:ℝ)/2000, Cv, 1, by norm_num, hCv1, by norm_num, ?_⟩
  refine ⟨by norm_num, hCv1, ?_⟩
  intro E hE α a q N κ hq hκ0 hκ1 hcop hα hqC hNC
  -- (A) basic facts
  have hE' : |E| ≤ |E₀| + 1 := by
    rcases hE with ⟨h1, h2⟩
    have h3 : E₀ ≤ |E₀| := le_abs_self E₀
    have h4 : -|E₀| ≤ E₀ := neg_abs_le E₀
    rw [abs_le]; constructor <;> linarith
  have hFE : ldtF lam E ≤ lamE := by
    rw [ldtF, hlamE]; linarith [abs_nonneg lam]
  have hlogFE : Real.log (ldtF lam E) ≤ Real.log lamE := Real.log_le_log (ldtF_pos lam E) hFE
  have hN1 : 1 ≤ N := by
    have h1 : (1:ℝ) ≤ Cv * (κ^2)⁻¹ * (q:ℝ) := by
      have hk2 : (1:ℝ) ≤ (κ^2)⁻¹ :=
        (one_le_inv₀ (show (0:ℝ) < κ^2 by positivity)).mpr (by nlinarith)
      have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      have h2 : (1:ℝ) ≤ Cv * (κ^2)⁻¹ := by
        calc (1:ℝ) = 1 * 1 := by ring
          _ ≤ Cv * (κ^2)⁻¹ := mul_le_mul hCv1 hk2 (by norm_num) (by linarith [hCv1])
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ Cv * (κ^2)⁻¹ * (q:ℝ) := mul_le_mul h2 hq1 (by norm_num) (by positivity)
    have h2 : (1:ℝ) ≤ (N:ℝ) := le_trans h1 hNC
    exact_mod_cast h2
  -- (B) parameters
  let s : ℕ := ⌈100 / Real.sqrt κ⌉₊
  have hs1 : 1 ≤ s := show 1 ≤ ⌈100 / Real.sqrt κ⌉₊ from
    Nat.one_le_ceil_iff.mpr (by exact div_pos (by norm_num) (Real.sqrt_pos.mpr hκ0))
  have hsge : 100 / Real.sqrt κ ≤ (s:ℝ) := show 100 / Real.sqrt κ ≤ (⌈100 / Real.sqrt κ⌉₊ : ℝ) from
    Nat.le_ceil _
  have hsle : (s:ℝ) ≤ 100 / Real.sqrt κ + 1 := show (⌈100 / Real.sqrt κ⌉₊ : ℝ) ≤ 100 / Real.sqrt κ + 1 from
    le_of_lt (Nat.ceil_lt_add_one (le_of_lt (div_pos (by norm_num) (Real.sqrt_pos.mpr hκ0))))
  have hspos : (0:ℝ) < (s:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs1)
  have hsk : (100:ℝ) ≤ (s:ℝ) * Real.sqrt κ := by
    have h1 : Real.sqrt κ * (100 / Real.sqrt κ) ≤ Real.sqrt κ * (s:ℝ) :=
      mul_le_mul_of_nonneg_left hsge (Real.sqrt_nonneg κ)
    have h2 : Real.sqrt κ * (100 / Real.sqrt κ) = 100 := by
      rw [mul_comm, div_mul_cancel₀]
      exact ne_of_gt (Real.sqrt_pos.mpr hκ0)
    linarith
  have hs100 : 100 ≤ (s:ℝ) := by
    have h1 : Real.sqrt κ ≤ 1 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hκ1
    nlinarith [hsk, h1, hspos]
  have hsk2 : (100:ℝ)^2 ≤ (s:ℝ)^2 * κ := by
    nlinarith [hsk, Real.sq_sqrt hκ0.le, sq_nonneg ((s:ℝ) * Real.sqrt κ - 100)]
  let R : ℕ := q * s
  have hR1 : 1 ≤ R := show 1 ≤ q * s from by simpa using Nat.mul_le_mul hq hs1
  have hRq : (R:ℝ) = (q:ℝ) * (s:ℝ) := show ((q * s : ℕ) : ℝ) = (q:ℝ) * (s:ℝ) by push_cast; ring
  let K : ℕ := ⌈8 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2⌉₊
  have hK1 : 1 ≤ K := show 1 ≤ ⌈8 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2⌉₊ from
    Nat.one_le_ceil_iff.mpr (by positivity)
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK1)
  have hKge : 8 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2 ≤ (K:ℝ) :=
    show 8 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2 ≤ (⌈8 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2⌉₊ : ℝ) from
      Nat.le_ceil _
  have hKle : (K:ℝ) < 8 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2 + 1 :=
    show (⌈8 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2⌉₊ : ℝ) <
        8 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2 + 1 from
      Nat.ceil_lt_add_one (by positivity)
  -- (C) the function and its periodicity
  set g : ℝ → ℂ := fun x => ((uAvg α lam (E:ℂ) N x : ℝ) : ℂ) with hgdef
  have hgper : ∀ x : ℝ, g (x + 1) = g x := by
    intro x; simp only [hgdef]; rw [uAvg_period]
  have hfrobpos : ∀ x : ℝ, 0 < frob (iterC α lam (E:ℂ) N x) := fun x =>
    lt_of_lt_of_le (by norm_num)
      (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one (det_iterC α lam (E:ℂ) N x))
  have hgov : Continuous (fun x : ℝ => uAvg α lam (E:ℂ) N x) := by
    change Continuous (fun x : ℝ => Real.log (frob (iterC α lam (E:ℂ) N x)) / (N:ℝ))
    exact ((Work.TMC7Core.Cocycle.continuous_frob_iterC α lam (E:ℂ) N).log
      (fun x => ne_of_gt (hfrobpos x))).div_const _
  have hgcont : Continuous g := by
    rw [hgdef]
    exact Complex.continuous_ofReal.comp hgov
  have hg2 : MemLp g 2 (volume.restrict (Set.Ioc 0 1)) := by
    refine MemLp.of_bound hgcont.aestronglyMeasurable (Real.log lamE) ?_
    filter_upwards with x
    simp only [hgdef]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (uAvg_nonneg α lam (E:ℂ) N x)]
    exact le_trans (uAvg_le_ldtF α lam E N hN1 x) hlogFE
  -- (D) the two kernel estimates
  have hfej : ∀ R' : ℕ, 1 ≤ R' → ∀ θ : ℝ,
      fejerKer R' θ ≤ 2 / (1 + ((R':ℝ) * fracDist θ) ^ 2) := fejer_bound
  have hdec : ∀ k : ℤ, k ≠ 0 → ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) g k‖ ≤ 1 / |(k:ℝ)| := by
    intro k hk
    rw [fourierCoeffOn_eq_integral_exp (f := g) (m := k)]
    have hI : (∫ x in (0:ℝ)..1, Complex.exp (-(2*Real.pi*Complex.I*((k:ℝ):ℂ)*↑x)) * g x)
        = ∫ x in (0:ℝ)..1, ((uAvg α lam (E:ℂ) N x : ℝ) : ℂ) *
            Complex.exp (-(2*Real.pi*Complex.I*((k:ℝ):ℂ)*↑x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [hgdef]
      ring
    rw [hI]
    exact ldt_fourier_decay α lam E N hN1 k hk
  -- (E) arithmetic estimates
  have hCvq : Cv ≤ (q:ℝ) * κ^2 := by
    have h4 := mul_le_mul_of_nonneg_right hqC (by positivity : (0:ℝ) ≤ κ^2)
    rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt (by positivity : (0:ℝ) < κ^2)), mul_one] at h4
  have hqinv : (1:ℝ) / (q:ℝ) ≤ κ^2 / Cv := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hCvq]
  have hexp1 : (1:ℝ) ≤ Real.exp (1/1000 * κ * (q:ℝ)) := Real.one_le_exp (by positivity)
  have hKle9 : (K:ℝ) ≤ 9 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2 := by
    have h1 : (1:ℝ) ≤ Real.exp (1/1000 * κ * (q:ℝ)) / κ^2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hexp1, hκ0, hκ1]
    have h2 : 8 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2 + 1
        ≤ 9 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2 := by
      have h4 : (8:ℝ) * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2
          + Real.exp (1/1000 * κ * (q:ℝ)) / κ^2
          = 9 * Real.exp (1/1000 * κ * (q:ℝ)) / κ^2 := by ring
      linarith [h1, h4]
    linarith [hKle, h2]
  have hCvq' : Cv ≤ (q:ℝ) * κ^2 := by
    have h4 := mul_le_mul_of_nonneg_right hqC (show (0:ℝ) ≤ κ^2 by positivity)
    rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt (show (0:ℝ) < κ^2 by positivity)), mul_one] at h4
  have harith : (∑ k ∈ Finset.Icc 1 K,
        (1 / (k : ℝ)) * (1 + ((s : ℝ) * (q : ℝ) * fracDist ((k : ℝ) * α)) ^ 2)⁻¹)
      ≤ 50 / ((s:ℝ)^2) + 2 / (q:ℝ) + 12 * (1/(q:ℝ)) * (1 + Real.log (1 + (K:ℝ)/(q:ℝ))) :=
    Work.TMComp.RedC7.arith_slack α a q s K hq hs1 hcop hα
  -- (F) the pointwise bound on the truncated Fourier sum
  set M : ℝ → ℂ := fun x => ∑ k ∈ (Finset.Icc (-(K:ℤ)) (K:ℤ)).filter (fun k => k ≠ 0),
      fourierCoeffOn (by norm_num : (0:ℝ) < 1) g k * (fejerKer R ((k:ℝ)*α) : ℂ) *
        Complex.exp (2*Real.pi*Complex.I*(k:ℝ)*x) with hMdef
  have hMbound : ∀ x : ℝ, ‖M x‖ ≤ κ/4 := by
    intro x
    have h1 := Work.TMComp.RedC7.trig_bound_of_arith
      (50 / ((s:ℝ)^2) + 2 / (q:ℝ) + 12 * (1/(q:ℝ)) * (1 + Real.log (1 + (K:ℝ)/(q:ℝ))))
      α a q s K hq hs1 hK1
      (fun k => fourierCoeffOn (by norm_num : (0:ℝ) < 1) g k) (fun k hk => hdec k hk) hfej hcop hα
      harith x
    have h2 : 4 * (50/((s:ℝ)^2) + 2/(q:ℝ) + 12 * (1/(q:ℝ)) * (1 + Real.log (1 + (K:ℝ)/(q:ℝ)))) ≤ κ/4 := by
      have hKl' : (K:ℝ) < 8 * Real.exp (κ * (q:ℝ) / 1000) / κ^2 + 1 := by
        have h := hKle
        rw [show (1:ℝ)/1000 * κ * (q:ℝ) = κ * (q:ℝ) / 1000 by ring] at h
        exact h
      have hsk2' : (10000 : ℝ) ≤ (s:ℝ) ^ 2 * κ := by
        have h := hsk2
        norm_num at h
        exact h
      exact Work.TMComp.RedC7.app_numeric (s:ℝ) (q:ℝ) κ Cv K hsk2' hκ0 hκ1
        (by exact_mod_cast (by omega : 0 < q)) hCv_864 hCvq' hKl'
    exact le_trans h1 h2
  -- (G) the telescoping bound
  have htel : ∀ x : ℝ, ‖g x - mAve g α R x‖ ≤ κ/4 := by
    intro x
    have h1 := uAvg_mAve_le α lam E N hN1 R hR1 x
    have h1' : ‖((uAvg α lam (E:ℂ) N x : ℝ) : ℂ) - mAve g α R x‖
        ≤ 2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ) := by
      simpa only [hgdef] using h1
    have hsκ : (s:ℝ) * κ ≤ 101 := by
      have h2 : (100 / Real.sqrt κ + 1) * κ = 100 * Real.sqrt κ + κ := by
        rw [add_mul, one_mul]
        congr 1
        rw [div_mul_eq_mul_div, div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hκ0))]
        nlinarith [Real.sq_sqrt hκ0.le]
      have h1 : (s:ℝ) * κ ≤ (100 / Real.sqrt κ + 1) * κ := mul_le_mul_of_nonneg_right hsle hκ0.le
      rw [h2] at h1
      have h3 : Real.sqrt κ ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hκ1
      nlinarith [h1, h3, hκ0, hκ1]
    have hNpos : (0:ℝ) < (N:ℝ) := by
      have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
      linarith
    have hCvpos : (0:ℝ) < Cv := by linarith
    have hRN : (R:ℝ)/(N:ℝ) ≤ (s:ℝ) * κ^2 / Cv := by
      have hqCv : (q:ℝ) * Cv ≤ (N:ℝ) * κ^2 := by
        have h4 := mul_le_mul_of_nonneg_right hNC (show (0:ℝ) ≤ κ^2 by positivity)
        have h5 : Cv * (κ^2)⁻¹ * (q:ℝ) * κ^2 = Cv * (q:ℝ) := by field_simp
        rw [h5] at h4
        linarith
      rw [hRq, div_le_div_iff₀ hNpos hCvpos]
      nlinarith [hqCv, hspos]
    have hkey : 2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ) ≤ κ/4 := by
      have h4 : 2 * (R:ℝ) * Real.log (ldtF lam E) / (N:ℝ)
          = 2 * ((R:ℝ)/(N:ℝ)) * Real.log (ldtF lam E) := by
        field_simp
      rw [h4]
      have hFnn : 0 ≤ Real.log (ldtF lam E) := Real.log_nonneg (one_le_ldtF lam E)
      have hBnn : 0 ≤ (s:ℝ) * κ^2 / Cv := by positivity
      have h5 : 2 * ((R:ℝ)/(N:ℝ)) * Real.log (ldtF lam E)
          ≤ 2 * ((s:ℝ)*κ^2/Cv) * Real.log lamE := by
        have hstep : ((R:ℝ)/(N:ℝ)) * Real.log (ldtF lam E)
            ≤ ((s:ℝ)*κ^2/Cv) * Real.log lamE :=
          (mul_le_mul_of_nonneg_right hRN hFnn).trans
            (mul_le_mul_of_nonneg_left hlogFE hBnn)
        linarith [hstep]
      have h8 : 2 * ((s:ℝ)*κ^2/Cv) * Real.log lamE ≤ κ/4 := by
        have h9 : 2 * ((s:ℝ)*κ^2/Cv) * Real.log lamE
            = (2 * (s:ℝ) * κ^2 * Real.log lamE)/Cv := by
          field_simp
        rw [h9, div_le_iff₀ hCvpos]
        have h2 : (s:ℝ) * κ^2 ≤ 101 * κ := by
          have h2a : (s:ℝ) * κ * κ ≤ 101 * κ := mul_le_mul_of_nonneg_right hsκ hκ0.le
          calc (s:ℝ) * κ^2 = (s:ℝ) * κ * κ := by ring
            _ ≤ 101 * κ := h2a
        have h3 : 2 * (s:ℝ) * κ^2 * Real.log lamE ≤ 202 * κ * Real.log lamE := by
          have h3a : 2 * ((s:ℝ) * κ^2) * Real.log lamE ≤ 2 * (101 * κ) * Real.log lamE :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) hlamElog
          linarith [h3a]
        have h4' : 202 * κ * Real.log lamE ≤ κ/4 * Cv := by
          have h4a := mul_le_mul_of_nonneg_left hCv_big hκ0.le
          linarith [h4a]
        linarith [h3, h4']
      linarith [h5, h8]
    linarith [h1', hkey]
  -- (H) the tail and the measure bound
  set tail : ℝ → ℂ := fun x => mAve g α R x - fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0 - M x
    with htaildef
  have htail2 : ∫ x in (0:ℝ)..1, ‖tail x‖ ^ 2 ≤ 2/(K:ℝ) := by
    have h1 := tail_L2b g hgper α R hR1 K hK1 hg2 hdec
    rw [htaildef]
    exact h1
  have htailcont : Continuous tail := by
    have h1 : Continuous (fun x : ℝ => mAve g α R x) := by
      rw [show (fun x : ℝ => mAve g α R x)
          = (fun x : ℝ => ((R:ℂ)^2)⁻¹ * ∑ j ∈ Finset.range R, ∑ j' ∈ Finset.range R,
              g (x + ((j:ℝ) - (j':ℝ)) * α)) from rfl]
      refine continuous_const.mul ?_
      refine continuous_finset_sum _ (fun j _ => ?_)
      refine continuous_finset_sum _ (fun j' _ => ?_)
      exact hgcont.comp (by fun_prop)
    have h2 : Continuous M := by
      rw [hMdef]
      refine continuous_finset_sum _ (fun k _ => ?_)
      exact (continuous_const.mul continuous_const).mul (by fun_prop)
    rw [htaildef]
    exact (h1.sub continuous_const).sub h2
  have hSsub : {x : ℝ | x ∈ Set.Icc 0 1 ∧ κ < |uAvg α lam (E:ℂ) N x - lyapAvg α lam (E:ℂ) N|}
      ⊆ Set.Icc (0:ℝ) 1 := fun x hx => hx.1
  have hSlarge : ∀ x ∈ {x : ℝ | x ∈ Set.Icc 0 1 ∧
      κ < |uAvg α lam (E:ℂ) N x - lyapAvg α lam (E:ℂ) N|}, (κ/2)^2 ≤ ‖tail x‖^2 := by
    intro x hx
    have h1 : |uAvg α lam (E:ℂ) N x - lyapAvg α lam (E:ℂ) N|
        = ‖g x - fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0‖ := by
      have hq' : g x - fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0
          = ((uAvg α lam (E:ℂ) N x - lyapAvg α lam (E:ℂ) N : ℝ) : ℂ) := by
        rw [hgdef, fourierCoeffOn_zero_uAvg]
        push_cast
        ring
      rw [hq', Complex.norm_real, Real.norm_eq_abs]
    have h2 : g x - fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0
        = (g x - mAve g α R x) + M x + tail x := by
      rw [htaildef]; ring
    have h3 : ‖g x - mAve g α R x‖ ≤ κ/4 := htel x
    have h4 : ‖M x‖ ≤ κ/4 := hMbound x
    have h5 : ‖g x - fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0‖
        ≤ ‖g x - mAve g α R x‖ + ‖M x‖ + ‖tail x‖ := by
      rw [h2]
      calc ‖(g x - mAve g α R x) + M x + tail x‖
          ≤ ‖(g x - mAve g α R x) + M x‖ + ‖tail x‖ := norm_add_le _ _
        _ ≤ (‖g x - mAve g α R x‖ + ‖M x‖) + ‖tail x‖ := by
            linarith [norm_add_le (g x - mAve g α R x) (M x)]
    have h6 : κ < ‖g x - fourierCoeffOn (by norm_num : (0:ℝ) < 1) g 0‖ := by
      rw [← h1]; exact hx.2
    have h7 : κ/2 ≤ ‖tail x‖ := by linarith
    have h8 : 0 ≤ κ/2 := by linarith
    exact pow_le_pow_left₀ h8 h7 2
  have hmain := markov_deviation (fun x => ‖tail x‖^2) (htailcont.norm.pow 2)
    (fun x => sq_nonneg _) {x : ℝ | x ∈ Set.Icc 0 1 ∧
      κ < |uAvg α lam (E:ℂ) N x - lyapAvg α lam (E:ℂ) N|} hSsub ((κ/2)^2)
    (by positivity) hSlarge (K:ℝ) hKpos htail2
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have h8' : 2 / ((K:ℝ) * (κ/2) ^ 2) = 8 / ((K:ℝ) * κ ^ 2) := by
    field_simp; ring
  rw [h8']
  have h10 : (8:ℝ) * Real.exp ((1/1000) * κ * (q:ℝ)) ≤ (K:ℝ) * κ ^ 2 := by
    have h11 := mul_le_mul_of_nonneg_right hKge (show (0:ℝ) ≤ κ ^ 2 by positivity)
    rwa [div_mul_cancel₀ _ (ne_of_gt (by positivity : (0:ℝ) < κ ^ 2))] at h11
  have hpos : 0 < (K:ℝ) * κ ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  have hexp : Real.exp (-((1/1000) * κ * (q:ℝ))) * Real.exp ((1/1000) * κ * (q:ℝ)) = 1 := by
    rw [← Real.exp_add]; simp
  have h13 : Real.exp (-((1/1000) * κ * (q:ℝ))) ≤ Real.exp (-((1:ℝ)/2000 * κ * (q:ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
    nlinarith [hκ0.le, hq0]
  calc (8:ℝ) = 8 * (Real.exp (-((1/1000) * κ * (q:ℝ))) * Real.exp ((1/1000) * κ * (q:ℝ))) := by
        rw [hexp, mul_one]
    _ = Real.exp (-((1/1000) * κ * (q:ℝ))) * (8 * Real.exp ((1/1000) * κ * (q:ℝ))) := by ring
    _ ≤ Real.exp (-((1/1000) * κ * (q:ℝ))) * ((K:ℝ) * κ ^ 2) :=
        mul_le_mul_of_nonneg_left h10 (Real.exp_pos _).le
    _ ≤ Real.exp (-((1:ℝ)/2000 * κ * (q:ℝ))) * ((K:ℝ) * κ ^ 2) :=
        mul_le_mul_of_nonneg_right h13 hpos.le

end Work.TMComp.RedC7

end
