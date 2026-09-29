import Mathlib
import Submission.Work.TMC7Core.Scale.scale_step
import Submission.Work.TMC7Core.Scale.prop9_aux
import Submission.Work.TMC7Core.LDT

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini
open Work.TMC7Core.Lyap

namespace Work.TMC7Core.Scale

/-- **Upper half of the `ψ`-estimate.**  The one-scale step `scale_step` controls

`L_{mN} + (1 - 2/m) L_N - (2 - 2/m) L_{2N} = A`,

i.e. the *triple* of scales `(mN, N, 2N)`.  Rewriting

`L_{mN} + L_N - 2 L_{2N} = A + (2/m) (L_N - L_{2N})`

and using `lyap ≤ L_{mN}` (`prop9_aux.lyap_le_lyapAvg`) together with `L_N ≤ C₀`
(`HasLEBound`) and `L_{2N} ≥ 0` gives the upper bound on the `ψ`-quantity
`L + L_N - 2 L_{2N}` with the extra term `2 C₀ / m`, which is exactly what the
halving/bootstrap step of the assembly consumes (it is sent to `0` by taking `m` large,
and `m` is thereby the free parameter of the final argument). -/
theorem psi_upper (lam : ℝ) (K : Set ℝ) (c C C₀ : ℝ) (hLDT : HasLDTOn lam K c C)
    (hC₀ : HasLEBound lam K C₀) (hc1 : c ≤ 1) (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 100)
    (E : ℝ) (hE : E ∈ K) (α : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (hcop : Nat.Coprime (Int.natAbs a) q) (hqC : C * (κ ^ 2)⁻¹ ≤ (q : ℝ))
    (hα : |α - (a : ℝ) / (q : ℝ)| < 1 / ((q : ℝ) ^ 2)) (N : ℕ)
    (hN : C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (N : ℝ))
    (hL : 100 * κ < lyap α lam (E : ℂ))
    (h2N : (9 / 10) * lyapAvg α lam (E : ℂ) N < lyapAvg α lam (E : ℂ) (2 * N))
    (m : ℕ) (hm : 3 ≤ m) (hmq : (m : ℝ) < Real.exp (c * κ * (q : ℝ) / 2)) :
    lyap α lam (E : ℂ) + lyapAvg α lam (E : ℂ) N - 2 * lyapAvg α lam (E : ℂ) (2 * N)
      ≤ (12 * C₀ + 1000) * Real.exp (-(c * κ * (q : ℝ) / 4)) + 2 * C₀ / (m : ℝ) := by
  have hC : 1 ≤ C := hLDT.2.1
  have hC0pos : 0 < C₀ := hC₀.1
  have hLEB := hC₀.2
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  -- `κ ≤ 1/100` gives `(κ^2)⁻¹ ≥ 1`
  have hκ2inv1 : (1 : ℝ) ≤ (κ ^ 2)⁻¹ := by
    have hpos : (0 : ℝ) < κ ^ 2 := by positivity
    have hle : κ ^ 2 ≤ 1 := by nlinarith [hκ.le, hκ1]
    have h := one_div_le_one_div_of_le hpos hle
    simpa using h
  -- hence `C (κ^2)⁻¹ q ≥ 1`, so `hN` forces `1 ≤ N`
  have hbase : (1 : ℝ) ≤ C * (κ ^ 2)⁻¹ * (q : ℝ) := by
    have h1 : (1 : ℝ) ≤ C * (κ ^ 2)⁻¹ := by
      have h := mul_le_mul hC hκ2inv1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ C)
      simpa using h
    have h2 := mul_le_mul h1 hq1 (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ C * (κ ^ 2)⁻¹)
    simpa using h2
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := le_trans hbase hN
    exact_mod_cast this
  have hmN1 : 1 ≤ m * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h2N1 : 1 ≤ 2 * N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  -- `L_N ≤ C₀` from the standing bound `u_N ≤ C₀`
  have hLNle : lyapAvg α lam (E : ℂ) N ≤ C₀ := by
    rw [lyapAvg, div_le_iff₀ hNpos, mul_comm C₀ (N : ℝ)]
    have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        Real.log (frob (iterC α lam (E : ℂ) N x)) ≤ (N : ℝ) * C₀ := by
      intro x _
      rw [log_frob_eq_mul_uAvg α lam (E : ℂ) hN1]
      exact mul_le_mul_of_nonneg_left (hLEB E hE α N x) (by positivity)
    have hc : IntervalIntegrable (fun x : ℝ => Real.log (frob (iterC α lam (E : ℂ) N x)))
        volume (0 : ℝ) 1 :=
      (continuous_log_frob_iterC α lam (E : ℂ) N).intervalIntegrable _ _
    have hg : IntervalIntegrable (fun _ : ℝ => (N : ℝ) * C₀) volume (0 : ℝ) 1 :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hc hg hpt
    simpa using hmono
  -- `L_{2N} ≥ 0`
  have hL2Nnn : 0 ≤ lyapAvg α lam (E : ℂ) (2 * N) := by
    have h := lyapAvg_nonneg' α lam (E : ℂ) (2 * N - 1)
    rwa [Nat.sub_add_cancel h2N1] at h
  -- `lyap ≤ L_{mN}`
  have hlyap : lyap α lam (E : ℂ) ≤ lyapAvg α lam (E : ℂ) (m * N) :=
    lyap_le_lyapAvg α lam (E : ℂ) hmN1
  -- the one-scale step
  have hss := scale_step lam K c C C₀ hLDT hC₀ hc1 κ hκ hκ1 E hE α a q hq hcop hqC hα N hN hL
    h2N m hm hmq
  have hA : lyapAvg α lam (E : ℂ) (m * N) + (1 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
      - (2 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N)
      ≤ (12 * C₀ + 1000) * Real.exp (-(c * κ * (q : ℝ) / 4)) :=
    le_of_lt (lt_of_le_of_lt (le_abs_self _) hss)
  have hLNsub : lyapAvg α lam (E : ℂ) N - lyapAvg α lam (E : ℂ) (2 * N) ≤ C₀ := by linarith
  have hstep : (2 / (m : ℝ)) * (lyapAvg α lam (E : ℂ) N - lyapAvg α lam (E : ℂ) (2 * N))
      ≤ 2 * C₀ / (m : ℝ) := by
    have h2m : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left hLNsub h2m
    have heq : (2 / (m : ℝ)) * C₀ = 2 * C₀ / (m : ℝ) := by ring
    rwa [heq] at h
  have hid : lyapAvg α lam (E : ℂ) (m * N) + lyapAvg α lam (E : ℂ) N
        - 2 * lyapAvg α lam (E : ℂ) (2 * N)
      = (lyapAvg α lam (E : ℂ) (m * N) + (1 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) N
          - (2 - 2 / (m : ℝ)) * lyapAvg α lam (E : ℂ) (2 * N))
        + (2 / (m : ℝ)) * (lyapAvg α lam (E : ℂ) N - lyapAvg α lam (E : ℂ) (2 * N)) := by
    ring
  linarith [hlyap, hA, hstep, hid]

end Work.TMC7Core.Scale
