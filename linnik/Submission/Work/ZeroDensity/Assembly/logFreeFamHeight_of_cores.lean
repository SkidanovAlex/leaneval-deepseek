import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.LinnikAreas.Setup
import Submission.Work.ZeroDensity.Basic

namespace Work.ZeroDensity.Assembly

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- Arithmetic core of the three-way split: if `e ≤ (5/2)(1-σ)` and `e ≤ 3/2` then
`C₀ (qT)^e ≤ C e^{(5/2)(1-σ) log q} T^{3/2}` for `q ≥ 2`, `T ≥ 1`, `0 ≤ C₀ ≤ C`.  The base `qT`
splits as `q · T`: the `q`-part is bounded against the exponential `e^{(5/2)(1-σ) log q}` and the
`T`-part against `T^{3/2}`. -/
private lemma rpow_mul_le_exp_mul {q : ℕ} (hq : 2 ≤ q) {T C₀ C e σ : ℝ} (hT : 1 ≤ T)
    (hC₀ : 0 ≤ C₀) (hC : C₀ ≤ C) (hef : e ≤ (5 / 2) * (1 - σ)) (heg : e ≤ (3 : ℝ) / 2) :
    C₀ * ((q : ℝ) * T) ^ e
      ≤ C * Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) * T ^ ((3 : ℝ) / 2) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := hT
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
  have hbase : (0 : ℝ) ≤ (q : ℝ) * T := by positivity
  have hexp_pos : (0 : ℝ) < Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) := Real.exp_pos _
  have hkey : ((q : ℝ) * T) ^ e
      ≤ Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) * T ^ ((3 : ℝ) / 2) := by
    rw [Real.mul_rpow hq0.le hT0.le]
    have h1 : (q : ℝ) ^ e ≤ Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) := by
      rw [Real.rpow_def_of_pos hq0]
      apply Real.exp_le_exp.mpr
      calc Real.log (q : ℝ) * e ≤ Real.log (q : ℝ) * ((5 / 2) * (1 - σ)) :=
            mul_le_mul_of_nonneg_left hef hlogq
        _ = (5 / 2) * ((1 - σ) * Real.log (q : ℝ)) := by ring
    have h2 : T ^ e ≤ T ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hT1 heg
    exact mul_le_mul h1 h2 (Real.rpow_nonneg hT0.le e) (le_of_lt hexp_pos)
  calc C₀ * ((q : ℝ) * T) ^ e
      ≤ C * ((q : ℝ) * T) ^ e := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hbase e)
    _ ≤ C * (Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) * T ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hkey (le_trans hC₀ hC)
    _ = C * Real.exp ((5 / 2) * ((1 - σ) * Real.log (q : ℝ))) * T ^ ((3 : ℝ) / 2) := by
        rw [mul_assoc]

/-- The height version of the log-free family zero count with the two exponents separated, assembled from Jutila's estimate on sigma >= 4/5 and Huxley's 12/5 estimate on sigma <= 4/5 together with the sigma-blind count. Assume `hJ : Work.ZeroDensity.FamDensityEpsRange (4/5) 1 2`, i.e. sum_chi N(sigma,T,chi) <= C*(q*T)^((2+eps)(1-sigma)) for 4/5 <= sigma <= 1, and `hH : Work.ZeroDensity.FamDensityEpsRange 0 (4/5) (12/5)`, i.e. sum_chi N(sigma,T,chi) <= C*(q*T)^((12/5+eps)(1-sigma)) for 0 <= sigma <= 4/5. Conclude `Work.ZeroDensity.LogFreeFamHeight (5/2) (3/2)`: there are C > 0 and q_0 with `famCount q sigma T <= C*exp((5/2)*((1-sigma)*log q))*T^(3/2)` for all q >= q_0, 0 <= sigma <= 1 and T >= 1. Splitting at sigma = 2/5: for sigma >= 4/5 use hJ at a small eps (eps <= 1/2), so that the q-exponent (2+eps)(1-sigma) <= (5/2)(1-sigma) and the T-exponent (2+eps)(1-sigma) <= (2+eps)/5 <= 3/2; for 2/5 <= sigma <= 4/5 use hH at eps <= 1/10, so that (12/5+eps) <= 5/2 and (12/5+eps)(1-sigma) <= (12/5+eps)(3/5) <= 3/2; for sigma <= 2/5 use the sigma-blind `Work.ZeroDensity.trivial_bound` (already proved: famCount q sigma T <= C*(q*T)^(1+eps)) with eps <= 1/2, where 1+eps <= 3/2 and 1+eps <= (5/2)*(1-sigma) because 1-sigma >= 3/5. The three constants are maxed and the eps's may be chosen independently; the hypothesis `[NeZero q]` and `q >= 2` are available throughout and `q_0` may be taken to be 2. -/
theorem logFreeFamHeight_of_cores (hJ : Work.ZeroDensity.FamDensityEpsRange (4/5) 1 2)
    (hH : Work.ZeroDensity.FamDensityEpsRange 0 (4/5) (12/5)) :
    Work.ZeroDensity.LogFreeFamHeight (5/2) (3/2) := by
  obtain ⟨CJ, hCJ, hJ'⟩ := hJ (1 / 2) (by norm_num)
  obtain ⟨CH, hCH, hH'⟩ := hH (1 / 10) (by norm_num)
  obtain ⟨CT, hCT, hT'⟩ := trivial_bound (1 / 2) (by norm_num)
  refine ⟨max (max CJ CH) CT,
    lt_of_lt_of_le hCJ (le_trans (le_max_left _ _) (le_max_left _ _)), 2, ?_⟩
  intro q hq _ σ T h0 hσ1 hT
  have hCJle : CJ ≤ max (max CJ CH) CT := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCHle : CH ≤ max (max CJ CH) CT := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCTle : CT ≤ max (max CJ CH) CT := le_max_right _ _
  rcases le_total (4 / 5) σ with hA | hA
  · -- `σ ≥ 4/5`: Jutila at `eps = 1/2`, exponent `(5/2)(1-σ)`
    refine le_trans (hJ' q hq σ T hA hσ1 hT) ?_
    refine rpow_mul_le_exp_mul hq hT (le_of_lt hCJ) hCJle ?_ ?_
    · nlinarith
    · have h : 1 - σ ≤ 1 / 5 := by linarith
      nlinarith
  · rcases le_total (2 / 5) σ with hB | hC
    · -- `2/5 ≤ σ ≤ 4/5`: Huxley at `eps = 1/10`, exponent `(5/2)(1-σ)`
      refine le_trans (hH' q hq σ T h0 hA hT) ?_
      refine rpow_mul_le_exp_mul hq hT (le_of_lt hCH) hCHle ?_ ?_
      · nlinarith
      · have h : 1 - σ ≤ 3 / 5 := by linarith
        nlinarith
    · -- `σ ≤ 2/5`: the σ-blind count at `eps = 1/2`, exponent `3/2`
      refine le_trans (hT' q hq σ T h0 hσ1 hT) ?_
      refine rpow_mul_le_exp_mul hq hT (le_of_lt hCT) hCTle ?_ ?_
      · have h : 3 / 5 ≤ 1 - σ := by linarith
        nlinarith
      · norm_num

end

end Work.ZeroDensity.Assembly
