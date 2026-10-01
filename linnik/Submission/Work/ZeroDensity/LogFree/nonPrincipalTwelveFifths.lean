import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs

namespace Work.ZeroDensity.LogFree

/-- L8(c) of JUTILA_UNIFIED_LEAD.md section 3: Heath-Brown's (1.4) for the non-principal characters, `Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths`, glued from two inputs. Assume

* `hlog : Work.ZeroDensity.LogFree.logFreeNP (93/100) (12/5)`, i.e. `sum_{chi != 1} N(sigma,T,chi) <= C (qT)^((12/5)(1-sigma))` for `sigma >= 93/100`, log-free;
* `hhux : Work.ZeroDensity.LogFree.HuxleyNPWide`, i.e. `sum_{chi != 1} N(sigma,T,chi) <= C (qT)^((12/5+eps)(1-sigma)) log(qT)` for `3/4 <= sigma <= 93/100`.

Conclude `Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths`: for every `eps > 0` there is `C > 0` with `sum_{chi != 1} N(sigma,T,chi) <= C (qT)^((12/5+eps)(1-sigma))` for all `q >= 2`, all `sigma` with `3979/5000 <= sigma <= 1` and all `T >= 1`. Route: split at `sigma = 93/100` (note `3979/5000 = 0.7958 > 3/4`, so the lower range is inside `[3/4, 93/100]`); on `[3979/5000, 93/100]` use `hhux` at `eps/2` and absorb the logarithm via `log x <= C_delta x^delta` with `delta = (eps/2)*(7/100) <= (eps/2)(1-sigma)`, because `1 - sigma >= 7/100` there; on `[93/100, 1]` use `hlog` with exponent `(12/5)(1-sigma) <= (12/5+eps)(1-sigma)`; take the maximum of the two constants. -/
theorem nonPrincipalTwelveFifths (hlog : Work.ZeroDensity.LogFree.logFreeNP (93/100) (12/5))
    (hhux : Work.ZeroDensity.LogFree.HuxleyNPWide) :
    Work.ZeroDensity.LogFree.NonPrincipalTwelveFifths := by
  intro ε hε
  obtain ⟨C1, hC1, h1⟩ := hlog
  obtain ⟨C2, hC2, h2⟩ := hhux (ε/2) (by linarith)
  set δ : ℝ := (ε/2) * (7/100) with hδdef
  have hδ : 0 < δ := by positivity
  refine ⟨max C1 (C2 / δ), lt_of_lt_of_le hC1 (le_max_left _ _), ?_⟩
  intro q hq _inst σ T hσlo hσ1 hT
  have hbase1 : (1:ℝ) ≤ (q:ℝ)*T := by
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    nlinarith
  have hbase0 : (0:ℝ) ≤ (q:ℝ)*T := by linarith
  have hbasepos : (0:ℝ) < (q:ℝ)*T := by linarith
  by_cases hle : σ ≤ 93/100
  · have hσ34 : (3:ℝ)/4 ≤ σ := by
      have : (3:ℝ)/4 ≤ 3979/5000 := by norm_num
      linarith
    have hb := h2 q hq σ T hσ34 hle hT
    have hlogb : Real.log ((q:ℝ)*T) ≤ δ⁻¹ * ((q:ℝ)*T)^δ := by
      have h := Real.log_le_rpow_div hbase0 hδ
      rw [div_eq_inv_mul] at h
      simpa only [mul_comm] using h
    have hCa : (0:ℝ) ≤ C2 * ((q:ℝ)*T)^((12/5+ε/2)*(1-σ)) :=
      mul_nonneg (le_of_lt hC2) (Real.rpow_nonneg hbase0 _)
    have hexp : (12/5 + ε/2)*(1-σ) + δ ≤ (12/5+ε)*(1-σ) := by
      rw [hδdef]; nlinarith [hε, hle]
    calc famCountNP q σ T
        ≤ C2 * ((q:ℝ)*T)^((12/5+ε/2)*(1-σ)) * Real.log ((q:ℝ)*T) := hb
      _ ≤ (C2 * ((q:ℝ)*T)^((12/5+ε/2)*(1-σ))) * (δ⁻¹ * ((q:ℝ)*T)^δ) :=
            mul_le_mul_of_nonneg_left hlogb hCa
      _ = (C2/δ) * ((q:ℝ)*T)^((12/5+ε/2)*(1-σ) + δ) := by
            rw [Real.rpow_add hbasepos]; ring
      _ ≤ (C2/δ) * ((q:ℝ)*T)^((12/5+ε)*(1-σ)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase1 hexp)
              (div_nonneg (le_of_lt hC2) (le_of_lt hδ))
      _ ≤ max C1 (C2/δ) * ((q:ℝ)*T)^((12/5+ε)*(1-σ)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hbase0 _)
  · have hσ93 : (93/100:ℝ) ≤ σ := le_of_lt (not_le.mp hle)
    have hb := h1 q hq σ T hσ93 hσ1 hT
    have hexp2 : (12/5)*(1-σ) ≤ (12/5+ε)*(1-σ) := by
      have h0 : 0 ≤ 1-σ := by linarith
      nlinarith [hε, h0]
    calc famCountNP q σ T
        ≤ C1 * ((q:ℝ)*T)^((12/5)*(1-σ)) := hb
      _ ≤ C1 * ((q:ℝ)*T)^((12/5+ε)*(1-σ)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase1 hexp2) (le_of_lt hC1)
      _ ≤ max C1 (C2/δ) * ((q:ℝ)*T)^((12/5+ε)*(1-σ)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hbase0 _)

end Work.ZeroDensity.LogFree
