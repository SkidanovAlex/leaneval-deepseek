import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup
import Submission.Work.LinnikAreas.Density4.norm_lcmF_le

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- Same bound as `norm_lcmF_le`, but only assuming `s.re ≥ 1 - 1/k` instead of equality.
Since every term of `lcmF` carries a factor `[d,e]^{-s}` with `[d,e] ≥ 1`, increasing `s.re`
can only decrease the modulus of every term, so the bound gets easier. -/
theorem norm_lcmF_le_gen (q : ℕ) [NeZero q] {U V W : ℝ} (hU : 0 < U) (hUV : U ≤ V) (hV : 1 ≤ V)
    (hW : 1 ≤ W) (χ : DirichletCharacter ℂ q) {k : ℕ} (hk : 1 ≤ k) {s : ℂ}
    (hs : 1 - (k : ℝ)⁻¹ ≤ s.re) :
    ‖lcmF q U V W χ s‖ ≤ (V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3 := by
  set A : ℕ := Nat.floor V with hAdef
  set B : ℕ := Nat.floor W with hBdef
  set σ : ℝ := 1 - (k : ℝ)⁻¹ with hσdef
  have hA1 : 1 ≤ A := by rw [hAdef]; exact Nat.le_floor (by exact_mod_cast hV)
  have hB1 : 1 ≤ B := by rw [hBdef]; exact Nat.le_floor (by exact_mod_cast hW)
  have hAV : (A:ℝ) ≤ V := by rw [hAdef]; exact Nat.floor_le (by linarith only [hU, hUV])
  have hBW : (B:ℝ) ≤ W := by rw [hBdef]; exact Nat.floor_le (by linarith only [hW])
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkinv1 : (k:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hk)
  have hkinv0 : 0 ≤ (k:ℝ)⁻¹ := inv_nonneg.mpr hkpos.le
  have hσ0 : 0 ≤ σ := by rw [hσdef]; linarith only [hkinv1]
  have hσ1 : σ ≤ 1 := by rw [hσdef]; linarith only [hkinv0]
  have hsre : σ ≤ s.re := by rw [hσdef]; exact hs
  have hV0 : (0:ℝ) < V := lt_of_lt_of_le one_pos hV
  have hW0 : (0:ℝ) < W := lt_of_lt_of_le one_pos hW
  have hnorm : ‖lcmF q U V W χ s‖
      ≤ ∑ d ∈ Finset.Icc 1 A, ∑ e ∈ Finset.Icc 1 B, ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ) := by
    rw [lcmF_eq_sum_lcmTerm q hUV χ s, ← hAdef, ← hBdef]
    calc ‖∑ d ∈ Finset.Icc 1 A, ∑ e ∈ Finset.Icc 1 B, lcmTerm q U V W χ s d e‖
        ≤ ∑ d ∈ Finset.Icc 1 A, ‖∑ e ∈ Finset.Icc 1 B, lcmTerm q U V W χ s d e‖ :=
          norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 A, ∑ e ∈ Finset.Icc 1 B, ‖lcmTerm q U V W χ s d e‖ :=
          Finset.sum_le_sum (fun d _ => norm_sum_le _ _)
      _ ≤ ∑ d ∈ Finset.Icc 1 A, ∑ e ∈ Finset.Icc 1 B, ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ) := by
          apply Finset.sum_le_sum; intro d hd
          apply Finset.sum_le_sum; intro e he
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
          have hlcm1 : (1:ℝ) ≤ ((Nat.lcm d e : ℕ) : ℝ) := by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.lcm_ne_zero (by omega) (by omega)))
          calc ‖lcmTerm q U V W χ s d e‖ ≤ ((Nat.lcm d e : ℕ) : ℝ) ^ (-s.re) :=
                norm_lcmTerm_le q hU χ hd1 he1
            _ ≤ ((Nat.lcm d e : ℕ) : ℝ) ^ (-σ) :=
                Real.rpow_le_rpow_of_exponent_le hlcm1 (by linarith only [hs])
  have hsum := sum_lcm_rpow_neg_le hA1 hB1 hσ0 hσ1
  refine hnorm.trans (hsum.trans ?_)
  have hAle : (A:ℝ) ^ (1 - σ) ≤ V ^ (1 - σ) :=
    Real.rpow_le_rpow (by positivity) hAV (by linarith only [hkinv0])
  have hBle : (B:ℝ) ^ (1 - σ) ≤ W ^ (1 - σ) :=
    Real.rpow_le_rpow (by positivity) hBW (by linarith only [hkinv0])
  have hlogA : 1 + Real.log (A:ℝ) ≤ 1 + Real.log (V * W) := by
    have h1 : Real.log (A:ℝ) ≤ Real.log (V * W) :=
      Real.log_le_log (by positivity) (by nlinarith only [hAV, hW0.le, hV0.le, hU, hW, hUV])
    linarith only [h1]
  have hlogB : 1 + Real.log (B:ℝ) ≤ 1 + Real.log (V * W) := by
    have h1 : Real.log (B:ℝ) ≤ Real.log (V * W) :=
      Real.log_le_log (by positivity) (by nlinarith only [hBW, hV0.le, hW0.le, hV, hU, hUV])
    linarith only [h1]
  have hlogA0 : 0 ≤ 1 + Real.log (A:ℝ) := by
    have : (1:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA1
    linarith only [Real.log_nonneg this, this]
  have hlogB0 : 0 ≤ 1 + Real.log (B:ℝ) := by
    have : (1:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB1
    linarith only [Real.log_nonneg this, this]
  have hlogle : (1 + Real.log (A:ℝ)) ^ 2 * (1 + Real.log (B:ℝ))
      ≤ (1 + Real.log (V * W)) ^ 3 := by
    have h2 : (1 + Real.log (A:ℝ)) ^ 2 ≤ (1 + Real.log (V * W)) ^ 2 :=
      pow_le_pow_left₀ hlogA0 hlogA 2
    have h3 : (1 + Real.log (V * W)) ^ 2 * (1 + Real.log (B:ℝ))
        ≤ (1 + Real.log (V * W)) ^ 2 * (1 + Real.log (V * W)) :=
      mul_le_mul_of_nonneg_left hlogB (by positivity)
    calc (1 + Real.log (A:ℝ)) ^ 2 * (1 + Real.log (B:ℝ))
        ≤ (1 + Real.log (V * W)) ^ 2 * (1 + Real.log (B:ℝ)) :=
          mul_le_mul_of_nonneg_right h2 hlogB0
      _ ≤ (1 + Real.log (V * W)) ^ 2 * (1 + Real.log (V * W)) := h3
      _ = (1 + Real.log (V * W)) ^ 3 := by ring
  have hprod : (A:ℝ) ^ (1 - σ) * (B:ℝ) ^ (1 - σ) ≤ (V * W) ^ (1 - σ) := by
    have h4 : (A:ℝ) ^ (1 - σ) * (B:ℝ) ^ (1 - σ) ≤ V ^ (1 - σ) * W ^ (1 - σ) :=
      mul_le_mul hAle hBle (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hV0.le _)
    simpa [← Real.mul_rpow hV0.le hW0.le] using h4
  have hexp : 1 - σ = 1 / (k : ℝ) := by
    rw [hσdef]; simp [one_div]
  calc (A : ℝ) ^ (1 - σ) * (B : ℝ) ^ (1 - σ) * (1 + Real.log (A : ℝ)) ^ 2
        * (1 + Real.log (B : ℝ))
      = ((A:ℝ) ^ (1 - σ) * (B:ℝ) ^ (1 - σ))
          * ((1 + Real.log (A:ℝ)) ^ 2 * (1 + Real.log (B:ℝ))) := by ring
    _ ≤ (V * W) ^ (1 - σ) * (1 + Real.log (V * W)) ^ 3 :=
        mul_le_mul hprod hlogle (by positivity) (Real.rpow_nonneg (by positivity) _)
    _ = (V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3 := by rw [hexp]

end Work.LinnikAreas.Density4
