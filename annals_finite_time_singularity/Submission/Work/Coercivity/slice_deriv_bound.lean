import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Coercivity.changeOrigin_opNorm_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open scoped NNReal ENNReal Topology

/-- **Cauchy-type estimate on a slice.**  If `G` is the sum of the power series `q` on the ball of
radius `r` around the origin of `ℝ × ℝ`, and `4ρ < r`, then for every `k` the `k`-th derivative of
`G` at a point `(0, δ)` with `|δ| ≤ ρ`, taken in the direction `(1, 0)`, is bounded by
`C k! / ρ^k` with a constant `C` independent of `k` and `δ`.

The proof shifts the origin to `a = (0, δ)`, rewrites the `k`-th derivative of `G` at `a` along the
diagonal `(1,0)` as `k!` times the `k`-th coefficient `(q.changeOrigin a) k` of the shifted series,
and bounds that coefficient by Cauchy's estimate for power series coefficients. -/
theorem slice_deriv_bound {G : ℝ × ℝ → ℝ} {q : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ} {r : ℝ≥0}
    (hq : HasFPowerSeriesOnBall G q 0 (r : ℝ≥0∞))
    {ρ : ℝ≥0} (hρ : 0 < ρ) (h4ρ : 4 * ρ < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (δ : ℝ), |δ| ≤ (ρ : ℝ) →
      ‖iteratedFDeriv ℝ k G ((0 : ℝ), δ) (fun _ => ((1 : ℝ), (0 : ℝ)))‖ ≤
        C * (k.factorial : ℝ) / (ρ : ℝ) ^ k := by
  -- Choose `s` with `4 ρ < s < r`.
  obtain ⟨s, hs4, hsr⟩ : ∃ s : ℝ≥0, 4 * ρ < s ∧ s < r := by
    refine ⟨((4 * ρ + r) / 2 : ℝ≥0), ?_, ?_⟩
    · rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul]
      push_cast
      have h4ρ' : (4 : ℝ) * (ρ : ℝ) < (r : ℝ) := by exact_mod_cast h4ρ
      linarith
    · rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul]
      push_cast
      have h4ρ' : (4 : ℝ) * (ρ : ℝ) < (r : ℝ) := by exact_mod_cast h4ρ
      linarith
  have hs0 : (0 : ℝ) < (s : ℝ) := by
    have h4ρ' : (4 : ℝ) * (ρ : ℝ) < (s : ℝ) := by exact_mod_cast hs4
    nlinarith [show (0 : ℝ) ≤ (ρ : ℝ) by positivity]
  have hs0_nn : (0 : ℝ≥0) < s := lt_of_lt_of_le (mul_pos (by norm_num) hρ) (le_of_lt hs4)
  have hs_rad : (s : ℝ≥0∞) < q.radius :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hsr) hq.r_le
  -- Cauchy's estimate for the coefficients of `q`.
  obtain ⟨M, hMpos, hM⟩ := q.norm_le_div_pow_of_pos_of_lt_radius (r := s) hs0_nn hs_rad
  refine ⟨2 * M, by positivity, fun k δ hδ => ?_⟩
  set a : ℝ × ℝ := ((0 : ℝ), δ) with ha_def
  have ha_norm : ‖a‖ ≤ (ρ : ℝ) := by
    rw [ha_def, Prod.norm_def]
    simpa using hδ
  have hρ_le_4ρ : ρ ≤ 4 * ρ := by
    rw [← NNReal.coe_le_coe]; push_cast
    nlinarith [show (0 : ℝ) ≤ (ρ : ℝ) by positivity]
  have hnorm_nn_ρ : ‖a‖₊ ≤ ρ := by
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact ha_norm
  have hnorm_nn_r : ‖a‖₊ < r := lt_of_le_of_lt hnorm_nn_ρ (lt_of_le_of_lt hρ_le_4ρ h4ρ)
  have hnorm_nn_s : ‖a‖₊ < s := lt_of_le_of_lt hnorm_nn_ρ (lt_of_le_of_lt hρ_le_4ρ hs4)
  have ha_r : (‖a‖₊ : ℝ≥0∞) < (r : ℝ≥0∞) := ENNReal.coe_lt_coe.mpr hnorm_nn_r
  have ha_q : (‖a‖₊ : ℝ≥0∞) < q.radius :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hnorm_nn_s) (le_of_lt hs_rad)
  -- Shift the origin and use the diagonal formula for the `k`-th derivative.
  have hca := hq.changeOrigin ha_r
  have hfs := hca.factorial_smul ((1 : ℝ), (0 : ℝ)) k
  rw [zero_add] at hfs
  rw [← hfs, nsmul_eq_mul, norm_mul]
  have hkfac : ‖(k.factorial : ℝ)‖ = (k.factorial : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hkfac]
  have hz_le : ‖(q.changeOrigin a) k (fun _ => ((1 : ℝ), (0 : ℝ)))‖ ≤ ‖q.changeOrigin a k‖ := by
    have h := (q.changeOrigin a k).le_opNorm (fun _ => ((1 : ℝ), (0 : ℝ)))
    have h1 : (∏ i : Fin k, ‖((1 : ℝ), (0 : ℝ))‖) = 1 := by simp [Prod.norm_def]
    rwa [h1, mul_one] at h
  -- Cauchy's estimate for the shifted series.
  have hbound : ‖q.changeOrigin a k‖ ≤ (2 : ℝ) ^ (k + 1) * M / (s : ℝ) ^ k := by
    exact changeOrigin_opNorm_bound (p := q) (a := a) (M := M) (s := (s : ℝ)) (ρ := (ρ : ℝ))
      k hMpos hs0 (by positivity) (by exact_mod_cast hs4) hM ha_norm ha_q
  have hρpos : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  have h2ρ : (2 : ℝ) * (ρ : ℝ) ≤ (s : ℝ) := by
    have h4ρ' : (4 : ℝ) * (ρ : ℝ) < (s : ℝ) := by exact_mod_cast hs4
    linarith
  have hmain : (2 : ℝ) ^ (k + 1) * M / (s : ℝ) ^ k ≤ 2 * M / (ρ : ℝ) ^ k := by
    rw [div_le_div_iff₀ (pow_pos hs0 k) (pow_pos hρpos k)]
    have key : ((2 : ℝ) * (ρ : ℝ)) ^ k ≤ (s : ℝ) ^ k := pow_le_pow_left₀ (by positivity) h2ρ k
    calc (2 : ℝ) ^ (k + 1) * M * (ρ : ℝ) ^ k = (2 * M) * ((2 : ℝ) * (ρ : ℝ)) ^ k := by
          rw [pow_succ, mul_pow]; ring
      _ ≤ (2 * M) * (s : ℝ) ^ k := by gcongr
      _ = 2 * M * (s : ℝ) ^ k := by ring
  calc (k.factorial : ℝ) * ‖(q.changeOrigin a) k (fun _ => ((1 : ℝ), (0 : ℝ)))‖
      ≤ (k.factorial : ℝ) * ‖q.changeOrigin a k‖ :=
        mul_le_mul_of_nonneg_left hz_le (Nat.cast_nonneg _)
    _ ≤ (k.factorial : ℝ) * ((2 : ℝ) ^ (k + 1) * M / (s : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ ≤ (k.factorial : ℝ) * (2 * M / (ρ : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg _)
    _ = 2 * M * (k.factorial : ℝ) / (ρ : ℝ) ^ k := by ring

end Work.Coercivity
