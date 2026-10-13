import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.zHardyAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- Boundary-vanishing sequences at `0` and at `∞`: for a nonnegative integrable `H` on
`(0,∞)` which is continuous on each dyadic annulus around `0` and on each `[k+1, 2k+2]`,
there are `ε k → 0⁺` and `M k → ∞` with `ε k ≤ M k` along which the boundary term `H · id`
vanishes.  Immediate from `Work.FTS.EllipticEst.zHardy_seq_bot` (dyadic minimisers) and
`Work.FTS.EllipticEst.zHardy_seq_top` (minimisers on `[k+1, 2k+2]`), both in
`Submission.Work.FTS.EllipticEst.zHardyAux`: the minimiser `ε k ∈ [2^{-(k+1)}, 2^{-k}]`
satisfies `H (ε k) * ε k ≤ 2 * ∫_{(0, 2^{-k}]} H → 0`, similarly at `∞`. -/
theorem boundarySeqs (H : ℝ → ℝ) (hH : MeasureTheory.IntegrableOn H (Set.Ioi 0))
    (hHnn : ∀ z, 0 ≤ H z)
    (hc1 : ∀ k : ℕ, ContinuousOn H (Set.Icc ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)))
    (hc2 : ∀ k : ℕ, ContinuousOn H (Set.Icc ((k : ℝ) + 1) (2 * ((k : ℝ) + 1)))) :
    ∃ ε M : ℕ → ℝ, (∀ k, 0 < ε k) ∧ (∀ k, ε k ≤ M k) ∧
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      Filter.Tendsto M Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun k => H (ε k) * ε k) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k => H (M k) * M k) Filter.atTop (nhds 0) := by
  -- Integrability on the two halves of `(0,∞)`.
  have hbot : MeasureTheory.IntegrableOn H (Set.Ioc (0:ℝ) 1) :=
    hH.mono_set (fun z hz => hz.1)
  have htop : MeasureTheory.IntegrableOn H (Set.Ioi (1:ℝ)) :=
    hH.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  obtain ⟨ε, hεmem, hεtend, hεbd⟩ :=
    Work.FTS.EllipticEst.zHardy_seq_bot H hbot hHnn hc1
  obtain ⟨M, hMmem, hMtend, hMbd⟩ :=
    Work.FTS.EllipticEst.zHardy_seq_top H htop hHnn hc2
  refine ⟨ε, M, ?_, ?_, hεtend, hMtend, hεbd, hMbd⟩
  · -- `0 < 2^{-(k+1)} ≤ ε k`
    intro k
    have h := (Set.mem_Icc.mp (hεmem k)).1
    have hpos : (0:ℝ) < (1/2:ℝ) ^ (k + 1) := by positivity
    linarith
  · -- `ε k ≤ 2^{-k} ≤ 1 ≤ k+1 ≤ M k`
    intro k
    have hε := (Set.mem_Icc.mp (hεmem k)).2
    have hM := (Set.mem_Icc.mp (hMmem k)).1
    have hpow : (1/2:ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith

end Work.FTS.StrongPersist.H6Pair6Aux
