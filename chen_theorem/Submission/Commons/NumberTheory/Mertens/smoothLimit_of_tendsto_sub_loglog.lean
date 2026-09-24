import Mathlib
import Submission.Commons.NumberTheory.Mertens.error_smoothSum_tendsto_zero
import Submission.Commons.NumberTheory.Mertens.weightedDiff_telescoping
import Submission.Commons.NumberTheory.Mertens.summable_weighted_loglog
import Submission.Commons.NumberTheory.Mertens.summable_weighted_error
import Submission.Commons.Analysis.InfiniteSum.rpowDiff_loglog_add_log_tendsto

open Filter
open scoped Topology BigOperators

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- right filter: ε → 0⁺ -/
private def rightFilter : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))

/-- `(2:ℝ)^{-ε} → 1` as `ε → 0⁺` -/
private lemma tendsto_two_rpow_neg_one :
    Tendsto (fun ε : ℝ => (2 : ℝ) ^ (-ε)) rightFilter (nhds 1) := by
  have hid : Tendsto (fun ε : ℝ => ε) rightFilter (nhds (0 : ℝ)) :=
    continuousAt_id.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
  have hneg : Tendsto (fun ε : ℝ => -ε) rightFilter (nhds (0 : ℝ)) := by
    simpa using hid.neg
  have hlogc : Tendsto (fun _ : ℝ => Real.log (2 : ℝ)) rightFilter
      (nhds (Real.log (2 : ℝ))) := tendsto_const_nhds
  have hmul : Tendsto (fun ε : ℝ => (-ε) * Real.log (2 : ℝ)) rightFilter (nhds 0) := by
    simpa using hneg.mul hlogc
  have hexp := Real.continuous_exp.tendsto (0 : ℝ)
  have hcomp : Tendsto (fun ε : ℝ => Real.exp ((-ε) * Real.log (2 : ℝ))) rightFilter
      (nhds 1) := by
    simpa [Function.comp_def] using hexp.comp hmul
  refine hcomp.congr ?_
  intro ε
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- `M * (2:ℝ)^{-ε} → M` as `ε → 0⁺` -/
private lemma tendsto_const_mul_two_rpow_neg_one (M : ℝ) :
    Tendsto (fun ε : ℝ => M * (2 : ℝ) ^ (-ε)) rightFilter (nhds M) := by
  have hc : Tendsto (fun _ : ℝ => M) rightFilter (nhds M) := tendsto_const_nhds
  have h := hc.mul tendsto_two_rpow_neg_one
  simpa using h

/-- pointwise: `0 < ε` is eventually true along the right filter -/
private lemma eventually_pos_right :
    ∀ᶠ ε : ℝ in rightFilter, 0 < ε := by
  have h : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) :=
    self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ))
  exact h

/-- loglog of a natural index (well-defined only via the guard `2 ≤ k`) -/
private def ll (k : ℕ) : ℝ := Real.log (Real.log (k : ℝ))

theorem smoothLimit_of_tendsto_sub_loglog {a : ℕ → ℝ} {M : ℝ}
    (ha : Filter.Tendsto (fun k : ℕ => a k - Real.log (Real.log (k : ℝ))) Filter.atTop
      (nhds M)) :
    Filter.Tendsto (fun ε : ℝ =>
      (∑' k : ℕ, if 2 ≤ k then
        a k * (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0) + Real.log ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (M - Real.eulerMascheroniConstant)) := by
  -- the error sequence tends to zero
  let e : ℕ → ℝ := fun k => a k - ll k - M
  have he : Tendsto e atTop (nhds 0) := by
    have hsub : Tendsto (fun k : ℕ => (a k - ll k) - M) atTop (nhds (M - M)) := by
      simpa [ll] using ha.sub (tendsto_const_nhds (x := M))
    have hM : M - M = 0 := by ring
    simpa [e, hM] using hsub
  -- the smoothing coefficient
  let gw : ℝ → ℕ → ℝ := fun ε k =>
    if 2 ≤ k then (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0
  -- The three pieces of the decomposition
  let P1 : ℝ → ℝ := fun ε => ∑' k : ℕ, M * gw ε k
  let P2 : ℝ → ℝ := fun ε => (∑' k : ℕ, ll k * gw ε k) + Real.log ε
  let P3 : ℝ → ℝ := fun ε => ∑' k : ℕ, e k * gw ε k
  -- Pointwise decomposition of the sum (valid for 0 < ε)
  have hsplit : ∀ ε : ℝ, 0 < ε →
      (∑' k : ℕ, a k * gw ε k) + Real.log ε = (P1 ε + P2 ε) + P3 ε := by
    intro ε hε
    -- Summability of the three pieces
    have hSw : Summable (fun k : ℕ => gw ε k) := ⟨_, weightedDiff_telescoping hε⟩
    have hSM : Summable (fun k : ℕ => M * gw ε k) := hSw.mul_left M
    have hSL : Summable (fun k : ℕ => ll k * gw ε k) := by
      have h := (summable_weighted_loglog hε)
      refine h.congr ?_
      intro k
      by_cases hk : 2 ≤ k <;> simp [gw, ll, hk]
    have hSE : Summable (fun k : ℕ => e k * gw ε k) := by
      have h := (summable_weighted_error he hε)
      refine h.congr ?_
      intro k
      by_cases hk : 2 ≤ k <;> simp [gw, hk]
    have hsum : HasSum (fun k : ℕ =>
        (M * gw ε k + ll k * gw ε k) + e k * gw ε k)
        ((∑' k : ℕ, M * gw ε k) + (∑' k : ℕ, ll k * gw ε k) +
          (∑' k : ℕ, e k * gw ε k)) := by
      have h1 := (Summable.hasSum hSM).add (Summable.hasSum hSL)
      have h2 := h1.add (Summable.hasSum hSE)
      simpa [add_assoc] using h2
    have hcongfun : ∀ k : ℕ, a k * gw ε k =
        (M * gw ε k + ll k * gw ε k) + e k * gw ε k := by
      intro k
      unfold e ll
      ring
    have hAs : HasSum (fun k : ℕ => a k * gw ε k)
        ((∑' k : ℕ, M * gw ε k) + (∑' k : ℕ, ll k * gw ε k) +
          (∑' k : ℕ, e k * gw ε k)) := hsum.congr_fun hcongfun
    have hAsEq : (∑' k : ℕ, a k * gw ε k) =
        (∑' k : ℕ, M * gw ε k) + (∑' k : ℕ, ll k * gw ε k) +
          (∑' k : ℕ, e k * gw ε k) := hAs.tsum_eq
    calc
      (∑' k : ℕ, a k * gw ε k) + Real.log ε
          = ((∑' k : ℕ, M * gw ε k) + (∑' k : ℕ, ll k * gw ε k)) +
              (∑' k : ℕ, e k * gw ε k) + Real.log ε := by rw [hAsEq]
      _ = (P1 ε + P2 ε) + P3 ε := by
          dsimp [P1, P2, P3]
          ring
  -- Tendsto of the pieces
  have hP1 : Tendsto P1 rightFilter (nhds M) := by
    have hlim := tendsto_const_mul_two_rpow_neg_one M
    refine hlim.congr' ?_
    filter_upwards [eventually_pos_right] with ε hε
    have htel : HasSum (fun k : ℕ => gw ε k) ((2 : ℝ) ^ (-ε)) := by
      simpa [gw] using (weightedDiff_telescoping hε)
    have htelM : HasSum (fun k : ℕ => M * gw ε k) (M * (2 : ℝ) ^ (-ε)) :=
      htel.mul_left M
    dsimp [P1]
    exact htelM.tsum_eq.symm
  have hP2 : Tendsto P2 rightFilter (nhds (-Real.eulerMascheroniConstant)) := by
    have hC := Commons.Analysis.InfiniteSum.rpowDiff_loglog_add_log_tendsto
    refine (Filter.Tendsto.congr ?_ hC)
    intro ε
    congr 1
    apply tsum_congr
    intro k
    by_cases hk : 2 ≤ k <;> simp [gw, ll, hk]
  have hP3 : Tendsto P3 rightFilter (nhds 0) := by
    have hE := (error_smoothSum_tendsto_zero he).2
    refine (Filter.Tendsto.congr ?_ hE)
    intro ε
    apply tsum_congr
    intro k
    by_cases hk : 2 ≤ k <;> simp [gw, hk]
  -- Combine
  have hF : Tendsto (fun ε : ℝ => (P1 ε + P2 ε) + P3 ε) rightFilter
      (nhds (M + (-Real.eulerMascheroniConstant) + 0)) := by
    have h12 := hP1.add hP2
    simpa [add_assoc, add_comm, add_left_comm] using h12.add hP3
  have hEq : (fun ε : ℝ =>
      (∑' k : ℕ, if 2 ≤ k then
        a k * (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0) + Real.log ε)
      =ᶠ[rightFilter] (fun ε : ℝ => (P1 ε + P2 ε) + P3 ε) := by
    filter_upwards [eventually_pos_right] with ε hε
    -- the guarded sum equals the gw-sum pointwise
    have hg : (∑' k : ℕ, if 2 ≤ k then
          a k * (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0)
        = ∑' k : ℕ, a k * gw ε k := by
      apply tsum_congr
      intro k
      by_cases hk : 2 ≤ k <;> simp [gw, hk]
    rw [hg]
    exact hsplit ε hε
  have hT := hF.congr' hEq.symm
  simpa [sub_eq_add_neg, rightFilter] using hT

end

end Commons.NumberTheory.Mertens
