import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-!
## The trace at `π/2` of a function with a weighted oscillation bound

`TraceOfOscPiO` is the "right endpoint" companion of `TraceOfOsc`.  If `u : ℝ → ℝ` satisfies

  `|u b - u a| ≤ K · sin(2a)^{(γ-1)/2}`   for `π/4 ≤ a ≤ b < π/2`,   `γ > 1`, `K ≥ 0`,

then `u` has a limit `mu` at `π/2` from the left, at the weighted Hardy rate

  `(u θ - mu)² ≤ K² · sin(2θ)^{γ-1}`   for `π/4 < θ < π/2`.

The weight `sin(2a)^{(γ-1)/2}` tends to `0` as `a → π/2⁻`, so the hypothesis says precisely
that `u` is Cauchy at `π/2⁻` with an explicit modulus.  The proof extracts the limit along the
explicit sequence `a n = π/2 - 1/(n+2) ↑ π/2` (Cauchy + completeness of `ℝ`), recovers the rate
by passing the oscillation bound to the limit, and finally obtains the unrestricted filter
convergence by squeezing `|u θ - mu|` between `0` and `K · sin(2θ)^{(γ-1)/2} → 0`.
-/

theorem TraceOfOscPiO {u : ℝ → ℝ} {γ K : ℝ} (hγ : 0 < γ - 1) (hK : 0 ≤ K)
    (hbound : ∀ a b : ℝ, Real.pi / 4 ≤ a → a ≤ b → b < Real.pi / 2 →
      |u b - u a| ≤ K * (Real.sin (2 * a)) ^ ((γ - 1) / 2)) :
    ∃ mu : ℝ, Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds mu) ∧
      ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
        (u θ - mu) ^ 2 ≤ K ^ 2 * (Real.sin (2 * θ)) ^ (γ - 1) := by
  have hγ2 : 0 < (γ - 1) / 2 := by linarith
  -- the explicit sequence tending to `π/2` from below
  let a : ℕ → ℝ := fun n => Real.pi / 2 - 1 / ((n : ℝ) + 2)
  have ha_ge : ∀ n : ℕ, Real.pi / 4 ≤ a n := by
    intro n
    have h1 : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 := by
      refine one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) ?_
      linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
    have h2 : (1 : ℝ) / 2 ≤ Real.pi / 4 := by linarith [Real.pi_gt_three]
    dsimp only [a]
    linarith
  have ha_lt : ∀ n : ℕ, a n < Real.pi / 2 := by
    intro n
    have h1 : 0 < (1 : ℝ) / ((n : ℝ) + 2) := by positivity
    dsimp only [a]
    linarith
  have ha_mono : Monotone a := by
    refine monotone_nat_of_le_succ fun n => ?_
    have h1 : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) := by
      refine one_div_le_one_div_of_le (show (0 : ℝ) < (n : ℝ) + 2 by positivity) ?_
      push_cast
      linarith
    dsimp only [a]
    linarith
  have ha_tendsto : Tendsto a atTop (nhds (Real.pi / 2)) := by
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (f := fun n : ℕ => (n : ℝ)) 2
        tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp h2
    have h3 := (tendsto_const_nhds (x := Real.pi / 2)).sub hinv
    simpa [a, one_div, sub_zero] using h3
  -- `sin (2·) ≥ 0` on the closed angular interval `[π/4, π/2]`
  have sin_nn : ∀ θ : ℝ, Real.pi / 4 ≤ θ → θ < Real.pi / 2 → 0 ≤ Real.sin (2 * θ) := by
    intro θ h1 h2
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  -- the weight along the testing sequence tends to `0`
  have hSseq : Tendsto (fun n : ℕ => K * Real.sin (2 * a n) ^ ((γ - 1) / 2)) atTop (nhds 0) := by
    have hsin : Tendsto (fun n : ℕ => Real.sin (2 * a n)) atTop (nhds 0) := by
      have h2 : Tendsto (fun n : ℕ => 2 * a n) atTop (nhds (2 * (Real.pi / 2))) :=
        (tendsto_const_nhds (x := (2 : ℝ))).mul ha_tendsto
      have h3 := (Real.continuous_sin.tendsto (2 * (Real.pi / 2))).comp h2
      simpa [Function.comp_def, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi] using h3
    have h4 := hsin.rpow_const_nhds_zero hγ2
    simpa using h4.const_mul K
  -- the sequence is Cauchy, hence converges
  have hcauchy : CauchySeq (fun n : ℕ => u (a n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hSseq (ε / 2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hSN : K * Real.sin (2 * a N) ^ ((γ - 1) / 2) < ε / 2 := by
      have h0 := hN N le_rfl
      rw [Real.dist_eq, sub_zero] at h0
      rwa [abs_of_nonneg
        (mul_nonneg hK (Real.rpow_nonneg (sin_nn (a N) (ha_ge N) (ha_lt N)) _))] at h0
    have h1 : dist (u (a m)) (u (a N)) ≤ K * Real.sin (2 * a N) ^ ((γ - 1) / 2) := by
      rw [Real.dist_eq]
      exact hbound (a N) (a m) (ha_ge N) (ha_mono hm) (ha_lt m)
    have h2 : dist (u (a N)) (u (a n)) ≤ K * Real.sin (2 * a N) ^ ((γ - 1) / 2) := by
      rw [Real.dist_eq, abs_sub_comm]
      exact hbound (a N) (a n) (ha_ge N) (ha_mono hn) (ha_lt n)
    linarith [dist_triangle (u (a m)) (u (a N)) (u (a n))]
  obtain ⟨mu, hmu⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the weighted rate, obtained by passing the oscillation bound to the limit
  have hbd : ∀ θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2),
      |u θ - mu| ≤ K * Real.sin (2 * θ) ^ ((γ - 1) / 2) := by
    intro θ hθ
    have hev : ∀ᶠ n : ℕ in atTop, θ < a n :=
      ha_tendsto.eventually (isOpen_Ioi.mem_nhds hθ.2)
    have hlim : Tendsto (fun n : ℕ => |u (a n) - u θ|) atTop (nhds |mu - u θ|) :=
      (hmu.sub_const (u θ)).abs
    have hle : |mu - u θ| ≤ K * Real.sin (2 * θ) ^ ((γ - 1) / 2) := by
      refine le_of_tendsto hlim ?_
      filter_upwards [hev] with n hn
      exact hbound θ (a n) (le_of_lt hθ.1) (le_of_lt hn) (ha_lt n)
    rwa [abs_sub_comm] at hle
  refine ⟨mu, ?_, ?_⟩
  · -- the unrestricted convergence at `π/2` from the left
    have hmem : Set.Ioo (Real.pi / 4) (Real.pi / 2) ∈
        nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
      rw [mem_nhdsWithin_iff_eventually]
      filter_upwards [Ioi_mem_nhds (show Real.pi / 4 < Real.pi / 2 by linarith [Real.pi_pos])]
        with x hx hx2
      exact ⟨hx, hx2⟩
    have hS : Tendsto (fun θ : ℝ => K * Real.sin (2 * θ) ^ ((γ - 1) / 2))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have hid : Tendsto (fun θ : ℝ => θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (Real.pi / 2)) := tendsto_id.mono_right nhdsWithin_le_nhds
      have h2 : Tendsto (fun θ : ℝ => 2 * θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (2 * (Real.pi / 2))) := (tendsto_const_nhds (x := (2 : ℝ))).mul hid
      have h3 : Tendsto (fun θ : ℝ => Real.sin (2 * θ))
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (Real.sin (2 * (Real.pi / 2)))) :=
        (Real.continuous_sin.tendsto (2 * (Real.pi / 2))).comp h2
      have h4 : Tendsto (fun θ : ℝ => Real.sin (2 * θ))
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        simpa [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi] using h3
      have h5 := h4.rpow_const_nhds_zero hγ2
      simpa using h5.const_mul K
    have habs : Tendsto (fun θ : ℝ => |u θ - mu|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      refine squeeze_zero' (g := fun θ : ℝ => K * Real.sin (2 * θ) ^ ((γ - 1) / 2))
        (Eventually.of_forall fun θ => abs_nonneg _) ?_ hS
      exact eventually_of_mem hmem fun θ hθ => hbd θ hθ
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using habs
  · -- the rate, by squaring the oscillation bound
    intro θ hθ
    have hb := hbd θ hθ
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos])
    have hsq : (u θ - mu) ^ 2 ≤ (K * Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg hK (Real.rpow_nonneg (le_of_lt hspos) _))]
      exact hb
    have hkey : (K * Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2
        = K ^ 2 * Real.sin (2 * θ) ^ (γ - 1) := by
      have h1 : (Real.sin (2 * θ) ^ ((γ - 1) / 2)) ^ 2 = Real.sin (2 * θ) ^ (γ - 1) := by
        rw [pow_two, ← Real.rpow_add hspos]
        congr 1
        ring
      rw [mul_pow, h1]
    rw [hkey] at hsq
    exact hsq

end Work.FTS.StrongEps.EpsLocalPStar
