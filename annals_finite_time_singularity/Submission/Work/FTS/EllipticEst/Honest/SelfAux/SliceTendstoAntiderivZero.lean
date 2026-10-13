import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.SelfAux

/-- **Squeezing with a bounded factor.** If `g → 0` along `l` and `|f| ≤ c |g|` eventually then
`f → 0` along `l` (no sign hypothesis on `c`: `c |g| → c * 0 = 0` regardless). -/
lemma tendsto_zero_of_eventually_abs_le {α : Type*} {l : Filter α} {f g : α → ℝ} {c : ℝ}
    (hg : Filter.Tendsto g l (nhds 0)) (h : ∀ᶠ x in l, |f x| ≤ c * |g x|) :
    Filter.Tendsto f l (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (f := fun x => ‖f x‖) (g := fun x => c * ‖g x‖) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _
  · filter_upwards [h] with x hx
    simpa only [Real.norm_eq_abs] using hx
  · simpa using hg.norm.const_mul c

/-- **The antiderivative `F θ = -(deriv u θ) * u θ + (1/2) * tan θ * (u θ)^2` tends to `0` at
both endpoints of `(0, π/2)`.**  Hypotheses: `u → 0` at `0⁺` and at `(π/2)⁻`, `|u'| ≤ M`,
`|u| ≤ B` and `|u / cos θ| ≤ K` on `(0, π/2)`.

Proof route, by squeezing (`squeeze_zero` + `tendsto_zero_iff_norm_tendsto_zero`):
* `(deriv u) * u → 0` at both endpoints since `|(deriv u θ) * u θ| ≤ M |u θ|`, `|u θ| → 0`, and
  `(0, π/2) ∈ 𝓝[>] 0` and `(0, π/2) ∈ 𝓝[<] (π/2)` make the pointwise bounds available eventually;
* `tan θ * (u θ)^2 → 0` at `0⁺` since `|Real.tan θ * (u θ)^2| ≤ |Real.tan θ| * B^2` and
  `Real.tan → 0` at `0` (`Real.continuous_tan`, `Real.tan_zero`);
* `tan θ * (u θ)^2 → 0` at `(π/2)⁻` since
  `|Real.tan θ * (u θ)^2| = |Real.sin θ| * |u θ| * |u θ / cos θ| ≤ 1 * K * |u θ|` and `u → 0`.
Then assemble with `Filter.Tendsto.neg.mul`, `Filter.Tendsto.add` and constants.

Please declare it at the ROOT namespace (no `namespace` wrapper), so that its name is exactly
`SliceTendstoAntiderivZero`. -/
theorem SliceTendstoAntiderivZero (u : ℝ → ℝ) {B K M : ℝ}
    (h0 : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hpi : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv u θ| ≤ M)
    (hB : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ B)
    (hK : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ / Real.cos θ| ≤ K) :
    Filter.Tendsto (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun s => -(deriv u s) * u s + (1 / 2) * Real.tan s * (u s) ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hhalf : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  -- the pointwise bounds are available *eventually*, on both one-sided filters
  have hev0 : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), s ∈ Set.Ioo 0 (Real.pi / 2) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hhalf),
      eventually_mem_nhdsWithin] with s hs hs'
    exact ⟨hs', hs⟩
  have hevpi : ∀ᶠ s in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      s ∈ Set.Ioo 0 (Real.pi / 2) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hhalf),
      eventually_mem_nhdsWithin] with s hs hs'
    exact ⟨hs, hs'⟩
  -- the `-(deriv u) * u` term at both endpoints
  have hA0 : Filter.Tendsto (fun s => -(deriv u s) * u s) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    refine tendsto_zero_of_eventually_abs_le (c := max M 0) h0 ?_
    filter_upwards [hev0] with s hs
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (le_trans (hM s hs) (le_max_left _ _)) (abs_nonneg (u s))
  have hApi : Filter.Tendsto (fun s => -(deriv u s) * u s)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine tendsto_zero_of_eventually_abs_le (c := max M 0) hpi ?_
    filter_upwards [hevpi] with s hs
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (le_trans (hM s hs) (le_max_left _ _)) (abs_nonneg (u s))
  -- the `(1/2) * tan θ * (u θ)^2` term at `0⁺`: `tan → 0` and `|u| ≤ B`
  have htan0 : Filter.Tendsto (fun s => (1 / 2) * Real.tan s * (u s) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have htan : Filter.Tendsto Real.tan (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc : ContinuousAt Real.tan 0 := Real.continuousAt_tan.mpr (by simp)
      simpa [Real.tan_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    refine tendsto_zero_of_eventually_abs_le (c := (max B 0) ^ 2 / 2) htan ?_
    filter_upwards [hev0] with s hs
    have hBs : |u s| ≤ max B 0 := le_trans (hB s hs) (le_max_left _ _)
    have hsq : (u s) ^ 2 ≤ (max B 0) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg (u s)) hBs 2
      simpa [sq_abs] using this
    have habs : |(1 / 2 : ℝ) * Real.tan s * (u s) ^ 2|
        = (1 / 2 : ℝ) * |Real.tan s| * (u s) ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2), abs_sq]
    rw [habs]
    calc (1 / 2 : ℝ) * |Real.tan s| * (u s) ^ 2
        ≤ (1 / 2 : ℝ) * |Real.tan s| * (max B 0) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = ((max B 0) ^ 2 / 2) * |Real.tan s| := by ring
  -- the same term at `(π/2)⁻`: `tan θ * (u θ)^2 = sin θ * u θ * (u θ / cos θ)`
  have htanpi : Filter.Tendsto (fun s => (1 / 2) * Real.tan s * (u s) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine tendsto_zero_of_eventually_abs_le (c := max K 0 / 2) hpi ?_
    filter_upwards [hevpi] with s hs
    have hcos : Real.cos s ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hhalf, hs.1], hs.2⟩)
    have hid : (1 / 2 : ℝ) * Real.tan s * (u s) ^ 2
        = (1 / 2 : ℝ) * Real.sin s * u s * (u s / Real.cos s) := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    have hstep : |(1 / 2 : ℝ) * Real.sin s * u s * (u s / Real.cos s)|
        = (1 / 2 : ℝ) * |Real.sin s| * |u s| * |u s / Real.cos s| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
    rw [hid, hstep]
    have h1 : |Real.sin s| ≤ 1 := Real.abs_sin_le_one s
    have h2 : |u s / Real.cos s| ≤ max K 0 := le_trans (hK s hs) (le_max_left _ _)
    have h6 : |Real.sin s| * |u s / Real.cos s| ≤ max K 0 := by
      have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ (1 : ℝ))
      simpa using this
    calc (1 / 2 : ℝ) * |Real.sin s| * |u s| * |u s / Real.cos s|
        = (1 / 2 : ℝ) * |u s| * (|Real.sin s| * |u s / Real.cos s|) := by ring
      _ ≤ (1 / 2 : ℝ) * |u s| * max K 0 := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = (max K 0 / 2) * |u s| := by ring
  exact ⟨by simpa using hA0.add htan0, by simpa using hApi.add htanpi⟩

end Work.FTS.EllipticEst.Honest.SelfAux
