/-
# Boundedness at the cusp `i∞` for periodic functions of moderate growth

The class `𝒫 = Work.Kernels.InP` of CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska,
*Universal optimality of the E8 and Leech lattices*, Ann. of Math. 196 (2022), Section 4.1)
consists of the holomorphic `h : ℍ → ℂ` of moderate growth

  `‖h τ‖ ≤ α * ((im τ)⁻¹ ^ β + ‖τ‖ ^ γ)`   (`α β γ ≥ 0`).

Such an `h` that is in addition periodic of period `1` is bounded at the cusp: the periodicity
lets us write `h = F ∘ 𝕢` with `𝕢 = qParam 1` and `F = Function.Periodic.cuspFunction 1 h`; a
moderate growth bound in `τ` is a bound of the shape `(1 + |log ‖q‖|) ^ N` in `q`, which is
slower than any negative power of `‖q‖`, so Riemann's removable singularity theorem (`Riemann's
theorem`, Mathlib's `Complex.differentiableOn_update_limUnder_of_isLittleO`) extends `F` across
`0`.  Since `‖𝕢 1 τ‖ = e^{-2π im τ} → 0`, boundedness of `F` near `0` is boundedness of `h` at
`i∞`.

## Main result

* `Work.Rigidity.boundedAtImInfty_of_periodic_inP`.

The proof goes through the following auxiliary statements, all private to this file:

* `tendsto_one_add_abs_log_rpow_mul`, `tendsto_logPow_mul` : `t (1 + |log t|) ^ N → 0` as
  `t → 0⁺`, which is the quantitative content of Riemann's theorem used here;
* `logPowGrowthRemovable` : removable singularity under growth `C (1 + |log ‖q‖|) ^ N`
  (the existing `Work.Analysis.RemovableSingularity.logGrowthRemovable` is the case `N = 1`);
* `invQParam_scale_bound`, `cuspFunction_growth` : the translation of moderate growth on `ℍ`
  into logarithmic growth on the punctured disc;
* `periodic_lift`, `differentiableAt_lift` : the lift `h ∘ ofComplex` is `1`-periodic and
  holomorphic on `ℍ`, so that its cusp function is holomorphic on the punctured disc.
-/
import Mathlib
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Analysis.RemovableSingularity.logGrowthRemovable

noncomputable section

open UpperHalfPlane Filter Topology Asymptotics
open scoped Topology Manifold

namespace Work.Rigidity

/-! ## The real-analytic limit `t (1 + |log t|) ^ N → 0` as `t → 0⁺` -/

private lemma tendsto_one_add_abs_log_rpow_mul (N : ℝ) (hN : 0 ≤ N) :
    Tendsto (fun t : ℝ => (1 + |Real.log t|) ^ N * t) (𝓝[>] 0) (𝓝 0) := by
  -- `|log t| ^ N * t → 0`: since `|log t| ^ N = o(t ^ (-1/2))`, multiplying by `t ^ (1/2)`
  -- gives `|log t| ^ N * t ^ (1/2) → 0`, and one more factor `t ^ (1/2)` gives the claim.
  have hf : Tendsto (fun t : ℝ => |Real.log t| ^ N * t) (𝓝[>] 0) (𝓝 0) := by
    have h1 : (fun t : ℝ => |Real.log t| ^ N) =o[𝓝[>] (0:ℝ)]
        (fun t : ℝ => t ^ (-1/2 : ℝ)) :=
      isLittleO_abs_log_rpow_rpow_nhdsGT_zero N (by norm_num)
    have hA : Tendsto (fun t : ℝ => |Real.log t| ^ N / t ^ (-1/2 : ℝ)) (𝓝[>] 0) (𝓝 0) :=
      h1.tendsto_div_nhds_zero
    have hB : Tendsto (fun t : ℝ => t ^ (1/2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ => t ^ (1/2 : ℝ)) 0 :=
        Real.continuousAt_rpow_const 0 (1/2 : ℝ) (Or.inr (by norm_num))
      simpa [Real.zero_rpow (by norm_num : (1/2 : ℝ) ≠ 0)] using
        hc.tendsto.mono_left nhdsWithin_le_nhds
    have hmul := hA.mul hB
    simp only [mul_zero] at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h1' : (t ^ (-1/2 : ℝ))⁻¹ = t ^ (1/2 : ℝ) := by
      rw [← Real.rpow_neg ht.le]; norm_num
    rw [div_eq_mul_inv, h1', mul_assoc, ← Real.rpow_add ht]
    norm_num
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hupper : Tendsto (fun t : ℝ => 2 ^ N * t + 2 ^ N * (|Real.log t| ^ N * t))
      (𝓝[>] 0) (𝓝 0) := by
    have h := (ht.const_mul (2 ^ N)).add (hf.const_mul (2 ^ N))
    simpa using h
  -- `(1 + |log t|) ^ N ≤ 2 ^ N (1 + |log t| ^ N)`
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_nonneg (Real.rpow_nonneg (by positivity) N) ht.le
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hmax : 1 + |Real.log t| ≤ 2 * max 1 |Real.log t| := by
      rcases le_total 1 |Real.log t| with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hmul : (2 * max 1 |Real.log t|) ^ N = 2 ^ N * (max 1 |Real.log t|) ^ N :=
      Real.mul_rpow (by norm_num) (le_trans zero_le_one (le_max_left _ _))
    have hmaxN : (max 1 |Real.log t|) ^ N = max (1 ^ N) (|Real.log t| ^ N) := by
      rcases le_total 1 |Real.log t| with h | h
      · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow zero_le_one h hN)]
      · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow (abs_nonneg _) h hN)]
    have hstep : (1 + |Real.log t|) ^ N ≤ 2 ^ N * (1 + |Real.log t| ^ N) := by
      calc (1 + |Real.log t|) ^ N ≤ (2 * max 1 |Real.log t|) ^ N :=
            Real.rpow_le_rpow (by positivity) hmax hN
        _ = 2 ^ N * (max 1 |Real.log t|) ^ N := hmul
        _ = 2 ^ N * max (1 ^ N) (|Real.log t| ^ N) := by rw [hmaxN]
        _ ≤ 2 ^ N * (1 + |Real.log t| ^ N) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [Real.one_rpow]
            exact max_le (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg (Real.log t)) N))
              (le_add_of_nonneg_left (by norm_num))
    calc (1 + |Real.log t|) ^ N * t ≤ (2 ^ N * (1 + |Real.log t| ^ N)) * t :=
          mul_le_mul_of_nonneg_right hstep ht.le
      _ = 2 ^ N * t + 2 ^ N * (|Real.log t| ^ N * t) := by ring

private lemma tendsto_logPow_mul (C D N : ℝ) (hN : 0 ≤ N) :
    Tendsto (fun t : ℝ => (C * (1 + |Real.log t|) ^ N + D) * t) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_one_add_abs_log_rpow_mul N hN
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hsum : Tendsto (fun t : ℝ => C * ((1 + |Real.log t|) ^ N * t) + D * t)
      (𝓝[>] 0) (𝓝 0) := by
    have h' := (h.const_mul C).add (ht.const_mul D)
    simpa using h'
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  ring

/-! ## Removable singularity under polynomial logarithmic growth -/

/-- A function holomorphic on a punctured disc `0 < ‖z‖ < ρ` growing at most like a power of
`|log ‖z‖|` extends holomorphically across `0`.  (The case `N = 1` is
`Work.Analysis.RemovableSingularity.logGrowthRemovable`.) -/
private theorem logPowGrowthRemovable {G : ℂ → ℂ} {ρ C N : ℝ} (hρ : 0 < ρ) (hN : 0 ≤ N)
    (hG : DifferentiableOn ℂ G (Metric.ball 0 ρ \ {0}))
    (hgr : ∀ q : ℂ, q ≠ 0 → ‖q‖ < ρ → ‖G q‖ ≤ C * (1 + |Real.log ‖q‖|) ^ N) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧
      ∀ q : ℂ, q ≠ 0 → ‖q‖ < ρ → F q = G q := by
  have hev : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 ∧ ‖z‖ < ρ := by
    have hball : Metric.ball (0 : ℂ) ρ ∈ 𝓝[≠] (0 : ℂ) :=
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (by simpa using hρ))
    filter_upwards [self_mem_nhdsWithin, hball] with z hz hzb
    exact ⟨hz, by simpa [Metric.mem_ball, dist_eq_norm] using hzb⟩
  have hbound : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
      ‖(G z - G 0) * z‖ ≤ (C * (1 + |Real.log ‖z‖|) ^ N + ‖G 0‖) * ‖z‖ := by
    filter_upwards [hev] with z hz
    obtain ⟨hz0, hzlt⟩ := hz
    calc
      ‖(G z - G 0) * z‖ = ‖G z - G 0‖ * ‖z‖ := norm_mul _ _
      _ ≤ (‖G z‖ + ‖G 0‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ (C * (1 + |Real.log ‖z‖|) ^ N + ‖G 0‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (add_le_add (hgr z hz0 hzlt) le_rfl) (norm_nonneg _)
  have htend : Tendsto (fun z : ℂ => (C * (1 + |Real.log ‖z‖|) ^ N + ‖G 0‖) * ‖z‖)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_logPow_mul C ‖G 0‖ N hN).comp (tendsto_norm_nhdsNE_zero (E := ℂ))
  have hsq : Tendsto (fun z : ℂ => ‖(G z - G 0) * z‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) hbound htend
  have hmain : Tendsto (fun z : ℂ => (G z - G 0) * z) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hsq
  have hlittle : (fun z : ℂ => G z - G 0) =o[𝓝[≠] (0 : ℂ)] (fun z => (z - 0)⁻¹) := by
    refine (isLittleO_iff_tendsto ?_).mpr ?_
    · intro z hz
      have hz0 : z = 0 := sub_eq_zero.mp (inv_eq_zero.mp hz)
      simp [hz0]
    · show Tendsto (fun z : ℂ => (G z - G 0) / (z - 0)⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 0)
      simpa only [div_inv_eq_mul, sub_zero] using hmain
  refine ⟨Function.update G 0 ((𝓝[≠] (0 : ℂ)).limUnder G), ?_, ?_⟩
  · exact Complex.differentiableOn_update_limUnder_of_isLittleO
      (Metric.isOpen_ball.mem_nhds (by simpa using hρ)) hG hlittle
  · intro q hq _
    exact Function.update_of_ne hq _ _

/-! ## The lift of `h` to `ℂ`: periodicity and holomorphy -/

/-- The lift `h ∘ ofComplex : ℂ → ℂ` of a `1`-periodic function on `ℍ` is `1`-periodic. -/
private lemma periodic_lift {h : ℍ → ℂ} (hper : ∀ τ : ℍ, h ((1 : ℝ) +ᵥ τ) = h τ) :
    Function.Periodic (h ∘ UpperHalfPlane.ofComplex) 1 := by
  intro z
  simp only [Function.comp_apply]
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + 1).im := by simpa using hz
    rw [ofComplex_apply_of_im_pos hz', ofComplex_apply_of_im_pos hz]
    have hcoe : (⟨z + 1, hz'⟩ : ℍ) = (1 : ℝ) +ᵥ (⟨z, hz⟩ : ℍ) := by
      apply UpperHalfPlane.coe_inj.mp
      rw [coe_vadd]
      push_cast
      ring
    rw [hcoe, hper]
  · have hzle : z.im ≤ 0 := not_lt.mp hz
    have hz' : (z + 1).im ≤ 0 := by simpa using hzle
    have h1 : UpperHalfPlane.ofComplex (z + 1) = Classical.choice (inferInstance : Nonempty ℍ) :=
      ofComplex_apply_of_im_nonpos hz'
    have h2 : UpperHalfPlane.ofComplex z = Classical.choice (inferInstance : Nonempty ℍ) :=
      ofComplex_apply_of_im_nonpos hzle
    rw [h1, h2]

/-- The lift `h ∘ ofComplex` of a holomorphic `h : ℍ → ℂ` is holomorphic on `{0 < im z}`. -/
private lemma differentiableAt_lift {h : ℍ → ℂ} (hP : Work.Kernels.InP h) :
    ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ (h ∘ UpperHalfPlane.ofComplex) z := by
  intro z hz
  have h := (UpperHalfPlane.mdifferentiableAt_iff (f := h) (τ := (⟨z, hz⟩ : ℍ))).mp
    (hP.1 ⟨z, hz⟩)
  simpa using h

/-! ## Moderate growth at `i∞` is logarithmic growth at `0` -/

/-- For `q ≠ 0` with `‖q‖ ≤ 1/2`, the point `τ = invQParam 1 q ∈ ℍ` satisfies
`1 + (im τ)⁻¹ + ‖τ‖ ≤ K (1 + |log ‖q‖|)` with `K = 1 + 2π/log 2 + (1/2 + 1/(2π))`. -/
private lemma invQParam_scale_bound {q : ℂ} (hq : q ≠ 0) (hq2 : ‖q‖ ≤ 1 / 2) :
    1 + ((Function.Periodic.invQParam 1 q).im)⁻¹ + ‖Function.Periodic.invQParam 1 q‖
      ≤ (1 + 2 * Real.pi / Real.log 2 + (1 / 2 + 1 / (2 * Real.pi))) * (1 + |Real.log ‖q‖|) := by
  set K : ℝ := 1 + 2 * Real.pi / Real.log 2 + (1 / 2 + 1 / (2 * Real.pi)) with hKdef
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq
  -- `log 2 ≤ -log ‖q‖`, i.e. `2 ‖q‖ ≤ 1`
  have h2 : Real.log 2 ≤ -Real.log ‖q‖ := by
    have hmul : Real.log 2 + Real.log ‖q‖ ≤ 0 := by
      rw [← Real.log_mul (by norm_num) hqpos.ne']
      exact Real.log_nonpos (by positivity) (by linarith)
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have him : (Function.Periodic.invQParam 1 q).im = -Real.log ‖q‖ / (2 * Real.pi) := by
    rw [Function.Periodic.im_invQParam]; ring
  have hre : (Function.Periodic.invQParam 1 q).re = q.arg / (2 * Real.pi) := by
    simp [Function.Periodic.invQParam, Complex.log_re, Complex.log_im]
    ring
  have hL : 0 < -Real.log ‖q‖ := by linarith
  -- the real part is `arg q / (2π)` with `|arg q| ≤ π`
  have hnormre : |(Function.Periodic.invQParam 1 q).re| ≤ 1 / 2 := by
    rw [hre, abs_div]
    have harg : |q.arg| ≤ Real.pi :=
      abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg q), Complex.arg_le_pi q⟩
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [abs_of_pos h2pi, div_le_iff₀ h2pi]
    linarith
  have hnorm : ‖Function.Periodic.invQParam 1 q‖ ≤ 1 / 2 + (-Real.log ‖q‖) / (2 * Real.pi) := by
    calc ‖Function.Periodic.invQParam 1 q‖
        ≤ |(Function.Periodic.invQParam 1 q).re| + |(Function.Periodic.invQParam 1 q).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |(Function.Periodic.invQParam 1 q).re| + (-Real.log ‖q‖) / (2 * Real.pi) := by
          rw [him, abs_div, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      _ ≤ 1 / 2 + (-Real.log ‖q‖) / (2 * Real.pi) := by linarith
  have hinv : ((Function.Periodic.invQParam 1 q).im)⁻¹ ≤ 2 * Real.pi / Real.log 2 := by
    rw [him, inv_div]
    exact div_le_div_of_nonneg_left (by positivity) hlog2pos h2
  have hmain : 1 + ((Function.Periodic.invQParam 1 q).im)⁻¹ + ‖Function.Periodic.invQParam 1 q‖ ≤
      1 + 2 * Real.pi / Real.log 2 + (1 / 2 + (-Real.log ‖q‖) / (2 * Real.pi)) := by linarith
  have hK1 : 1 + 2 * Real.pi / Real.log 2 + 1 / 2 ≤ K := by
    have : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
    simp only [hKdef]; linarith
  have hK2 : 1 / (2 * Real.pi) ≤ K := by
    have : (0 : ℝ) ≤ 1 + 2 * Real.pi / Real.log 2 + 1 / 2 := by positivity
    simp only [hKdef]; linarith
  have hgoal : 1 + 2 * Real.pi / Real.log 2 + (1 / 2 + (-Real.log ‖q‖) / (2 * Real.pi)) ≤
      K * (1 + |Real.log ‖q‖|) := by
    rw [abs_of_neg (by linarith : Real.log ‖q‖ < 0), mul_add, mul_one]
    have hL0 : (0 : ℝ) ≤ -Real.log ‖q‖ := hL.le
    have step : (-Real.log ‖q‖) / (2 * Real.pi) ≤ K * (-Real.log ‖q‖) := by
      have h' := mul_le_mul_of_nonneg_right hK2 hL0
      simpa [div_eq_inv_mul] using h'
    linarith
  linarith [hmain, hgoal]

/-- Moderate growth of `h` on `ℍ` bounds its cusp function on the disc `‖q‖ ≤ 1/2` by
`C (1 + |log ‖q‖|) ^ N`. -/
private lemma cuspFunction_growth {h : ℍ → ℂ} (hgr : Work.Kernels.ModerateGrowthOn Set.univ h) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ q : ℂ, q ≠ 0 → ‖q‖ ≤ 1 / 2 →
      ‖Function.Periodic.cuspFunction 1 (h ∘ UpperHalfPlane.ofComplex) q‖
        ≤ C * (1 + |Real.log ‖q‖|) ^ N := by
  obtain ⟨α, N, hα, hN, hb⟩ := (Work.Kernels.moderateGrowthOn_iff_scale Set.univ h).mp hgr
  set K : ℝ := 1 + 2 * Real.pi / Real.log 2 + (1 / 2 + 1 / (2 * Real.pi)) with hKdef
  refine ⟨α * K ^ N, N, by positivity, hN, fun q hq hq2 => ?_⟩
  have hq_lt1 : ‖q‖ < 1 := lt_of_le_of_lt hq2 (by norm_num)
  have him : 0 < (Function.Periodic.invQParam 1 q).im :=
    Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq_lt1 hq
  set τ : ℍ := ⟨Function.Periodic.invQParam 1 q, him⟩ with hτ
  have hval : Function.Periodic.cuspFunction 1 (h ∘ UpperHalfPlane.ofComplex) q = h τ := by
    rw [Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hq, Function.comp_apply,
      ofComplex_apply_of_im_pos him]
  rw [hval]
  have hKpos : (0 : ℝ) < K := by
    simp only [hKdef]; positivity
  have hbase : (0 : ℝ) ≤ 1 + |Real.log ‖q‖| := by positivity
  have hscale' : Work.Kernels.scale τ
      ≤ (1 + 2 * Real.pi / Real.log 2 + (1 / 2 + 1 / (2 * Real.pi))) * (1 + |Real.log ‖q‖|) := by
    simpa [Work.Kernels.scale, hτ] using invQParam_scale_bound hq hq2
  have hscale : Work.Kernels.scale τ ≤ K * (1 + |Real.log ‖q‖|) := by
    rw [hKdef]
    exact hscale'
  calc ‖h τ‖ ≤ α * (Work.Kernels.scale τ) ^ N := hb τ (Set.mem_univ τ)
    _ ≤ α * (K * (1 + |Real.log ‖q‖|)) ^ N :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Work.Kernels.scale_pos τ).le hscale hN) hα
    _ = α * K ^ N * (1 + |Real.log ‖q‖|) ^ N := by
          rw [Real.mul_rpow hKpos.le hbase]; ring

/-! ## The main theorem -/

/-- A holomorphic function on the upper half plane that is periodic of period `1` and of
moderate growth (i.e. lies in the CKMRV class `𝒫 = Work.Kernels.InP`: holomorphic and
`‖h τ‖ ≤ α * ((τ.im)⁻¹ ^ β + ‖τ‖ ^ γ)`) is **bounded** at the cusp `i∞`.

Sketch.  Write `h = F ∘ 𝕢` with `F = UpperHalfPlane.cuspFunction 1 h`, a function holomorphic
on the punctured unit disc `D*`.  For `q ≠ 0` with `‖q‖ < 1` and `τ = Periodic.invQParam 1 q`
one has `F q = h τ`, `im τ = -Real.log ‖q‖ / (2π)` (`Periodic.im_invQParam`), and
`τ.re = (arg q)/(2π)`, so `‖τ‖ ≤ 1/2 + |Real.log ‖q‖| / (2π)`.  The moderate growth bound then
gives `‖F q‖ ≤ C * (1 + |Real.log ‖q‖|) ^ N` for `q` in a punctured neighbourhood of `0`, i.e.
growth slower than any negative power of `‖q‖`.  Riemann's removable singularity theorem
(or the existing `Work.Analysis.RemovableSingularity.logGrowthRemovable`, generalised from
growth `(1 + |log ‖q‖|)` to `(1 + |log ‖q‖|) ^ N`: still `t * (1+|log t|)^N → 0` as `t → 0⁺`)
extends `F` holomorphically across `0`, so `F` is bounded near `0`; since `‖𝕢 1 τ‖ = e^{-2π τ.im}`
one gets `IsBoundedAtImInfty h`. -/
theorem boundedAtImInfty_of_periodic_inP {h : UpperHalfPlane → ℂ} (hP : Work.Kernels.InP h)
    (hper : ∀ τ : UpperHalfPlane, h ((1 : ℝ) +ᵥ τ) = h τ) :
    UpperHalfPlane.IsBoundedAtImInfty h := by
  have hper_g : Function.Periodic (h ∘ UpperHalfPlane.ofComplex) 1 := periodic_lift hper
  have hdiffg : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ (h ∘ UpperHalfPlane.ofComplex) z :=
    differentiableAt_lift hP
  -- the cusp function is holomorphic on the punctured disc of radius `1/2`
  have hdiffOn : DifferentiableOn ℂ
      (Function.Periodic.cuspFunction 1 (h ∘ UpperHalfPlane.ofComplex))
      (Metric.ball 0 (1/2) \ {0}) := by
    intro q hq
    have hq0 : q ≠ 0 := by simpa using hq.2
    have hqlt : ‖q‖ < 1 / 2 := by
      have h := hq.1
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h
    have him : 0 < (Function.Periodic.invQParam 1 q).im :=
      Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos (by linarith) hq0
    have hd : DifferentiableAt ℂ
        (Function.Periodic.cuspFunction 1 (h ∘ UpperHalfPlane.ofComplex))
        (Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 q)) :=
      Function.Periodic.differentiableAt_cuspFunction one_ne_zero hper_g (hdiffg _ him)
    rw [Function.Periodic.qParam_right_inv one_ne_zero hq0] at hd
    exact hd.differentiableWithinAt
  obtain ⟨C, N, hC, hN, hbound⟩ := cuspFunction_growth hP.2
  obtain ⟨F, hFdiff, hFeq⟩ :=
    logPowGrowthRemovable (ρ := 1/2) (C := C) (N := N) (by norm_num) hN hdiffOn
      (fun q hq hqlt => hbound q hq hqlt.le)
  -- `F` is bounded near `0`
  have hFcont : ContinuousAt F 0 :=
    hFdiff.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (by norm_num))
  have hevbd : ∀ᶠ q : ℂ in 𝓝 0, ‖F q‖ ≤ ‖F 0‖ + 1 :=
    hFcont.norm.eventually (eventually_le_nhds (lt_add_one ‖F 0‖))
  -- along the cusp, `qParam 1 τ → 0`
  have htend_q : Tendsto (fun τ : ℍ => Function.Periodic.qParam 1 (τ : ℂ)) atImInfty (𝓝 0) :=
    ((Function.Periodic.qParam_tendsto (h := 1) one_pos).comp
      UpperHalfPlane.tendsto_coe_atImInfty).mono_right nhdsWithin_le_nhds
  have hev1 : ∀ᶠ τ : ℍ in atImInfty,
      ‖F (Function.Periodic.qParam 1 (τ : ℂ))‖ ≤ ‖F 0‖ + 1 :=
    htend_q.eventually hevbd
  have hev2 : ∀ᶠ τ : ℍ in atImInfty, ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 / 2 := by
    filter_upwards [htend_q.eventually
      (Metric.isOpen_ball.mem_nhds (by norm_num : (0 : ℂ) ∈ Metric.ball 0 (1/2)))] with τ hτ
    simpa [dist_eq_norm] using hτ
  have hev3 : ∀ᶠ τ : ℍ in atImInfty, h τ = F (Function.Periodic.qParam 1 (τ : ℂ)) := by
    filter_upwards [hev2] with τ hs
    have hq0 : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
    have e1 : h τ = (h ∘ UpperHalfPlane.ofComplex) (τ : ℂ) := by
      simp [Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    have e2 : (h ∘ UpperHalfPlane.ofComplex) (τ : ℂ) =
        Function.Periodic.cuspFunction 1 (h ∘ UpperHalfPlane.ofComplex)
          (Function.Periodic.qParam 1 (τ : ℂ)) :=
      (Function.Periodic.eq_cuspFunction one_ne_zero hper_g (τ : ℂ)).symm
    have e3 : F (Function.Periodic.qParam 1 (τ : ℂ)) =
        Function.Periodic.cuspFunction 1 (h ∘ UpperHalfPlane.ofComplex)
          (Function.Periodic.qParam 1 (τ : ℂ)) := hFeq _ hq0 hs
    rw [e1, e2, e3]
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hev : {τ : ℍ | ‖h τ‖ ≤ ‖F 0‖ + 1} ∈ atImInfty := by
    filter_upwards [hev1, hev3] with τ h1 h3
    rw [h3]; exact h1
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp hev
  exact ⟨‖F 0‖ + 1, A, fun z hz => hA z hz⟩

end Work.Rigidity
