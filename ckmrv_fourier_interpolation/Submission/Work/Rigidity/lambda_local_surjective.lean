/-
# Local surjectivity of `λ` at the cusp `i∞`

`Work.Rigidity.LambdaLocalSurjective` states that `λ = θ₁₀⁴/θ₀₀⁴` maps the region
`Im τ > 1` onto a punctured neighbourhood of `0`.  The proof is the `q`-expansion of `λ`
at the cusp: writing `ζ = e^{π i τ}`,

  `λ(τ) = lambdaSeries ζ = 16 ζ (aSeries ζ)⁴ / (bSeries ζ)⁴ = 16 ζ + O(ζ²)`,

and `lambdaSeries` has a strict derivative `16 ≠ 0` at `ζ = 0`, so it maps every
neighbourhood of `0` onto a neighbourhood of `0` and is injective near `0`; a non-zero
`ζ` with `|ζ| < e^{-π}` is then `e^{π i τ}` for some `τ` with `Im τ > 1`.

The pieces of the `q`-expansion itself are proved in the companion modules
`Work.Rigidity.aSeries_sub_bound`, `Work.Rigidity.bSeries_sub_bound` (the two point
Lipschitz bounds for `aSeries` and `bSeries`) and `Work.Rigidity.lambdaFun_eq_lambdaSeries`
(the identity `λ(τ) = lambdaSeries (e^{π i τ})`).
-/
import Mathlib
import Submission.Work.Rigidity.LambdaDescentDefs
import Submission.Work.Rigidity.LambdaSeries
import Submission.Work.Rigidity.aSeries_sub_bound
import Submission.Work.Rigidity.bSeries_sub_bound
import Submission.Work.Rigidity.lambdaFun_eq_lambdaSeries

noncomputable section

open UpperHalfPlane Filter Topology

namespace Work.Rigidity

/-- Every non-zero `z` of modulus `< e^{-π}` is `e^{π i τ}` for some `τ ∈ ℍ` with
`1 < Im τ`, namely `τ = arg z / π + i (log ‖z‖⁻¹)/π`. -/
lemma exists_upperHalfPlane_cexp_eq {z : ℂ} (hz0 : z ≠ 0)
    (hz : ‖z‖ < Real.exp (-Real.pi)) :
    ∃ τ : ℍ, 1 < τ.im ∧ Complex.exp (Real.pi * Complex.I * (τ : ℂ)) = z := by
  have hρ : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set a : ℝ := Complex.arg z / Real.pi with ha
  set b : ℝ := Real.log ‖z‖⁻¹ / Real.pi with hb
  have hb1 : 1 < b := by
    rw [hb, Real.log_inv]
    have hlog : Real.log ‖z‖ < -Real.pi := by
      have h := Real.log_lt_log hρ hz
      rwa [Real.log_exp] at h
    have h : Real.log ‖z‖ / Real.pi < -1 := by
      rw [div_lt_iff₀ Real.pi_pos]
      linarith
    have h2 : -(Real.log ‖z‖) / Real.pi = -(Real.log ‖z‖ / Real.pi) := by ring
    rw [h2]
    linarith
  have hb0 : 0 < b := lt_trans zero_lt_one hb1
  have hkey : (Real.pi : ℂ) * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)
      = (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I := by
    have h1 : (Real.pi : ℂ) * (a : ℂ) = (Complex.arg z : ℂ) := by
      rw [ha, ← Complex.ofReal_mul]
      congr 1
      field_simp
    have h2 : (Real.pi : ℂ) * (b : ℂ) = (Real.log ‖z‖⁻¹ : ℂ) := by
      rw [hb, ← Complex.ofReal_mul]
      congr 1
      field_simp
    have h3 : (Real.log ‖z‖⁻¹ : ℂ) = -(Real.log ‖z‖ : ℂ) := by
      rw [Real.log_inv]; simp
    calc (Real.pi : ℂ) * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)
        = ((Real.pi : ℂ) * (a : ℂ)) * Complex.I
          + ((Real.pi : ℂ) * (b : ℂ)) * (Complex.I * Complex.I) := by ring
      _ = (Complex.arg z : ℂ) * Complex.I + (Real.log ‖z‖⁻¹ : ℂ) * (-1) := by
            rw [h1, h2, Complex.I_mul_I]
      _ = (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * Complex.I := by rw [h3]; ring
  have him : ((a : ℂ) + (b : ℂ) * Complex.I).im = b := by
    simp
  refine ⟨⟨(a : ℂ) + (b : ℂ) * Complex.I, ?_⟩, ?_, ?_⟩
  · rw [him]; exact hb0
  · show 1 < ((a : ℂ) + (b : ℂ) * Complex.I).im
    rw [him]; exact hb1
  · show Complex.exp (Real.pi * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I)) = z
    rw [hkey, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hρ]
    exact Complex.norm_mul_exp_arg_mul_I z

/-- **A two point bound with slope `c * r` gives strict differentiability at `0`.**
If `‖f x - f y‖ ≤ c r ‖x - y‖` for all `x, y` in the closed ball of radius `r ≤ 1/2`, then
`f` is strictly differentiable at `0` with derivative `0`. -/
lemma hasStrictDerivAt_zero_of_bound {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (h : ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ x y : ℂ, ‖x‖ ≤ r → ‖y‖ ≤ r →
      ‖f x - f y‖ ≤ c * r * ‖x - y‖) :
    HasStrictDerivAt f 0 0 := by
  rw [hasStrictDerivAt_iff_hasStrictFDerivAt, hasStrictFDerivAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  set r : ℝ := min (1 / 2) (ε / (2 * c)) with hr
  have hrpos : 0 < r := lt_min (by norm_num) (by positivity)
  have hrle : r ≤ 1 / 2 := min_le_left _ _
  have hreps : c * r ≤ ε / 2 := by
    have h2 : r ≤ ε / (2 * c) := min_le_right _ _
    calc c * r ≤ c * (ε / (2 * c)) := by gcongr
      _ = ε / 2 := by field_simp
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ × ℂ) hrpos] with p hp
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hp
  have hp1 : ‖p.1‖ ≤ r := by
    calc ‖p.1‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ r := le_of_lt hp
  have hp2 : ‖p.2‖ ≤ r := by
    calc ‖p.2‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      _ ≤ r := le_of_lt hp
  have hb := h r hrpos hrle p.1 p.2 hp1 hp2
  simp only [ContinuousLinearMap.toSpanSingleton_zero, zero_apply, sub_zero]
  calc ‖f p.1 - f p.2‖ ≤ c * r * ‖p.1 - p.2‖ := hb
    _ ≤ (ε / 2) * ‖p.1 - p.2‖ := mul_le_mul_of_nonneg_right hreps (norm_nonneg _)
    _ ≤ ε * ‖p.1 - p.2‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); linarith

/-- `aSeries` is strictly differentiable at `0` with derivative `0` (its only nonconstant
term of order `< 2` is absent). -/
lemma aSeries_hasStrictDerivAt_of
    (h : ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ x y : ℂ, ‖x‖ ≤ r → ‖y‖ ≤ r →
      ‖aSeries x - aSeries y‖ ≤ 16 * r * ‖x - y‖) :
    HasStrictDerivAt aSeries 0 0 :=
  hasStrictDerivAt_zero_of_bound (f := aSeries) (c := 16) (by norm_num) h

/-- `bSeries` is strictly differentiable at `0` with derivative `2`. -/
lemma bSeries_hasStrictDerivAt_of
    (h : ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ x y : ℂ, ‖x‖ ≤ r → ‖y‖ ≤ r →
      ‖bSeries x - bSeries y - 2 * (x - y)‖ ≤ 32 * r * ‖x - y‖) :
    HasStrictDerivAt bSeries 2 0 := by
  have hb : ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → ∀ x y : ℂ, ‖x‖ ≤ r → ‖y‖ ≤ r →
      ‖(bSeries x - 2 * x) - (bSeries y - 2 * y)‖ ≤ 32 * r * ‖x - y‖ := by
    intro r hr hr1 x y hx hy
    have hxy := h r hr hr1 x y hx hy
    have heq : bSeries x - 2 * x - (bSeries y - 2 * y)
        = bSeries x - bSeries y - 2 * (x - y) := by ring
    rw [heq]
    exact hxy
  have h0 : HasStrictDerivAt (fun z : ℂ => bSeries z - 2 * z) 0 0 :=
    hasStrictDerivAt_zero_of_bound (f := fun z : ℂ => bSeries z - 2 * z) (c := 32)
      (by norm_num) hb
  have h2 : HasStrictDerivAt (fun z : ℂ => 2 * z) 2 0 := by
    simpa using (hasStrictDerivAt_id (0 : ℂ)).const_mul (2 : ℂ)
  have h3 : HasStrictDerivAt (fun z : ℂ => (bSeries z - 2 * z) + 2 * z) (0 + 2) 0 :=
    h0.add h2
  have hfun : (fun z : ℂ => (bSeries z - 2 * z) + 2 * z) = bSeries := by
    funext z; ring
  rw [hfun] at h3
  simpa using h3

/-- `lambdaSeries` is strictly differentiable at `0` with derivative `16 ≠ 0`. -/
lemma lambdaSeries_hasStrictDerivAt_of
    (hA : HasStrictDerivAt aSeries 0 0) (hB : HasStrictDerivAt bSeries 2 0) :
    HasStrictDerivAt lambdaSeries 16 0 := by
  have hA4 : HasStrictDerivAt (fun z : ℂ => (aSeries z) ^ 4) _ 0 := hA.pow 4
  have hB4 : HasStrictDerivAt (fun z : ℂ => (bSeries z) ^ 4) _ 0 := hB.pow 4
  have hdiv : HasStrictDerivAt
      (fun z : ℂ => (aSeries z) ^ 4 / (bSeries z) ^ 4) _ 0 :=
    hA4.div hB4 (by rw [bSeries_zero]; norm_num)
  have hmul : HasStrictDerivAt
      (fun z : ℂ => 16 * z * ((aSeries z) ^ 4 / (bSeries z) ^ 4)) _ 0 :=
    ((hasStrictDerivAt_id (0 : ℂ)).const_mul (16 : ℂ)).mul hdiv
  have hfun : (fun z : ℂ => 16 * z * ((aSeries z) ^ 4 / (bSeries z) ^ 4)) = lambdaSeries := by
    funext z
    rw [lambdaSeries_apply]
    ring
  have hmul' : HasStrictDerivAt
      (fun z : ℂ => 16 * z * ((aSeries z) ^ 4 / (bSeries z) ^ 4)) 16 0 := by
    convert hmul using 1
    rw [aSeries_zero, bSeries_zero]
    norm_num
  rw [hfun] at hmul'
  exact hmul'

/-- **Local surjectivity of `λ` at the cusp from its `q`-expansion.**  If `lambdaSeries` is
the `q`-expansion of `λ` at the cusp and has strict derivative `16 ≠ 0` at the origin, then
`λ` maps `{Im τ > 1}` onto a punctured neighbourhood of `0`. -/
lemma lambda_local_surjective_of
    (hG : HasStrictDerivAt lambdaSeries 16 0)
    (hlam : ∀ τ : ℍ, Work.Kernels.lambdaFun τ
      = lambdaSeries (Complex.exp (Real.pi * Complex.I * (τ : ℂ)))) :
    LambdaLocalSurjective := by
  have hmap : Filter.map lambdaSeries (𝓝 (0 : ℂ)) = 𝓝 (lambdaSeries 0) :=
    hG.map_nhds_eq (by norm_num)
  rw [lambdaSeries_zero] at hmap
  set r : ℝ := Real.exp (-Real.pi) / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hrlt : r < Real.exp (-Real.pi) := by
    rw [hrdef]; linarith [Real.exp_pos (-Real.pi)]
  have hU : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hrpos
  have hV : lambdaSeries '' Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := by
    rw [← hmap]
    exact Filter.image_mem_map hU
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨δ, hδpos, ?_⟩
  intro w hw hwlt
  have hwball : w ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_zero_right]; exact hwlt
  obtain ⟨ζ, hζball, hζeq⟩ := hδsub hwball
  have hζnorm : ‖ζ‖ < Real.exp (-Real.pi) := by
    have h := Metric.mem_ball.mp hζball
    rw [dist_zero_right] at h
    exact lt_trans h hrlt
  have hζne : ζ ≠ 0 := by
    rintro rfl
    rw [lambdaSeries_zero] at hζeq
    exact hw hζeq.symm
  obtain ⟨τ, hτim, hτζ⟩ := exists_upperHalfPlane_cexp_eq hζne hζnorm
  exact ⟨τ, hτim, by rw [hlam τ, hτζ, hζeq]⟩

/-- `aSeries` is strictly differentiable at `0` with derivative `0`. -/
lemma aSeries_hasStrictDerivAt : HasStrictDerivAt aSeries 0 0 :=
  hasStrictDerivAt_zero_of_bound (f := aSeries) (c := 16) (by norm_num)
    (fun r hr hr1 x y hx hy => aSeries_sub_bound r hr hr1 x y hx hy)

/-- `bSeries` is strictly differentiable at `0` with derivative `2`. -/
lemma bSeries_hasStrictDerivAt : HasStrictDerivAt bSeries 2 0 :=
  bSeries_hasStrictDerivAt_of
    (fun r hr hr1 x y hx hy => bSeries_sub_bound r hr hr1 x y hx hy)

/-- `lambdaSeries` is strictly differentiable at `0` with derivative `16 ≠ 0`. -/
lemma lambdaSeries_hasStrictDerivAt : HasStrictDerivAt lambdaSeries 16 0 :=
  lambdaSeries_hasStrictDerivAt_of aSeries_hasStrictDerivAt bSeries_hasStrictDerivAt

/-- **The theorem.**  `λ` maps the region `Im τ > 1` onto a punctured neighbourhood of `0`. -/
theorem lambda_local_surjective : Work.Rigidity.LambdaLocalSurjective :=
  lambda_local_surjective_of lambdaSeries_hasStrictDerivAt
    (fun τ => lambdaFun_eq_lambdaSeries τ)

end Work.Rigidity
