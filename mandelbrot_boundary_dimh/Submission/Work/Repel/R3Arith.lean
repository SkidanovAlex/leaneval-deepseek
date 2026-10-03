import Mathlib
import Submission.Work.Repel.deriv_bound_on_ball_explicit

open Set Metric Filter Topology
open scoped Topology

/-!
# REPEL3: the arithmetic of the assembly, in small contexts

The assembly `Work.Repel.repel3` carries a very large context (all the §6 hypotheses, the
`PertData`s, ...).  Every `linarith`/`nlinarith`/`positivity`/`field_simp` run there pays for
every hypothesis, which made the single-file version of `repel3` blow up in elaboration time.
The arithmetic steps are therefore isolated here, in lemmas whose context is a handful of real
variables.

* `eta_le_cube`: `η ≤ η³` for `η ≥ 1`;
* `fit_arith`: the fit condition `hfit` of `Work.Repel.chain_returns_v7` from the scale
  condition `η³ ≥ 256/(320(C₀+1)10¹²Cb²(C₁'+1)²)` (this is where v7's `η₁` in place of
  `exp (2πη)` makes the condition *independent of `s`*: `η₁²` cancels);
* `kc_bound_arith`: the derivative bound of `chain_returns_v7`
  (`Kc ≤ 10⁶ Cb (C₁'+1) η² η₁`) turned into the `exp (2πη)`-form used by `Work.Repel.dim_arith`,
  absorbing the `‖s‖⁻¹` into the constant, and with `max Kc 2`.
-/

namespace Work.Repel

theorem eta_le_cube {η : ℝ} (h : 1 ≤ η) : η ≤ η ^ 3 := by
  have h0 : 0 ≤ η := by linarith
  have h1 : 0 ≤ η - 1 := by linarith
  have h2 : 0 ≤ η + 1 := by linarith
  nlinarith [mul_nonneg (mul_nonneg h0 h1) h2]

/-- **The fit condition of `chain_returns_v7`.**  From `η ≥ 1`, `η₁ > 0`, `Cb > 0`, `C₀ + 1 > 0`
and `256 ≤ η³ · 320(C₀+1) · 10¹²Cb²(C₁'+1)²` — equivalently `η` above the threshold
`256 / (320(C₀+1)10¹²Cb²(C₁'+1)²)`, which does **not** involve `s`. -/
theorem fit_arith {η η₁ Cb C₀ C₁' : ℝ} (hη : 1 ≤ η) (hη₁ : 0 < η₁) (hCb : 0 < Cb)
    (hC₀ : 0 < C₀ + 1) (hC₁ : 0 < C₁')
    (hkey : 256 ≤ η ^ 3 * (320 * (C₀ + 1) * (10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2))) :
    η * η₁ ^ 2 / (320 * (C₀ + 1)) ≤ (10 ^ 6 * Cb * (C₁' + 1) * η ^ 2 * η₁) ^ 2 / 256 := by
  have hηpos : 0 < η := by linarith
  have hD : 0 < 320 * (C₀ + 1) := by linarith
  have hM : 0 < 10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hCb 2)) (pow_pos (by linarith) 2)
  have h1 : 1 / (320 * (C₀ + 1)) ≤ 10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2 * η ^ 3 / 256 := by
    rw [div_le_iff₀ hD, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 256)]
    nlinarith [hkey]
  have h2 : η / (320 * (C₀ + 1)) ≤ 10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2 * η ^ 4 / 256 := by
    have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hηpos)
    calc η / (320 * (C₀ + 1)) = η * (1 / (320 * (C₀ + 1))) := by ring
      _ ≤ η * (10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2 * η ^ 3 / 256) := h3
      _ = 10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2 * η ^ 4 / 256 := by ring
  have hη₁2 : 0 < η₁ ^ 2 := pow_pos hη₁ 2
  have h4 := mul_le_mul_of_nonneg_left h2 (le_of_lt hη₁2)
  calc η * η₁ ^ 2 / (320 * (C₀ + 1)) = η₁ ^ 2 * (η / (320 * (C₀ + 1))) := by ring
    _ ≤ η₁ ^ 2 * (10 ^ 12 * Cb ^ 2 * (C₁' + 1) ^ 2 * η ^ 4 / 256) := h4
    _ = (10 ^ 6 * Cb * (C₁' + 1) * η ^ 2 * η₁) ^ 2 / 256 := by ring

/-- The derivative bound of `chain_returns_v7` (`Kc ≤ 10⁶ Cb (C₁'+1) η² η₁`), rewritten in the
`exp (2πη)`-form required by `Work.Repel.dim_arith` (the `‖s‖⁻¹` becomes part of the constant),
together with `max Kc 2`. -/
theorem kc_bound_arith {Kc Cb C₁' η η₁ s : ℝ} (hKc : Kc ≤ 10 ^ 6 * Cb * (C₁' + 1) * η ^ 2 * η₁)
    (hη₁ : η₁ * s = Real.exp (2 * Real.pi * η)) (hs : 0 < s) (hCb : 0 < Cb)
    (hη : 1 ≤ η) :
    max Kc 2 ≤ (10 ^ 6 * Cb * (|C₁'| + 1) / s + 2) * η ^ 2 * Real.exp (2 * Real.pi * η) := by
  have hη₁' : η₁ = Real.exp (2 * Real.pi * η) / s := by
    rw [eq_div_iff (ne_of_gt hs)]
    exact hη₁
  have hE : (1 : ℝ) ≤ Real.exp (2 * Real.pi * η) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hEp : 0 < Real.exp (2 * Real.pi * η) := Real.exp_pos _
  have hη2 : (1 : ℝ) ≤ η ^ 2 := by nlinarith
  have h2E : (1 : ℝ) ≤ η ^ 2 * Real.exp (2 * Real.pi * η) := by nlinarith
  have hcoef : (0 : ℝ) ≤ 10 ^ 6 * Cb * (|C₁'| + 1) / s := by positivity
  have hle : C₁' + 1 ≤ |C₁'| + 1 := by nlinarith [le_abs_self C₁']
  rw [hη₁'] at hKc
  have hkey : 10 ^ 6 * Cb * (C₁' + 1) * (η ^ 2 * (Real.exp (2 * Real.pi * η) / s)) ≤
      10 ^ 6 * Cb * (|C₁'| + 1) * (η ^ 2 * (Real.exp (2 * Real.pi * η) / s)) := by
    have hpos : (0 : ℝ) ≤ 10 ^ 6 * Cb * (η ^ 2 * (Real.exp (2 * Real.pi * η) / s)) := by
      positivity
    nlinarith [hle, hpos]
  have hval : 10 ^ 6 * Cb * (|C₁'| + 1) * (η ^ 2 * (Real.exp (2 * Real.pi * η) / s)) =
      (10 ^ 6 * Cb * (|C₁'| + 1) / s) * (η ^ 2 * Real.exp (2 * Real.pi * η)) := by ring
  have hfin : (10 ^ 6 * Cb * (|C₁'| + 1) / s) * (η ^ 2 * Real.exp (2 * Real.pi * η)) ≤
      (10 ^ 6 * Cb * (|C₁'| + 1) / s + 2) * (η ^ 2 * Real.exp (2 * Real.pi * η)) := by
    nlinarith [hcoef, h2E]
  refine max_le ?_ ?_
  · linarith [hKc, hkey, hval, hfin]
  · nlinarith [hcoef, h2E]

/-! ## Derivative lower bounds on a small disc (v8 of the §6 link)

`chain_returns_v8` needs a *lower* bound for the target-side factor
`‖(P₀.φ)'‖·‖(P₁.φ)'‖·‖(π⁻¹)'‖` (hypothesis `hcblo`), i.e. lower bounds for `‖(P.φ)'‖` on the
target discs.  These are obtained from the derivatives of the *unperturbed* coordinates
(`d.φ' ≠ 0` at the target points, `invOrbit`) plus the uniform closeness `P.φ_close`:

* `deriv_close_of_close` (Cauchy's estimate for the difference of two holomorphic functions);
* `deriv_lower_half`, `norm_upper_double` (continuity of `deriv g` resp. of `g` at a point);
* `fitlo_arith` and the threshold bookkeeping for `hfitlo`. -/

theorem deriv_close_of_close {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) {c : ℂ} {R δ : ℝ} (hR : 0 < R)
    (hsub : Metric.closedBall c (2 * R) ⊆ U)
    (hclose : ∀ z ∈ Metric.closedBall c (2 * R), ‖f z - g z‖ ≤ δ) :
    ∀ z ∈ Metric.closedBall c R, ‖deriv f z - deriv g z‖ ≤ max δ 1 / R := by
  have h := deriv_bound_on_ball_explicit (g := fun z => f z - g z) (U := U) (hf.sub hg) hR hsub
    hclose
  intro z hz
  have hmem : z ∈ U := hsub (Metric.closedBall_subset_closedBall (by linarith) hz)
  have heq : deriv (fun z => f z - g z) z = deriv f z - deriv g z := by
    have hsub' : (fun z => f z - g z) = (f - g) := rfl
    rw [hsub', deriv_sub (hf.differentiableAt (hU.mem_nhds hmem))
      (hg.differentiableAt (hU.mem_nhds hmem))]
  have h' := h z hz
  rwa [heq] at h'

/-- **`‖g'‖` does not drop by more than a factor `3/2` on a small disc** (continuity of `g'`). -/
theorem deriv_lower_half {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    {c : ℂ} (hc : c ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ U ∧
      ∀ z ∈ Metric.ball c r, ‖deriv g c‖ * 2 / 3 ≤ ‖deriv g z‖ := by
  rcases eq_or_ne (deriv g c) 0 with h0 | h0
  · obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
    exact ⟨r, hr, hrU, fun z _ => by
      rw [h0, norm_zero, zero_mul]
      simpa using norm_nonneg (deriv g z)⟩
  · have hpos : 0 < ‖deriv g c‖ := norm_pos_iff.mpr h0
    have hcont : ContinuousAt (deriv g) c :=
      AnalyticAt.continuousAt (AnalyticAt.deriv (hg.analyticAt (hU.mem_nhds hc)))
    have hev : ∀ᶠ z in 𝓝 c, ‖deriv g c - deriv g z‖ < ‖deriv g c‖ / 3 := by
      have h1 : ∀ᶠ z in 𝓝 c, deriv g z ∈ Metric.ball (deriv g c) (‖deriv g c‖ / 3) :=
        hcont.eventually (Metric.ball_mem_nhds _ (by positivity))
      filter_upwards [h1] with z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rwa [norm_sub_rev] at hz
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (inter_mem hev (hU.mem_nhds hc))
    refine ⟨r, hr, fun z hz => (hrU hz).2, fun z hz => ?_⟩
    have h1 : ‖deriv g c‖ ≤ ‖deriv g c - deriv g z‖ + ‖deriv g z‖ := by
      have h := norm_add_le (deriv g c - deriv g z) (deriv g z)
      rwa [sub_add_cancel] at h
    have h2 : ‖deriv g c - deriv g z‖ < ‖deriv g c‖ / 3 := (hrU hz).1
    have h3 : (2 : ℝ) / 3 * ‖deriv g c‖ ≤ ‖deriv g z‖ := by linarith [h1, h2]
    linarith [h3]

/-- **`‖g‖` grows at most by a factor `2` (plus `1`) on a small disc.** -/
theorem norm_upper_double {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    {c : ℂ} (hc : c ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ U ∧
      ∀ z ∈ Metric.ball c r, ‖g z‖ ≤ 2 * ‖g c‖ + 1 := by
  have hcont : ContinuousAt g c := hg.continuousOn.continuousAt (hU.mem_nhds hc)
  have hev : ∀ᶠ z in 𝓝 c, ‖g z‖ < 2 * ‖g c‖ + 1 := by
    have h1 : ∀ᶠ z in 𝓝 c, g z ∈ Metric.ball (g c) (‖g c‖ + 1) :=
      hcont.eventually (Metric.ball_mem_nhds _ (by positivity))
    filter_upwards [h1] with z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h2 : ‖g z - g c‖ < ‖g c‖ + 1 := hz
    have h3 : ‖g z‖ ≤ ‖g c‖ + ‖g z - g c‖ := by
      have h := norm_add_le (g c) (g z - g c)
      have he : g c + (g z - g c) = g z := by ring
      rwa [he] at h
    linarith
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (inter_mem hev (hU.mem_nhds hc))
  exact ⟨r, hr, fun z hz => (hrU hz).2, fun z hz => le_of_lt (hrU hz).1⟩

/-- The lower-bound fit condition `hfitlo` of `chain_returns_v8` from the threshold
`5/4 ≤ (C₀+1)·C₁²·cb²·η³` (equivalently `η³ ≥ (5/4)/((C₀+1)C₁²cb²)`, independent of `s`). -/
theorem fitlo_arith {η η₁ C₀ C₁ cb : ℝ} (hη : 0 < η) (hη₁ : 0 < η₁) (hC₀ : 0 < C₀ + 1)
    (hC₁ : 0 < C₁) (hcb : 0 < cb)
    (hkey : 5 / 4 ≤ (C₀ + 1) * C₁ ^ 2 * cb ^ 2 * η ^ 3) :
    4 * (η * η₁ ^ 2 / (320 * (C₀ + 1))) ≤ (C₁ * cb * η ^ 2 * η₁ / 10) ^ 2 := by
  have hη₁2 : 0 < η₁ ^ 2 := pow_pos hη₁ 2
  have hD : 0 < 320 * (C₀ + 1) := by linarith
  rw [show 4 * (η * η₁ ^ 2 / (320 * (C₀ + 1))) = η₁ ^ 2 * (4 * η / (320 * (C₀ + 1))) by ring]
  rw [show (C₁ * cb * η ^ 2 * η₁ / 10) ^ 2 = η₁ ^ 2 * ((C₁ * cb * η ^ 2 / 10) ^ 2) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hη₁2)
  rw [div_le_iff₀ hD]
  rw [show (C₁ * cb * η ^ 2 / 10) ^ 2 = C₁ ^ 2 * cb ^ 2 * η ^ 4 / 100 by ring]
  nlinarith [hkey, hη]

/-- The threshold bookkeeping for `hfitlo`: multiplying `Hfitlo ≤ η³` (with
`Hfitlo = (5/4)/((C₀+1)C₁²cb²)`) out gives `5/4 ≤ (C₀+1)C₁²cb²η³`. -/
theorem fitlo_key {Hfitlo η C₀ C₁ cb : ℝ} (hC₀ : 0 < C₀ + 1) (hC₁ : 0 < C₁) (hcb : 0 < cb)
    (hH : Hfitlo = (5 / 4) / ((C₀ + 1) * C₁ ^ 2 * cb ^ 2)) (hη : Hfitlo ≤ η ^ 3) :
    5 / 4 ≤ (C₀ + 1) * C₁ ^ 2 * cb ^ 2 * η ^ 3 := by
  have hD : 0 < (C₀ + 1) * C₁ ^ 2 * cb ^ 2 := by positivity
  have hmul : Hfitlo * ((C₀ + 1) * C₁ ^ 2 * cb ^ 2) ≤ η ^ 3 * ((C₀ + 1) * C₁ ^ 2 * cb ^ 2) :=
    mul_le_mul_of_nonneg_right hη (le_of_lt hD)
  rw [hH] at hmul
  rw [div_mul_cancel₀ (5 / 4) (ne_of_gt hD)] at hmul
  nlinarith [hmul]

end Work.Repel
