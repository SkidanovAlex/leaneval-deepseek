/-
Work module: `Work.FTS.EllipticEst.Honest.SliceBoundary`.

# The boundary terms of the `θ`-slice integration by parts vanish

For the two singular weights of `Work.FTS.EllipticEst.Honest.SliceIbpDefs`,

* `sig η θ = sin (2θ)^{-η}`,
* `rho η θ = cos (2θ) · sin (2θ)^{-η-1}`,

and a function `f` of the slice whose *values* satisfy both endpoint bounds
`|f θ| ≤ C θ` and `|f θ| ≤ C (π/2 - θ)` while its derivative is bounded,
`|f' θ| ≤ C`, we prove

`sig η · f · f' → 0` and `rho η · f² → 0` at `θ → 0⁺` and at `θ → π/2⁻` (`η < 1`).

## The mathematics

On `(0, π/4)` one has `sin (2θ) ≥ (4/π) θ` (`Real.mul_le_sin`), so with `η ≥ 0`

`sig η θ · |f θ| · |f' θ| ≤ ((4/π) θ)^{-η} · C θ · C = C² (4/π)^{-η} θ^{1-η}`,

and `θ^{1-η} → 0` because `1 - η > 0`; likewise

`|rho η θ| · f θ² ≤ ((4/π) θ)^{-η-1} · C² θ² = C² (4/π)^{-η-1} θ^{1-η}`,

using `|cos (2θ)| ≤ 1`.  Near `π/2` the same computation applies with `t := π/2 - θ` in place
of `θ`, because `sin (2θ) = sin (2t)` and the hypotheses give `|f θ| ≤ C t`.  All four limits
follow from `squeeze_zero_norm'`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.EllipticEst.Honest.SliceIbpDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false

/-! ## Two elementary lower bounds for `sin (2θ)` near the endpoints -/

/-- On `[0, π/4]`, `sin (2θ)` dominates `(4/π) θ`. -/
theorem sin_two_ge_four_div_pi_mul (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 4) :
    (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
  have h := Real.mul_le_sin (x := 2 * θ) (by linarith) (by linarith [Real.pi_pos])
  have e : (2 / Real.pi) * (2 * θ) = (4 / Real.pi) * θ := by ring
  rwa [e] at h

/-- On `[π/4, π/2)`, `sin (2θ)` dominates `(4/π) (π/2 - θ)`. -/
theorem sin_two_ge_four_div_pi_mul_sub (θ : ℝ) (h0 : Real.pi / 4 ≤ θ) (h1 : θ < Real.pi / 2) :
    (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
  have ht0 : 0 ≤ Real.pi / 2 - θ := by linarith [Real.pi_pos]
  have ht1 : Real.pi / 2 - θ ≤ Real.pi / 4 := by linarith
  have h := sin_two_ge_four_div_pi_mul (Real.pi / 2 - θ) ht0 ht1
  rwa [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub] at h

/-! ## The pointwise bounds

Both are stated for a general "distance" `t` (which will be `θ` at the left endpoint and
`π/2 - θ` at the right one); the only input is `(4/π) t ≤ sin (2θ)`. -/

/-- `|sig η θ · f θ · f' θ| ≤ C² (4/π)^{-η} t^{1-η}` whenever `(4/π) t ≤ sin (2θ)`,
`|f θ| ≤ C t` and `|f' θ| ≤ C`. -/
theorem abs_sig_mul_le (f : ℝ → ℝ) (η C : ℝ) {t θ : ℝ} (hη0 : 0 ≤ η) (hC : 0 ≤ C)
    (ht0 : 0 < t) (hsin : 0 < Real.sin (2 * θ))
    (hge : (4 / Real.pi) * t ≤ Real.sin (2 * θ)) (hf : |f θ| ≤ C * t)
    (hd : |deriv f θ| ≤ C) :
    |sig η θ * f θ * deriv f θ| ≤ C ^ 2 * (4 / Real.pi) ^ (-η) * t ^ (1 - η) := by
  have htpos : (0 : ℝ) < (4 / Real.pi) * t := by positivity
  have hσ : |sig η θ| ≤ ((4 / Real.pi) * t) ^ (-η) := by
    simp only [sig]
    rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hsin) _)]
    exact Real.rpow_le_rpow_of_nonpos htpos hge (by linarith)
  have hxnn : (0 : ℝ) ≤ ((4 / Real.pi) * t) ^ (-η) := Real.rpow_nonneg (le_of_lt htpos) _
  have hstep : |sig η θ| * |f θ| * |deriv f θ| ≤ ((4 / Real.pi) * t) ^ (-η) * (C * t) * C := by
    refine mul_le_mul (mul_le_mul hσ hf (abs_nonneg _) hxnn) hd (abs_nonneg _) ?_
    exact mul_nonneg hxnn (mul_nonneg hC (le_of_lt ht0))
  have hcomb : t ^ (-η) * t = t ^ (1 - η) := by
    have h1 : t ^ (-η) * t ^ (1 : ℝ) = t ^ (-η + 1) := (Real.rpow_add ht0 (-η) 1).symm
    rw [Real.rpow_one] at h1
    rw [h1]
    congr 1
    ring
  have hfin : ((4 / Real.pi) * t) ^ (-η) * (C * t) * C
      = C ^ 2 * (4 / Real.pi) ^ (-η) * t ^ (1 - η) := by
    rw [Real.mul_rpow (by positivity) (le_of_lt ht0)]
    calc (4 / Real.pi) ^ (-η) * t ^ (-η) * (C * t) * C
        = (4 / Real.pi) ^ (-η) * C ^ 2 * (t ^ (-η) * t) := by ring
      _ = (4 / Real.pi) ^ (-η) * C ^ 2 * t ^ (1 - η) := by rw [hcomb]
      _ = C ^ 2 * (4 / Real.pi) ^ (-η) * t ^ (1 - η) := by ring
  calc |sig η θ * f θ * deriv f θ| = |sig η θ| * |f θ| * |deriv f θ| := by rw [abs_mul, abs_mul]
    _ ≤ ((4 / Real.pi) * t) ^ (-η) * (C * t) * C := hstep
    _ = C ^ 2 * (4 / Real.pi) ^ (-η) * t ^ (1 - η) := hfin

/-- `|rho η θ · f θ²| ≤ C² (4/π)^{-η-1} t^{1-η}` whenever `(4/π) t ≤ sin (2θ)` and
`|f θ| ≤ C t`. -/
theorem abs_rho_mul_le (f : ℝ → ℝ) (η C : ℝ) {t θ : ℝ} (hη0 : 0 ≤ η) (_hC : 0 ≤ C)
    (ht0 : 0 < t) (hsin : 0 < Real.sin (2 * θ))
    (hge : (4 / Real.pi) * t ≤ Real.sin (2 * θ)) (hf : |f θ| ≤ C * t) :
    |rho η θ * f θ ^ 2| ≤ C ^ 2 * (4 / Real.pi) ^ (-η - 1) * t ^ (1 - η) := by
  have htpos : (0 : ℝ) < (4 / Real.pi) * t := by positivity
  have hpow : |rho η θ| ≤ ((4 / Real.pi) * t) ^ (-η - 1) := by
    simp only [rho]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hsin) _)]
    have h1 : Real.sin (2 * θ) ^ (-η - 1) ≤ ((4 / Real.pi) * t) ^ (-η - 1) :=
      Real.rpow_le_rpow_of_nonpos htpos hge (by linarith)
    have h2 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h3 : 0 ≤ Real.sin (2 * θ) ^ (-η - 1) := Real.rpow_nonneg (le_of_lt hsin) _
    calc |Real.cos (2 * θ)| * Real.sin (2 * θ) ^ (-η - 1)
        ≤ 1 * Real.sin (2 * θ) ^ (-η - 1) := mul_le_mul_of_nonneg_right h2 h3
      _ = Real.sin (2 * θ) ^ (-η - 1) := one_mul _
      _ ≤ ((4 / Real.pi) * t) ^ (-η - 1) := h1
  have hxnn : (0 : ℝ) ≤ ((4 / Real.pi) * t) ^ (-η - 1) := Real.rpow_nonneg (le_of_lt htpos) _
  have hf2 : |f θ| ^ 2 ≤ (C * t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hf 2
  have hstep : |rho η θ| * |f θ| ^ 2 ≤ ((4 / Real.pi) * t) ^ (-η - 1) * (C * t) ^ 2 :=
    mul_le_mul hpow hf2 (by positivity) hxnn
  have hcomb : t ^ (-η - 1) * t ^ 2 = t ^ (1 - η) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht0]
    congr 1
    ring
  have hfin : ((4 / Real.pi) * t) ^ (-η - 1) * (C * t) ^ 2
      = C ^ 2 * (4 / Real.pi) ^ (-η - 1) * t ^ (1 - η) := by
    rw [Real.mul_rpow (by positivity) (le_of_lt ht0), mul_pow]
    calc (4 / Real.pi) ^ (-η - 1) * t ^ (-η - 1) * (C ^ 2 * t ^ 2)
        = (4 / Real.pi) ^ (-η - 1) * C ^ 2 * (t ^ (-η - 1) * t ^ 2) := by ring
      _ = (4 / Real.pi) ^ (-η - 1) * C ^ 2 * t ^ (1 - η) := by rw [hcomb]
      _ = C ^ 2 * (4 / Real.pi) ^ (-η - 1) * t ^ (1 - η) := by ring
  calc |rho η θ * f θ ^ 2| = |rho η θ| * |f θ| ^ 2 := by rw [abs_mul, abs_pow]
    _ ≤ ((4 / Real.pi) * t) ^ (-η - 1) * (C * t) ^ 2 := hstep
    _ = C ^ 2 * (4 / Real.pi) ^ (-η - 1) * t ^ (1 - η) := hfin

/-! ## The limit facts for the powers `θ^{1-η}` -/

/-- `θ^{1-η} → 0` as `θ → 0⁺` for `η < 1`. -/
theorem tendsto_rpow_one_sub_nhdsGT_zero {η : ℝ} (hη1 : η < 1) :
    Filter.Tendsto (fun θ : ℝ => θ ^ (1 - η)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine (((tendsto_rpow_neg_atTop (y := 1 - η) (by linarith)).comp
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x _
  rw [Function.comp_apply, Real.rpow_neg_eq_inv_rpow, inv_inv]

/-- `θ ↦ π/2 - θ` maps the left neighbourhood of `π/2` to the right neighbourhood of `0`. -/
theorem tendsto_sub_pi_div_two_nhdsLT :
    Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝[<] (Real.pi / 2)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h1 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 (Real.pi / 2))
        (𝓝 (Real.pi / 2 - Real.pi / 2)) := tendsto_const_nhds.sub tendsto_id
    simpa using h1.mono_left nhdsWithin_le_nhds
  · refine mem_of_superset self_mem_nhdsWithin ?_
    intro θ hθ
    show (0 : ℝ) < Real.pi / 2 - θ
    linarith [Real.pi_pos, Set.mem_Iio.mp hθ]

/-- `(π/2 - θ)^{1-η} → 0` as `θ → π/2⁻` for `η < 1`. -/
theorem tendsto_rpow_one_sub_nhdsLT_pi_div_two {η : ℝ} (hη1 : η < 1) :
    Filter.Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (1 - η))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
  (tendsto_rpow_one_sub_nhdsGT_zero hη1).comp tendsto_sub_pi_div_two_nhdsLT

/-! ## The four limits -/

theorem tendsto_sig_mul_deriv_nhdsGT_zero (f : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hC : 0 ≤ C) (hb1 : ∀ θ ∈ Iθo, |f θ| ≤ C * θ) (hb3 : ∀ θ ∈ Iθo, |deriv f θ| ≤ C) :
    Filter.Tendsto (fun θ => sig η θ * f θ * deriv f θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsGT_zero (η := η) hη1
  have hA : Filter.Tendsto (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η) * θ ^ (1 - η))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η))
  refine squeeze_zero_norm' ?_ hA
  have hsmall : Set.Iio (Real.pi / 4) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4))
  filter_upwards [self_mem_nhdsWithin, hsmall] with θ hθ0 hθ1
  have h0 : (0 : ℝ) < θ := Set.mem_Ioi.mp hθ0
  have h1 : θ ≤ Real.pi / 4 := le_of_lt (Set.mem_Iio.mp hθ1)
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨h0, by linarith [Real.pi_pos, h1]⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, h1])
  rw [Real.norm_eq_abs]
  exact abs_sig_mul_le f η C hη0 hC h0 hsin (sin_two_ge_four_div_pi_mul θ (le_of_lt h0) h1)
    (hb1 θ hθI) (hb3 θ hθI)

theorem tendsto_sig_mul_deriv_nhdsLT_pi_div_two (f : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hC : 0 ≤ C) (hb2 : ∀ θ ∈ Iθo, |f θ| ≤ C * (Real.pi / 2 - θ))
    (hb3 : ∀ θ ∈ Iθo, |deriv f θ| ≤ C) :
    Filter.Tendsto (fun θ => sig η θ * f θ * deriv f θ)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsLT_pi_div_two (η := η) hη1
  have hA : Filter.Tendsto
      (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η) * (Real.pi / 2 - θ) ^ (1 - η))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η))
  refine squeeze_zero_norm' ?_ hA
  have hbig : Set.Ioi (Real.pi / 4) ∈ 𝓝[<] (Real.pi / 2) :=
    mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2))
  filter_upwards [self_mem_nhdsWithin, hbig] with θ hθ1 hθ0
  have h1 : θ < Real.pi / 2 := Set.mem_Iio.mp hθ1
  have h0 : Real.pi / 4 ≤ θ := le_of_lt (Set.mem_Ioi.mp hθ0)
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨by linarith [Real.pi_pos, h0], h1⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, h0]) (by linarith [Real.pi_pos, h1])
  have ht0 : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos, h1]
  rw [Real.norm_eq_abs]
  exact abs_sig_mul_le f η C hη0 hC ht0 hsin (sin_two_ge_four_div_pi_mul_sub θ h0 h1)
    (hb2 θ hθI) (hb3 θ hθI)

theorem tendsto_rho_mul_sq_nhdsGT_zero (f : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hC : 0 ≤ C) (hb1 : ∀ θ ∈ Iθo, |f θ| ≤ C * θ) :
    Filter.Tendsto (fun θ => rho η θ * f θ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsGT_zero (η := η) hη1
  have hA : Filter.Tendsto (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η - 1) * θ ^ (1 - η))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η - 1))
  refine squeeze_zero_norm' ?_ hA
  have hsmall : Set.Iio (Real.pi / 4) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4))
  filter_upwards [self_mem_nhdsWithin, hsmall] with θ hθ0 hθ1
  have h0 : (0 : ℝ) < θ := Set.mem_Ioi.mp hθ0
  have h1 : θ ≤ Real.pi / 4 := le_of_lt (Set.mem_Iio.mp hθ1)
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨h0, by linarith [Real.pi_pos, h1]⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, h1])
  rw [Real.norm_eq_abs]
  exact abs_rho_mul_le f η C hη0 hC h0 hsin (sin_two_ge_four_div_pi_mul θ (le_of_lt h0) h1)
    (hb1 θ hθI)

theorem tendsto_rho_mul_sq_nhdsLT_pi_div_two (f : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η)
    (hη1 : η < 1) (hC : 0 ≤ C) (hb2 : ∀ θ ∈ Iθo, |f θ| ≤ C * (Real.pi / 2 - θ)) :
    Filter.Tendsto (fun θ => rho η θ * f θ ^ 2) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hpow := tendsto_rpow_one_sub_nhdsLT_pi_div_two (η := η) hη1
  have hA : Filter.Tendsto
      (fun θ : ℝ => C ^ 2 * (4 / Real.pi) ^ (-η - 1) * (Real.pi / 2 - θ) ^ (1 - η))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa using hpow.const_mul (C ^ 2 * (4 / Real.pi) ^ (-η - 1))
  refine squeeze_zero_norm' ?_ hA
  have hbig : Set.Ioi (Real.pi / 4) ∈ 𝓝[<] (Real.pi / 2) :=
    mem_nhdsWithin_of_mem_nhds
      (Ioi_mem_nhds (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2))
  filter_upwards [self_mem_nhdsWithin, hbig] with θ hθ1 hθ0
  have h1 : θ < Real.pi / 2 := Set.mem_Iio.mp hθ1
  have h0 : Real.pi / 4 ≤ θ := le_of_lt (Set.mem_Ioi.mp hθ0)
  have hθI : θ ∈ Iθo := Set.mem_Ioo.mpr ⟨by linarith [Real.pi_pos, h0], h1⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, h0]) (by linarith [Real.pi_pos, h1])
  have ht0 : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos, h1]
  rw [Real.norm_eq_abs]
  exact abs_rho_mul_le f η C hη0 hC ht0 hsin (sin_two_ge_four_div_pi_mul_sub θ h0 h1)
    (hb2 θ hθI)

theorem SliceBoundary (f : ℝ → ℝ) (η C : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (hC : 0 ≤ C)
    (hb1 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |f θ| ≤ C * θ)
    (hb2 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |f θ| ≤ C * (Real.pi / 2 - θ))
    (hb3 : ∀ θ ∈ Work.FTS.EllipticEst.Honest.Iθo, |deriv f θ| ≤ C) :
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.Honest.sig η θ * f θ * deriv f θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.Honest.sig η θ * f θ * deriv f θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.Honest.rho η θ * f θ ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun θ => Work.FTS.EllipticEst.Honest.rho η θ * f θ ^ 2) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
  ⟨tendsto_sig_mul_deriv_nhdsGT_zero f η C hη0 hη1 hC hb1 hb3,
   tendsto_sig_mul_deriv_nhdsLT_pi_div_two f η C hη0 hη1 hC hb2 hb3,
   tendsto_rho_mul_sq_nhdsGT_zero f η C hη0 hη1 hC hb1,
   tendsto_rho_mul_sq_nhdsLT_pi_div_two f η C hη0 hη1 hC hb2⟩

end Work.FTS.EllipticEst.Honest
