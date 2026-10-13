/-
Copyright: work module for the Elgindi finite-time singularity project.

# Vanishing of the "hard" slots at the endpoints of `Iθ`

A single `θ`-slot of the hard part of the `SpecialTransport` pairing has the shape

  `sin (2θ)^{-q} · f z θ · (v z θ)²`

with `f` of size `K·sin (2θ)` and `v` of size `C·sin (2θ)^p`.  Since

  `|sin (2θ)^{-q} · f · v²| ≤ K·C²·sin (2θ)^{1 + 2p - q}`

and `1 + 2p - q > 0` (because `p ≥ 0` and `1 + p - q > 0`), the slot vanishes at both
endpoints of `Iθ = [0, π/2]` — this is what makes the boundary terms of the angular
integration by parts disappear.

The two elementary facts used are collected in `STBasic`:
`sin (2θ)^s → 0` as `θ → 0⁺` (`tendsto_sin_rpow_zero_right`) and as `θ → (π/2)⁻`
(`tendsto_sin_rpow_zero_left`), both for `s > 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.STBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- For `s ≥ 0` the square of the `rpow` of `s` is the `rpow` of twice the exponent. -/
theorem sq_rpow_nat (s p : ℝ) (hs : 0 ≤ s) : (s ^ p) ^ 2 = s ^ (2 * p) := by
  have h : (s ^ p) ^ (2 : ℝ) = s ^ (2 * p) := by
    rw [← Real.rpow_mul hs p 2]
    congr 1
    ring
  simpa [Real.rpow_natCast] using h

/-- Pointwise bound for a hard slot on `Iθ`: `|sin(2θ)^{-q} f v²| ≤ K C² sin(2θ)^{1+2p-q}`.
The exponent `1 + 2p - q` is positive as soon as `q > 0`, `p ≥ 0` and `1 + p - q > 0`. -/
theorem hard_slot_abs_le {q K C p : ℝ} (hq0 : 0 < q) (hK : 0 ≤ K)
    {f v : ℝ → ℝ → ℝ} {z : ℝ}
    (hf1 : ∀ θ ∈ Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ))
    (hv1 : ∀ θ ∈ Spaces.Iθ, |v z θ| ≤ C * (Real.sin (2 * θ)) ^ p) :
    ∀ θ ∈ Spaces.Iθ,
      |(Real.sin (2 * θ)) ^ (-q) * f z θ * (v z θ) ^ 2| ≤
        K * C ^ 2 * (Real.sin (2 * θ)) ^ (1 + 2 * p - q) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rcases eq_or_lt_of_le hs0 with hs | hs
  · -- `sin (2θ) = 0`: the negative power kills the expression
    rw [← hs, Real.zero_rpow (x := -q) (by linarith)]
    simp only [zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg hK (sq_nonneg C)) (Real.rpow_nonneg le_rfl _)
  · have hsa : 0 ≤ (Real.sin (2 * θ)) ^ (-q) := Real.rpow_nonneg hs0 _
    have hv2 : (v z θ) ^ 2 ≤ (C * (Real.sin (2 * θ)) ^ p) ^ 2 := by
      rw [← sq_abs (v z θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hv1 θ hθ) 2
    have hbound : (Real.sin (2 * θ)) ^ (-q) * |f z θ| * (v z θ) ^ 2 ≤
        (Real.sin (2 * θ)) ^ (-q) * (K * Real.sin (2 * θ)) *
          (C * (Real.sin (2 * θ)) ^ p) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hf1 θ hθ) hsa) hv2 (sq_nonneg _)
        (mul_nonneg hsa (mul_nonneg hK hs0))
    calc |(Real.sin (2 * θ)) ^ (-q) * f z θ * (v z θ) ^ 2|
        = (Real.sin (2 * θ)) ^ (-q) * |f z θ| * (v z θ) ^ 2 := by
            rw [abs_mul, abs_mul, abs_of_nonneg hsa,
              abs_of_nonneg (sq_nonneg (v z θ))]
        _ ≤ (Real.sin (2 * θ)) ^ (-q) * (K * Real.sin (2 * θ)) *
              (C * (Real.sin (2 * θ)) ^ p) ^ 2 := hbound
        _ = K * C ^ 2 * (Real.sin (2 * θ)) ^ (1 + 2 * p - q) := by
            have hsq : (Real.sin (2 * θ) ^ p) ^ 2 = (Real.sin (2 * θ)) ^ (2 * p) :=
              sq_rpow_nat _ _ hs0
            have h1 : (Real.sin (2 * θ)) ^ (1 + 2 * p - q)
                = (Real.sin (2 * θ)) ^ (-q) * (Real.sin (2 * θ)) ^ (1 + 2 * p) := by
              rw [show (1 : ℝ) + 2 * p - q = -q + (1 + 2 * p) by ring]
              exact Real.rpow_add hs (-q) (1 + 2 * p)
            have h2 : (Real.sin (2 * θ)) ^ (1 + 2 * p)
                = Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (2 * p) := by
              rw [Real.rpow_add hs 1 (2 * p), Real.rpow_one]
            rw [mul_pow, hsq, h1, h2]
            ring

theorem HardSlotVan {q K C p : ℝ} (hq0 : 0 < q) (hp0 : 0 ≤ p) (hq4 : 0 < 1 + p - q)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    {f v : ℝ → ℝ → ℝ} {z : ℝ}
    (hf1 : ∀ θ ∈ Work.Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ))
    (hv1 : ∀ θ ∈ Work.Spaces.Iθ, |v z θ| ≤ C * (Real.sin (2 * θ)) ^ p) :
    Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (-q) * f z θ * (v z θ) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (-q) * f z θ * (v z θ) ^ 2)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have he : 0 < 1 + 2 * p - q := by linarith
  -- eventually `θ ∈ Iθ` at both endpoints
  have hneighR : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Spaces.Iθ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 4 by positivity)] with θ hθ
    exact ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hneighL : ∀ᶠ θ in 𝓝[<] (π / 2), θ ∈ Spaces.Iθ := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by positivity)] with θ hθ
    exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the dominating functions tend to zero at both endpoints
  have hlimR : Tendsto (fun θ => K * C ^ 2 * (Real.sin (2 * θ)) ^ (1 + 2 * p - q))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (tendsto_sin_rpow_zero_right (1 + 2 * p - q) he).const_mul (K * C ^ 2)
    simpa using h
  have hlimL : Tendsto (fun θ => K * C ^ 2 * (Real.sin (2 * θ)) ^ (1 + 2 * p - q))
      (𝓝[<] (π / 2)) (𝓝 0) := by
    have h := (tendsto_sin_rpow_zero_left (1 + 2 * p - q) he).const_mul (K * C ^ 2)
    simpa using h
  constructor
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have habs : Tendsto
        (fun θ => |(Real.sin (2 * θ)) ^ (-q) * f z θ * (v z θ) ^ 2|)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall (fun θ => abs_nonneg _)) ?_ hlimR
      filter_upwards [hneighR] with θ hθ
      exact hard_slot_abs_le hq0 hK hf1 hv1 θ hθ
    simpa [Real.norm_eq_abs] using habs
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have habs : Tendsto
        (fun θ => |(Real.sin (2 * θ)) ^ (-q) * f z θ * (v z θ) ^ 2|)
        (𝓝[<] (π / 2)) (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall (fun θ => abs_nonneg _)) ?_ hlimL
      filter_upwards [hneighL] with θ hθ
      exact hard_slot_abs_le hq0 hK hf1 hv1 θ hθ
    simpa [Real.norm_eq_abs] using habs

end Work.FTS.H2
