import Mathlib
import Submission.Work.FatouL1.abelSegmentMean

/-!
# FATOU-L1: second-order Taylor remainder along a segment, and the Abel form

`Work.FatouL1.normOneSubMulDerivLe` is the "second order Taylor with the exponent `2`"
estimate used in the Fatou/far-cap bookkeeping: if a holomorphic `Φ` satisfies the Abel
relation `Φ (z + v) = Φ z + 1` and its second derivative is bounded by `S` along the whole
segment `z + [0,1]·v`, then

`‖1 - v * deriv Φ z‖ ≤ ‖v‖ ^ 2 * (S / 2)`.

The mathematical content is Taylor's formula with integral remainder:
writing `g t = Φ (z + t • v) - Φ z - t * (v * deriv Φ z)` one has `g 0 = 0`, `g' 0 = 0`,
`‖g'' t‖ ≤ ‖v‖² S`, hence `‖g 1‖ ≤ ∫₀¹ (1-t) ‖g'' t‖ dt ≤ ‖v‖² S / 2`, and
`g 1 = 1 - v * deriv Φ z` by the Abel relation.

The key point of the formalisation here is that the only geometric hypothesis is that the
*segment* stays in the open set `U` (no ball around it is needed): at every point of the
segment `Φ` is holomorphic, so both `Φ` and `deriv Φ` are differentiable there and
`iteratedDeriv 2 Φ = deriv (deriv Φ)` is continuous along the segment.  Everything is then
reduced to the fundamental theorem of calculus along the segment, exactly as in
`Submission.Work.FatouL1.abelSegmentMean`.
-/

namespace Work.FatouL1

open Set MeasureTheory

/-- **Second-order Taylor remainder along a segment.**

For `Φ` holomorphic on an open set `U` containing the segment `z + [0,1]·v`, with
`‖iteratedDeriv 2 Φ‖ ≤ S` on that segment,

`‖Φ (z + v) - Φ z - v * deriv Φ z‖ ≤ ‖v‖ ^ 2 * (S / 2)`.

This is the segment-hypothesis version of `Work.FatouL1.abelTaylorRemainder`. -/
theorem taylorRemainder_of_differentiableOn {Φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΦd : DifferentiableOn ℂ Φ U) {z v : ℂ} {S : ℝ}
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → z + t • v ∈ U)
    (h2 : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → ‖iteratedDeriv 2 Φ (z + t • v)‖ ≤ S) :
    ‖Φ (z + v) - Φ z - v * deriv Φ z‖ ≤ ‖v‖ ^ 2 * (S / 2) := by
  have hiter : iteratedDeriv 2 Φ = deriv (deriv Φ) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  -- membership facts along the segment (now directly in `U`)
  have hB : ∀ t ∈ Icc (0:ℝ) 1, z + t • v ∈ U := fun t ht => hseg t ht
  have hst : ∀ s t : ℝ, s ∈ Icc (0:ℝ) 1 → t ∈ Icc (0:ℝ) 1 → s * t ∈ Icc (0:ℝ) 1 := by
    intro s t hs ht
    exact ⟨mul_nonneg hs.1 ht.1, by nlinarith [hs.1, hs.2, ht.1, ht.2]⟩
  have hB2 : ∀ s t : ℝ, s ∈ Icc (0:ℝ) 1 → t ∈ Icc (0:ℝ) 1 → z + s • (t • v) ∈ U := by
    intro s t hs ht
    have h : z + s • (t • v) = z + (s * t) • v := by rw [smul_smul]
    rw [h]
    exact hB (s * t) (hst s t hs ht)
  -- differentiability where needed
  have hd1 : ∀ t ∈ Icc (0:ℝ) 1, DifferentiableAt ℂ Φ (z + t • v) := fun t ht =>
    hΦd.differentiableAt (hU.mem_nhds (hB t ht))
  have hdd : DifferentiableOn ℂ (deriv Φ) U := hΦd.deriv hU
  have hd2 : ∀ t ∈ Icc (0:ℝ) 1, DifferentiableAt ℂ (deriv Φ) (z + t • v) := fun t ht =>
    (hdd _ (hB t ht)).differentiableAt (hU.mem_nhds (hB t ht))
  -- continuity along the segment
  have hgamma : ContinuousOn (fun t : ℝ => z + t • v) (Icc (0:ℝ) 1) := by fun_prop
  have hmapγ : MapsTo (fun t : ℝ => z + t • v) (Icc (0:ℝ) 1) U := fun t ht => hB t ht
  have hcont1 : ContinuousOn (fun t : ℝ => deriv Φ (z + t • v)) (Icc (0:ℝ) 1) :=
    hdd.continuousOn.comp hgamma hmapγ
  have hiterf : (fun t : ℝ => iteratedDeriv 2 Φ (z + t • v))
      = (fun t : ℝ => deriv (deriv Φ) (z + t • v)) := by
    funext t
    rw [hiter]
  have hcont2 : ContinuousOn (fun t : ℝ => iteratedDeriv 2 Φ (z + t • v)) (Icc (0:ℝ) 1) := by
    rw [hiterf]
    exact (hdd.deriv hU).continuousOn.comp hgamma hmapγ
  -- fundamental theorem of calculus, first order
  have hE1 : v • (∫ t in (0:ℝ)..1, deriv Φ (z + t • v)) = Φ (z + v) - Φ z :=
    intervalIntegral.integral_unitInterval_deriv_eq_sub hcont1
      (fun t ht => (hd1 t ht).hasDerivAt)
  have hE2 : (∫ t in (0:ℝ)..1, deriv Φ z) = deriv Φ z := by
    simp [intervalIntegral.integral_const]
  have hInt1 : IntervalIntegrable (fun t : ℝ => deriv Φ (z + t • v)) MeasureTheory.volume
      (0:ℝ) 1 :=
    hcont1.intervalIntegrable_of_Icc (by norm_num)
  have hsub_eq : (∫ t in (0:ℝ)..1, (deriv Φ (z + t • v) - deriv Φ z))
      = (∫ t in (0:ℝ)..1, deriv Φ (z + t • v)) - deriv Φ z := by
    rw [intervalIntegral.integral_sub hInt1 intervalIntegrable_const, hE2]
  have hAeq : Φ (z + v) - Φ z - v * deriv Φ z
      = v * ∫ t in (0:ℝ)..1, (deriv Φ (z + t • v) - deriv Φ z) := by
    rw [← hE1, smul_eq_mul, ← mul_sub, ← hsub_eq]
  -- pointwise second order bound through a second FTC
  have hpt : ∀ t ∈ Icc (0:ℝ) 1, ‖deriv Φ (z + t • v) - deriv Φ z‖ ≤ S * ‖v‖ * t := by
    intro t ht
    have hmap_st : MapsTo (fun s : ℝ => s * t) (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) :=
      fun s hs => hst s t hs ht
    have hfun2 : (fun s : ℝ => iteratedDeriv 2 Φ (z + s • (t • v)))
        = ((fun u : ℝ => iteratedDeriv 2 Φ (z + u • v)) ∘ (fun s : ℝ => s * t)) := by
      funext s
      show iteratedDeriv 2 Φ (z + s • (t • v)) = iteratedDeriv 2 Φ (z + (s * t) • v)
      rw [smul_smul]
    have hcont2t : ContinuousOn (fun s : ℝ => iteratedDeriv 2 Φ (z + s • (t • v)))
        (Icc (0:ℝ) 1) := by
      rw [hfun2]
      exact hcont2.comp (by fun_prop : ContinuousOn (fun s : ℝ => s * t) (Icc (0:ℝ) 1)) hmap_st
    have hderiv2t : ∀ s ∈ Icc (0:ℝ) 1,
        HasDerivAt (deriv Φ) (iteratedDeriv 2 Φ (z + s • (t • v))) (z + s • (t • v)) := by
      intro s hs
      have hw : z + (s * t) • v = z + s • (t • v) := by rw [smul_smul]
      rw [← hw]
      have hd := (hd2 (s * t) (hst s t hs ht)).hasDerivAt
      simpa only [← hiter] using hd
    have hE2' : (t • v) • (∫ s in (0:ℝ)..1, iteratedDeriv 2 Φ (z + s • (t • v)))
        = deriv Φ (z + t • v) - deriv Φ z :=
      intervalIntegral.integral_unitInterval_deriv_eq_sub hcont2t hderiv2t
    have hbd : ‖∫ s in (0:ℝ)..1, iteratedDeriv 2 Φ (z + s • (t • v))‖ ≤ S := by
      have hpt2 : ∀ s ∈ Icc (0:ℝ) 1, ‖iteratedDeriv 2 Φ (z + s • (t • v))‖ ≤ S := by
        intro s hs
        have hw : z + (s * t) • v = z + s • (t • v) := by rw [smul_smul]
        rw [← hw]
        exact h2 (s * t) (hst s t hs ht)
      calc ‖∫ s in (0:ℝ)..1, iteratedDeriv 2 Φ (z + s • (t • v))‖
          ≤ ∫ s in (0:ℝ)..1, ‖iteratedDeriv 2 Φ (z + s • (t • v))‖ :=
            intervalIntegral.norm_integral_le_integral_norm (by norm_num)
        _ ≤ ∫ s in (0:ℝ)..1, S := by
            refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const hpt2
            exact hcont2t.norm.intervalIntegrable_of_Icc (by norm_num)
        _ = S := by simp [intervalIntegral.integral_const]
    calc ‖deriv Φ (z + t • v) - deriv Φ z‖
        = ‖t • v‖ * ‖∫ s in (0:ℝ)..1, iteratedDeriv 2 Φ (z + s • (t • v))‖ := by
            rw [← hE2', norm_smul]
      _ = t * ‖v‖ * ‖∫ s in (0:ℝ)..1, iteratedDeriv 2 Φ (z + s • (t • v))‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ t * ‖v‖ * S := mul_le_mul_of_nonneg_left hbd (mul_nonneg ht.1 (norm_nonneg v))
      _ = S * ‖v‖ * t := by ring
  -- final assembly
  have hIntN : IntervalIntegrable (fun t : ℝ => ‖deriv Φ (z + t • v) - deriv Φ z‖)
      MeasureTheory.volume (0:ℝ) 1 := by
    have hc : ContinuousOn (fun t : ℝ => deriv Φ (z + t • v) - deriv Φ z) (Icc (0:ℝ) 1) :=
      hcont1.sub continuousOn_const
    exact hc.norm.intervalIntegrable_of_Icc (by norm_num)
  have hIntM : IntervalIntegrable (fun t : ℝ => S * ‖v‖ * t) MeasureTheory.volume (0:ℝ) 1 := by
    have hc : ContinuousOn (fun t : ℝ => S * ‖v‖ * t) (Icc (0:ℝ) 1) := by fun_prop
    exact hc.intervalIntegrable_of_Icc (by norm_num)
  have hnormint :
      ‖∫ t in (0:ℝ)..1, (deriv Φ (z + t • v) - deriv Φ z)‖ ≤ S * ‖v‖ / 2 := by
    calc ‖∫ t in (0:ℝ)..1, (deriv Φ (z + t • v) - deriv Φ z)‖
        ≤ ∫ t in (0:ℝ)..1, ‖deriv Φ (z + t • v) - deriv Φ z‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ t in (0:ℝ)..1, S * ‖v‖ * t :=
          intervalIntegral.integral_mono_on (by norm_num) hIntN hIntM hpt
      _ = S * ‖v‖ / 2 := by
          rw [show (fun t : ℝ => S * ‖v‖ * t) = (fun t : ℝ => (S * ‖v‖) * t) from rfl,
            intervalIntegral.integral_const_mul, integral_id]
          ring
  calc ‖Φ (z + v) - Φ z - v * deriv Φ z‖
      = ‖v * ∫ t in (0:ℝ)..1, (deriv Φ (z + t • v) - deriv Φ z)‖ := by rw [hAeq]
    _ = ‖v‖ * ‖∫ t in (0:ℝ)..1, (deriv Φ (z + t • v) - deriv Φ z)‖ := by rw [norm_mul]
    _ ≤ ‖v‖ * (S * ‖v‖ / 2) := mul_le_mul_of_nonneg_left hnormint (norm_nonneg v)
    _ = ‖v‖ ^ 2 * (S / 2) := by ring

theorem normOneSubMulDerivLe {Φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΦd : DifferentiableOn ℂ Φ U) {z v : ℂ} {S : ℝ}
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → z + t • v ∈ U)
    (h2 : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → ‖iteratedDeriv 2 Φ (z + t • v)‖ ≤ S)
    (hAbel : Φ (z + v) = Φ z + 1) :
    ‖1 - v * deriv Φ z‖ ≤ ‖v‖ ^ 2 * (S / 2) := by
  have hkey : 1 - v * deriv Φ z = Φ (z + v) - Φ z - v * deriv Φ z := by
    rw [hAbel]; ring
  rw [hkey]
  exact taylorRemainder_of_differentiableOn hU hΦd hseg h2

end Work.FatouL1
