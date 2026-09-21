import Mathlib
import Submission.Work.OddRadon.intervalIntegrable_one_sub_sq_rpow
import Submission.Work.OddRadon.intervalIntegrable_deriv_comp

namespace Work.OddRadon

open MeasureTheory Filter
open scoped Topology Interval

/-- **An integration-by-parts identity for the Abel kernel.**

For `α > 0`, `G` of class `C¹` on `[0,1]` and `0 < c < 1`:
`(2α+1) ∫_0^1 G(ct) (1-t²)^α dt + c ∫_0^1 (deriv G)(ct) t (1-t²)^α dt = 2α ∫_0^1 G(ct) (1-t²)^(α-1) dt`.

Proof sketch (corrected): put `P t = G(ct) * t * (1-t²)^α`.  Then `P` is continuous on `[0,1]`,
`P 0 = 0 = P 1` (since `α > 0`), and for `t ∈ (0,1)`
`P' t = c (deriv G)(ct) t (1-t²)^α + G(ct) (1-t²)^α - 2α t² G(ct) (1-t²)^(α-1)`.
Write `D = ∫_0^1 (deriv G)(ct) t (1-t²)^α`, `A = ∫_0^1 G(ct)(1-t²)^α`,
`B = ∫_0^1 G(ct)(1-t²)^(α-1)`, `C = ∫_0^1 G(ct) t² (1-t²)^(α-1)`.
The singular term `t ↦ (1-t²)^(α-1)` is integrable on `[0,1]` (since `-1 < α-1`; compare with
`(1-t)^(α-1)` and use `intervalIntegral.intervalIntegrable_rpow'` together with
`intervalIntegral.IntervalIntegrable.comp_sub_left_iff`), so `P'` is interval-integrable and
`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` gives `∫_0^1 P' = P 1 - P 0 = 0`,
i.e. `c D + A = 2α C`.  Splitting `A = B - C` (pointwise `(1-t²)^α = (1-t²)^(α-1) * (1-t²)`,
which also holds at `t = 1` because `α > 0` and `0^(α-1) * 0 = 0`) gives `c D = 2α C - A`, and
then `(2α+1) A + c D = (2α+1) A + 2α C - A = 2α (A + C) = 2α B`, which is the claim.

`deriv G (ct)` is the honest derivative for `t ∈ (0,1]` because `ct ∈ (0,c]` lies in the interior
of `[0,1]`; at `t = 0` the factor `t` kills whatever `deriv G 0` is.-/
theorem integral_rpow_one_sub_sq_ibp {α : ℝ} (hα : 0 < α) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Icc 0 1)) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (2 * α + 1) * (∫ t in (0 : ℝ)..1, G (c * t) * (1 - t ^ 2) ^ α)
      + c * (∫ t in (0 : ℝ)..1, deriv G (c * t) * t * (1 - t ^ 2) ^ α)
      = 2 * α * (∫ t in (0 : ℝ)..1, G (c * t) * (1 - t ^ 2) ^ (α - 1)) := by
  -- abbreviations for the four integrals in the statement
  set A : ℝ := ∫ t in (0:ℝ)..1, G (c * t) * (1 - t ^ 2) ^ α with hA
  set D : ℝ := ∫ t in (0:ℝ)..1, deriv G (c * t) * t * (1 - t ^ 2) ^ α with hD
  set B : ℝ := ∫ t in (0:ℝ)..1, G (c * t) * (1 - t ^ 2) ^ (α - 1) with hB
  set Cv : ℝ := ∫ t in (0:ℝ)..1, G (c * t) * t ^ 2 * (1 - t ^ 2) ^ (α - 1) with hCv
  -- the two integrability inputs: the singular Abel kernel, and `deriv G (c * ·)`
  have hsing : IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) ^ (α - 1)) volume (0:ℝ) 1 :=
    intervalIntegrable_one_sub_sq_rpow (by linarith : (-1:ℝ) < α - 1)
  have hderivint : IntervalIntegrable (fun t : ℝ => deriv G (c * t)) volume (0:ℝ) 1 :=
    intervalIntegrable_deriv_comp hG hc hc1
  -- continuity of the various factors on `[0,1]`
  have hcr : ContinuousOn (fun t : ℝ => (1 - t ^ 2) ^ α) (Set.uIcc 0 1) :=
    ContinuousOn.rpow_const (by fun_prop) (fun t ht => Or.inr hα.le)
  have hcG : ContinuousOn (fun t : ℝ => G (c * t)) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact hG.continuousOn.comp (continuousOn_const.mul continuousOn_id)
      (fun t ht => ⟨by nlinarith [ht.1, hc], by nlinarith [ht.2, hc1]⟩)
  have hA_int : IntervalIntegrable (fun t : ℝ => G (c * t) * (1 - t ^ 2) ^ α) volume (0:ℝ) 1 :=
    (hcG.mul hcr).intervalIntegrable
  have hB_int :
      IntervalIntegrable (fun t : ℝ => G (c * t) * (1 - t ^ 2) ^ (α - 1)) volume (0:ℝ) 1 :=
    hsing.continuousOn_mul hcG
  have hCv_int :
      IntervalIntegrable (fun t : ℝ => G (c * t) * t ^ 2 * (1 - t ^ 2) ^ (α - 1))
        volume (0:ℝ) 1 :=
    hsing.continuousOn_mul (hcG.mul (by fun_prop))
  have hA_rpow_int : IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) ^ α) volume (0:ℝ) 1 :=
    hcr.intervalIntegrable
  have hcont_u : ContinuousOn (fun t : ℝ => t * (1 - t ^ 2) ^ α) (Set.uIcc 0 1) :=
    continuousOn_id.mul hcr
  -- the two derivatives in the integration-by-parts lemma
  have hUU' : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivAt (fun t : ℝ => t * (1 - t ^ 2) ^ α)
        ((1 - x^2)^α - 2*α*x^2*(1 - x^2)^(α-1)) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0:ℝ) 1 := by simpa using hx
    have hpos : 0 < 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
    have h1 : HasDerivAt (fun s : ℝ => (1 - s ^ 2) ^ α) (-(2*α*x*(1 - x^2)^(α-1))) x := by
      have h2 : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2*x)) x := by
        have h : HasDerivAt (fun s : ℝ => s ^ 2) (2*x) x := by
          simpa using (hasDerivAt_pow 2 x :
            HasDerivAt (fun s : ℝ => s ^ 2) ((2:ℕ) * x ^ (2-1)) x)
        exact h.const_sub 1
      have h3 := h2.rpow_const (Or.inl (ne_of_gt hpos) : (1 - x^2) ≠ 0 ∨ 1 ≤ α)
      convert h3 using 1
      ring
    have h5 := (hasDerivAt_id x).mul h1
    convert h5 using 1
    all_goals first
      | rfl
      | (simp only [id_eq, one_mul]; ring)
  have hVV' : ∀ x ∈ Set.Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivAt (fun t : ℝ => G (c * t)) (c * deriv G (c * x)) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0:ℝ) 1 := by simpa using hx
    have hct : c * x ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨by nlinarith [hx'.1, hc], by nlinarith [hx'.2, hc1]⟩
    have hmem : Set.Icc (0:ℝ) 1 ∈ 𝓝 (c * x) := Icc_mem_nhds hct.1 hct.2
    have hcd : ContDiffAt ℝ 1 G (c * x) := hG.contDiffAt hmem
    have hf : HasFDerivAt G (fderiv ℝ G (c * x)) (c * x) :=
      (hcd.hasStrictFDerivAt (by norm_num)).hasFDerivAt
    have hGd : HasDerivAt G (deriv G (c * x)) (c * x) := by simpa using hf.hasDerivAt
    have hinner : HasDerivAt (fun s : ℝ => c * s) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have hcomp := hGd.comp x hinner
    convert hcomp using 1
    all_goals first
      | rfl
      | ring
  have hu' : IntervalIntegrable (fun t : ℝ => (1 - t^2)^α - 2*α*t^2*(1-t^2)^(α-1))
      volume (0:ℝ) 1 :=
    hA_rpow_int.sub (hsing.continuousOn_mul (by fun_prop))
  have hv' : IntervalIntegrable (fun t : ℝ => c * deriv G (c * t)) volume (0:ℝ) 1 :=
    hderivint.const_mul c
  -- integration by parts
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0:ℝ)) (b := 1)
    (u := fun t : ℝ => t * (1 - t^2)^α) (v := fun t : ℝ => G (c*t))
    (u' := fun t : ℝ => (1 - t^2)^α - 2*α*t^2*(1-t^2)^(α-1))
    (v' := fun t : ℝ => c * deriv G (c*t))
    hcont_u hcG hUU' hVV' hu' hv'
  -- the left-hand side of the identity above is `c * D`
  have hLHS_eq : (∫ x in (0:ℝ)..1, x * (1 - x^2)^α * (c * deriv G (c*x))) = c * D := by
    rw [hD]
    rw [show (∫ x in (0:ℝ)..1, x * (1 - x^2)^α * (c * deriv G (c*x)))
        = ∫ x in (0:ℝ)..1, c * (deriv G (c*x) * x * (1 - x^2)^α) from
        intervalIntegral.integral_congr (fun x _ => by ring)]
    rw [intervalIntegral.integral_const_mul]
  -- and the right-hand side is `A - 2 α C`
  have hRHS_eq :
      (∫ x in (0:ℝ)..1, ((1 - x^2)^α - 2*α*x^2*(1 - x^2)^(α-1)) * G (c*x))
        = A - 2*α*Cv := by
    rw [hA, hCv]
    rw [show (∫ x in (0:ℝ)..1, ((1 - x^2)^α - 2*α*x^2*(1 - x^2)^(α-1)) * G (c*x))
        = ∫ x in (0:ℝ)..1,
            (G (c*x) * (1 - x^2)^α - 2*α * (G (c*x) * x^2 * (1 - x^2)^(α-1))) from
        intervalIntegral.integral_congr (fun x _ => by ring)]
    rw [intervalIntegral.integral_sub hA_int (hCv_int.const_mul (2*α))]
    rw [intervalIntegral.integral_const_mul]
  -- the key identity `c D = 2 α C - A`
  have key : c * D = 2 * α * Cv - A := by
    have h := hIBP
    rw [hLHS_eq, hRHS_eq] at h
    have h1 : (1:ℝ) * (1 - 1^2)^α * G (c*1) = 0 := by simp [Real.zero_rpow hα.ne']
    have h2 : (0:ℝ) * (1 - 0^2)^α * G (c*0) = 0 := by ring
    rw [h1, h2] at h
    linarith
  -- and `A = B - C`
  have key2 : A = B - Cv := by
    rw [hA, hB, hCv]
    rw [← intervalIntegral.integral_sub hB_int hCv_int]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have htI : t ∈ Set.Icc (0:ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at ht
    have hnonneg : 0 ≤ 1 - t^2 := by nlinarith [htI.1, htI.2]
    have hbase : (1 - t^2)^(α-1) * (1 - t^2) = (1 - t^2)^α := by
      rcases eq_or_lt_of_le hnonneg with h0 | h0
      · rw [← h0, mul_zero, Real.zero_rpow hα.ne']
      · have hr := Real.rpow_add h0 (α-1) (1:ℝ)
        rw [Real.rpow_one] at hr
        rw [← hr]
        exact congrArg (fun e : ℝ => (1 - t ^ 2) ^ e) (by ring : (α - 1) + 1 = α)
    calc G (c*t) * (1 - t^2)^α
        = G (c*t) * ((1 - t^2)^(α-1) * (1 - t^2)) := by rw [hbase]
      _ = G (c*t) * (1 - t^2)^(α-1) - G (c*t) * t^2 * (1 - t^2)^(α-1) := by ring
  calc (2 * α + 1) * A + c * D = 2 * α * A + (A + c * D) := by ring
    _ = 2 * α * A + (A + (2 * α * Cv - A)) := by rw [key]
    _ = 2 * α * (A + Cv) := by ring
    _ = 2 * α * B := by rw [key2]; ring

end Work.OddRadon
