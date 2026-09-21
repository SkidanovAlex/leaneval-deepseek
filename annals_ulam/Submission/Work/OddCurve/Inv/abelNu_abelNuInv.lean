import Mathlib
import Submission.Work.OddCurve.Inv.Defs
import Submission.Commons.Analysis.Abel.continuousOn_abel_K
import Submission.Work.Analysis.Abel.intervalIntegrable_invSqrt_mul_invSqrt_sub

/-!
# `abelNu` is inverted by `abelNuInv`

The composition of the two unnormalized fractional integrals of order `1/2` is `π` times the
ordinary integral (`Commons.Analysis.Abel.abel_self_convolution`), and the kernel
`(√(ν-τ))⁻¹(√τ)⁻¹` integrates to `π` (`Commons.Analysis.Abel.integral_invSqrt_mul_invSqrt_sub`).
Hence `abelNu ∘ abelNuInv = id` on `C¹` profiles: the second term of `abelNuInv` supplies the
constant `G 0` which `J^{1/2}` of a continuous function cannot see.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace Work.OddCurve.Inv

/-- **Elliptic substitution for the Abel transform.**  For `τ ≥ 0` the right-edge Abel transform
is the (smooth-parameter) integral `2√τ ∫_0^1 f (τ (1-u²)) du`; the substitution removes the
`(√(τ-σ))⁻¹` singularity at the right endpoint.  This is the mirror of
`Commons.Analysis.Abel.intervalIntegral_abel_subst` and is what makes the continuity of
`abelNu` in the upper limit transparent. -/
lemma abelNu_eq_sqrt_mul_integral_aux (f : ℝ → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    abelNu f τ = 2 * Real.sqrt τ * ∫ u in (0:ℝ)..1, f (τ * (1 - u ^ 2)) := by
  have h1 : abelNu f τ = ∫ s in (0:ℝ)..τ, (Real.sqrt s)⁻¹ * f (τ - s) := by
    rw [abelNu]
    have hcomp := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := τ)
      (f := fun s => (Real.sqrt s)⁻¹ * f (τ - s)) (d := τ)
    simp only [sub_self, sub_zero] at hcomp
    calc ∫ x in (0:ℝ)..τ, (Real.sqrt (τ - x))⁻¹ * f x
        = ∫ x in (0:ℝ)..τ, (Real.sqrt (τ - x))⁻¹ * f (τ - (τ - x)) := by
          apply intervalIntegral.integral_congr
          intro x _
          show (Real.sqrt (τ - x))⁻¹ * f x = (Real.sqrt (τ - x))⁻¹ * f (τ - (τ - x))
          rw [show τ - (τ - x) = x from by ring]
      _ = ∫ x in (0:ℝ)..τ, (Real.sqrt x)⁻¹ * f (τ - x) := hcomp
  have h2 : (∫ s in (0:ℝ)..τ, (Real.sqrt s)⁻¹ * f (τ - s))
      = 2 * Real.sqrt τ * ∫ u in (0:ℝ)..1, f (τ * (1 - u ^ 2)) := by
    have h := Commons.Analysis.Abel.intervalIntegral_abel_subst (E := ℝ) (x := (0:ℝ)) (b := τ)
      hτ (fun _ s => f (τ - s))
    simp only [sub_zero, zero_add, smul_eq_mul] at h
    rw [h]
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [show τ - τ * u ^ 2 = τ * (1 - u ^ 2) from by ring]
  rw [h1, h2]

/-- Continuity of the Abel transform `abelNu g` in its upper limit, for `g` continuous on `[0,1]`
and `0 < ν ≤ 1`.  On `[0,ν]` the transformed form of `abelNu_eq_sqrt_mul_integral_aux` has a
jointly continuous integrand. -/
lemma abelNu_continuousOn_aux {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 1)) {ν : ℝ}
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    ContinuousOn (fun τ => abelNu g τ) (Set.Icc 0 ν) := by
  have hF : ContinuousOn (fun p : ℝ × ℝ => g (p.1 * (1 - p.2 ^ 2)))
      (Set.Icc 0 ν ×ˢ Set.uIcc 0 1) := by
    have hpath : ContinuousOn (fun p : ℝ × ℝ => p.1 * (1 - p.2 ^ 2))
        (Set.Icc 0 ν ×ˢ Set.uIcc 0 1) := by fun_prop
    have hmap : Set.MapsTo (fun p : ℝ × ℝ => p.1 * (1 - p.2 ^ 2))
        (Set.Icc 0 ν ×ˢ Set.uIcc 0 1) (Set.Icc 0 ν) := by
      intro p hp
      have hp1 : p.1 ∈ Set.Icc (0:ℝ) ν := hp.1
      have hp2 : p.2 ∈ Set.uIcc (0:ℝ) 1 := hp.2
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hp2
      have hle1 : 1 - p.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg p.2]
      have hge0 : 0 ≤ 1 - p.2 ^ 2 := by nlinarith [hp2.1, hp2.2, sq_nonneg p.2]
      exact ⟨by nlinarith [hp1.1, hge0], by nlinarith [hp1.2, hle1, hge0, hp1.1]⟩
    exact (hg.mono (Set.Icc_subset_Icc_right hν1)).comp' hpath hmap
  have hint : ContinuousOn (fun τ : ℝ => ∫ u in (0:ℝ)..1, g (τ * (1 - u ^ 2)))
      (Set.Icc 0 ν) :=
    Commons.Analysis.Abel.continuousOn_intervalIntegral_of_continuousOn_compact (s := Set.Icc 0 ν)
      isCompact_Icc (A := (0:ℝ)) (B := 1) (by norm_num) hF
  have hprod : ContinuousOn
      (fun τ : ℝ => 2 * Real.sqrt τ * ∫ u in (0:ℝ)..1, g (τ * (1 - u ^ 2)))
      (Set.Icc 0 ν) := by
    have hs : ContinuousOn (fun τ : ℝ => 2 * Real.sqrt τ) (Set.Icc 0 ν) := by fun_prop
    exact hs.mul hint
  exact hprod.congr (fun τ hτ => abelNu_eq_sqrt_mul_integral_aux g hτ.1)

/-- The Abel kernel against a continuous profile is interval integrable. -/
lemma intervalIntegrable_invSqrt_mul_abelNu_aux {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 1))
    {ν : ℝ} (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    IntervalIntegrable (fun τ => (Real.sqrt (ν - τ))⁻¹ * abelNu g τ) volume 0 ν := by
  have hcont : ContinuousOn (fun τ => abelNu g τ) (Set.uIcc 0 ν) := by
    rw [Set.uIcc_of_le hν0.le]
    exact abelNu_continuousOn_aux hg hν0 hν1
  exact (Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub_right hν0).mul_continuousOn hcont

theorem abelNu_abelNuInv {G : ℝ → ℝ} (hG : ContDiffOn ℝ 1 G (Set.Icc 0 1)) (hG' : ContinuousOn (deriv G) (Set.Icc 0 1)) : ∀ ν ∈ Set.Ioo (0 : ℝ) 1, Work.OddCurve.Inv.abelNu (Work.OddCurve.Inv.abelNuInv G) ν = G ν := by
  intro ν hν
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := le_of_lt hν.2
  have hI1 : IntervalIntegrable (fun τ => (Real.sqrt (ν - τ))⁻¹ * abelNu (deriv G) τ) volume 0 ν :=
    intervalIntegrable_invSqrt_mul_abelNu_aux hG' hν0 hν1
  have hI2 : IntervalIntegrable (fun τ => (Real.sqrt (ν - τ))⁻¹ * (Real.sqrt τ)⁻¹) volume 0 ν := by
    have h := Commons.Analysis.Abel.intervalIntegrable_invSqrt_mul_invSqrt_sub (t := 0) (x := ν) hν0
    simpa only [sub_zero, mul_comm] using h
  have h1 : IntervalIntegrable
      (fun τ => (Real.sqrt (ν - τ))⁻¹ * ((1 / Real.pi) * abelNu (deriv G) τ)) volume 0 ν := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hI1.const_mul (1 / Real.pi)
  have h2 : IntervalIntegrable
      (fun τ => (Real.sqrt (ν - τ))⁻¹ * ((G 0 / Real.pi) * (Real.sqrt τ)⁻¹)) volume 0 ν := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hI2.const_mul (G 0 / Real.pi)
  have e1 : (∫ τ in (0:ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * ((1 / Real.pi) * abelNu (deriv G) τ))
      = (1 / Real.pi) * (∫ τ in (0:ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * abelNu (deriv G) τ) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      intervalIntegral.integral_const_mul (1 / Real.pi)
        (fun τ => (Real.sqrt (ν - τ))⁻¹ * abelNu (deriv G) τ)
  have e2 : (∫ τ in (0:ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * ((G 0 / Real.pi) * (Real.sqrt τ)⁻¹))
      = (G 0 / Real.pi) * (∫ τ in (0:ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * (Real.sqrt τ)⁻¹) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      intervalIntegral.integral_const_mul (G 0 / Real.pi)
        (fun τ => (Real.sqrt (ν - τ))⁻¹ * (Real.sqrt τ)⁻¹)
  have hsplit : (∫ τ in (0:ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * abelNuInv G τ)
      = (1 / Real.pi) * (∫ τ in (0:ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * abelNu (deriv G) τ)
        + (G 0 / Real.pi) * (∫ τ in (0:ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * (Real.sqrt τ)⁻¹) := by
    have hadd : (∫ τ in (0:ℝ)..ν, ((Real.sqrt (ν - τ))⁻¹ * ((1 / Real.pi) * abelNu (deriv G) τ)
          + (Real.sqrt (ν - τ))⁻¹ * ((G 0 / Real.pi) * (Real.sqrt τ)⁻¹)))
        = (1 / Real.pi) * (∫ τ in (0:ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * abelNu (deriv G) τ)
          + (G 0 / Real.pi) * (∫ τ in (0:ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * (Real.sqrt τ)⁻¹) := by
      rw [intervalIntegral.integral_add h1 h2, e1, e2]
    rw [← hadd]
    apply intervalIntegral.integral_congr
    intro τ _
    show (Real.sqrt (ν - τ))⁻¹ * abelNuInv G τ
      = (Real.sqrt (ν - τ))⁻¹ * ((1 / Real.pi) * abelNu (deriv G) τ)
        + (Real.sqrt (ν - τ))⁻¹ * ((G 0 / Real.pi) * (Real.sqrt τ)⁻¹)
    rw [abelNuInv]
    ring
  have hA : (∫ τ in (0:ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * abelNu (deriv G) τ)
      = Real.pi * ∫ t in (0:ℝ)..ν, deriv G t := by
    have hself := Commons.Analysis.Abel.abel_self_convolution (g := deriv G) hG' hν0 hν1
    simpa only [abelNu] using hself
  have hB : (∫ τ in (0:ℝ)..ν, (Real.sqrt (ν - τ))⁻¹ * (Real.sqrt τ)⁻¹) = Real.pi := by
    have h := Commons.Analysis.Abel.integral_invSqrt_mul_invSqrt_sub (a := (0:ℝ)) (b := ν) hν0
    simpa only [sub_zero] using h
  have hftc : (∫ t in (0:ℝ)..ν, deriv G t) = G ν - G 0 :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc (f := G) (a := (0:ℝ)) (b := ν)
      (hG.mono (Set.Icc_subset_Icc_right hν1)) hν0.le
  rw [abelNu, hsplit, hA, hB, hftc]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end Work.OddCurve.Inv
