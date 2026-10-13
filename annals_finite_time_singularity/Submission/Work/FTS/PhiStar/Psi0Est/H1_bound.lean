import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.FTS.PhiStar.Psi0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open scoped Real
open MeasureTheory Set

set_option autoImplicit false

/-!
# The `H¹`-endpoint bound for `Ψ_Γ(θ) = ∫_θ^{π/2} sin t cos²t Γ(t) dt`

For `0 < α ≤ 1/4` and `π/4 < θ < π/2` we prove

`|3 Ψ_Γ(θ)/cos³θ − Γ(θ)| ≤ 3α cos^{2α/3}θ`,   `Γ(θ) = (sin θ cos²θ)^{α/3}`.

## The mathematics

Write `u(θ) = sin θ cos²θ` (so `Γ = u^{α/3}`) and let `A = ∫_θ^{π/2} u Γ`,
`Q = ∫_θ^{π/2} u (Γ(t) − Γ(θ))`.  The elementary integral `∫_θ^{π/2} u = cos³θ/3`
turns the desired difference into a *pure* integral of `u (Γ − Γ(t))`:

`3 A / cos³θ − Γ(θ) = 3 Q / cos³θ`.

Since `u` is strictly decreasing on `[π/4, π/2]` (because `u = f(sin θ)` with
`f(s) = s − s³` and `sin θ ∈ [√2/2, 1] ⊂ [1/√3, 1]`), one has `Γ(t) ≤ Γ(θ)` on
`[θ, π/2]`, hence `Q ≤ 0`.  In the other direction, Bernoulli's inequality
`(1 + x)^p ≤ 1 + p x` (`0 ≤ p ≤ 1`, `x ≥ −1`) applied with `1 + x = u(θ)/u(t)`,
`p = α/3` gives the pointwise bound

`u(t) (Γ(θ) − Γ(t)) ≤ u(t) p u(t)^{p−1} (u(θ) − u(t)) ≤ (α/3) Γ(θ) u(θ)`,

and integrating over `t ∈ [θ, π/2]` yields

`−Q ≤ (α/3) Γ(θ) u(θ) (π/2 − θ) ≤ (π/2) α Γ(θ) cos³θ`.

Together with `Γ(θ) = sin^{α/3}θ cos^{2α/3}θ ≤ cos^{2α/3}θ` and `π/2 ≤ 3` this gives
the claim.
-/

/-! ## The angular profile `u(θ) = sin θ cos²θ` is decreasing on `[π/4, π/2]` -/

/-- `u(θ) = sin θ cos²θ` is antitone on `[π/4, π/2]`. -/
lemma sin_mul_cos_sq_anti {θ t : ℝ} (hθ : Real.pi / 4 ≤ θ) (hθt : θ ≤ t)
    (ht : t ≤ Real.pi / 2) :
    Real.sin t * Real.cos t ^ 2 ≤ Real.sin θ * Real.cos θ ^ 2 := by
  have h1 : Real.sin θ ≤ Real.sin t :=
    Real.monotoneOn_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
      ⟨by linarith [Real.pi_pos], ht⟩ hθt
  have hy : Real.sqrt 2 / 2 ≤ Real.sin θ := by
    have h := Real.monotoneOn_sin
      (show Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      (show θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) hθ
    rwa [Real.sin_pi_div_four] at h
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : (1 : ℝ) / 2 ≤ Real.sin θ ^ 2 := by nlinarith [hy, hsq, Real.sqrt_nonneg 2]
  have hsy : (1 : ℝ) / 2 ≤ Real.sin θ * Real.sin t := by
    nlinarith [hs2, h1, Real.sqrt_nonneg 2]
  have hxy : 0 ≤ Real.sin t - Real.sin θ := by linarith
  have hprod : (Real.sin t - Real.sin θ) *
      (1 - (Real.sin t ^ 2 + Real.sin t * Real.sin θ + Real.sin θ ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hxy
      (by nlinarith [hs2, hsy, sq_nonneg (Real.sin t), h1])
  rw [Real.cos_sq' t, Real.cos_sq' θ]
  nlinarith [hprod]

/-- `Γ` is antitone on `[π/4, π/2]`. -/
lemma Gam_anti {α θ t : ℝ} (hα : 0 < α) (hθ : Real.pi / 4 ≤ θ) (hθt : θ ≤ t)
    (ht : t ≤ Real.pi / 2) :
    Work.Spaces.Gam α t ≤ Work.Spaces.Gam α θ := by
  have hs0 : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [Work.Spaces.Gam, Work.Spaces.Gam]
  exact Real.rpow_le_rpow (mul_nonneg hs0 (sq_nonneg _)) (sin_mul_cos_sq_anti hθ hθt ht)
    (by linarith)

/-- `Γ(θ) = sin^{α/3}θ cos^{2α/3}θ ≤ cos^{2α/3}θ`. -/
lemma Gam_le_cos_rpow {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.Gam α θ ≤ Real.cos θ ^ (2 * α / 3) := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], le_of_lt hθ.2⟩
  have h1 : Work.Spaces.Gam α θ =
      Real.sin θ ^ (α / 3) * (Real.cos θ ^ 2) ^ (α / 3) := by
    change (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) = _
    rw [Real.mul_rpow hs0 (by positivity)]
  have h2 : (Real.cos θ ^ 2) ^ (α / 3) = Real.cos θ ^ (2 * (α / 3)) := by
    rw [← Real.rpow_natCast (Real.cos θ) 2]
    exact (Real.rpow_mul hc0 (2 : ℝ) (α / 3)).symm
  have h3 : Real.sin θ ^ (α / 3) ≤ 1 :=
    Real.rpow_le_one hs0 (Real.sin_le_one θ) (by linarith)
  have h4 : (0 : ℝ) ≤ Real.cos θ ^ (2 * (α / 3)) := Real.rpow_nonneg hc0 _
  rw [h1, h2]
  calc Real.sin θ ^ (α / 3) * Real.cos θ ^ (2 * (α / 3))
      ≤ 1 * Real.cos θ ^ (2 * (α / 3)) := mul_le_mul_of_nonneg_right h3 h4
    _ = Real.cos θ ^ (2 * α / 3) := by
        rw [one_mul]
        congr 1
        ring

/-! ## The pointwise convexity (Bernoulli) bound -/

/-- **Key pointwise bound.**  For `π/4 ≤ θ ≤ t ≤ π/2`,

`u(t) (Γ(θ) − Γ(t)) ≤ (α/3) Γ(θ) u(θ)`,   `u(s) = sin s cos²s`.

This is the quantitative form of the concavity of `x ↦ x^{α/3}`: with
`a = u(θ)`, `b = u(t)`, `p = α/3`, Bernoulli's inequality gives
`a^p − b^p ≤ p b^{p−1}(a−b)`, and multiplying by `b ≥ 0` turns this into the
statement. -/
lemma key_pointwise {α θ t : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hθ : Real.pi / 4 ≤ θ)
    (hθt : θ ≤ t) (ht : t ≤ Real.pi / 2) :
    Real.sin t * Real.cos t ^ 2 * (Work.Spaces.Gam α θ - Work.Spaces.Gam α t)
      ≤ (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) := by
  have hp0 : 0 ≤ α / 3 := by linarith
  have hp1 : α / 3 ≤ 1 := by linarith
  set a := Real.sin θ * Real.cos θ ^ 2 with ha
  set b := Real.sin t * Real.cos t ^ 2 with hb
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      (sq_nonneg _)
  have hb0 : 0 ≤ b := by
    rw [hb]
    exact mul_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      (sq_nonneg _)
  have hGθ0 : 0 ≤ Work.Spaces.Gam α θ := by
    rw [Work.Spaces.Gam]; exact Real.rpow_nonneg ha0 _
  have hsub : Work.Spaces.Gam α θ = a ^ (α / 3) := by rw [Work.Spaces.Gam, ha]
  have hsubt : Work.Spaces.Gam α t = b ^ (α / 3) := by rw [Work.Spaces.Gam, hb]
  have hGa : b ^ (α / 3) ≤ a ^ (α / 3) := by
    have h := Gam_anti hα hθ hθt ht
    rw [hsubt, hsub] at h
    exact h
  rcases eq_or_lt_of_le hb0 with hbz | hbz
  · rw [← hbz, zero_mul]
    exact mul_nonneg (mul_nonneg hp0 hGθ0) ha0
  · rw [hsubt, hsub]
    set x := (a - b) / b with hxdef
    have hx1 : -1 ≤ x := by rw [hxdef, le_div_iff₀ hbz]; linarith
    have hbx : b * (1 + x) = a := by rw [hxdef]; field_simp; try ring
    have hx0 : 0 ≤ 1 + x := by linarith
    have hBern := rpow_one_add_le_one_add_mul_self hx1 hp0 hp1
    have hbp : 0 ≤ b ^ (α / 3) := Real.rpow_nonneg hb0 _
    have h2 : b * (b ^ (α / 3) * (1 + x) ^ (α / 3)) ≤
        b * (b ^ (α / 3) * (1 + (α / 3) * x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBern hbp) (le_of_lt hbz)
    have h3 : b * (b ^ (α / 3) * (1 + (α / 3) * x)) =
        b ^ (α / 3) * b + (α / 3) * b ^ (α / 3) * (a - b) := by
      rw [hxdef]; field_simp; try ring
    have h4 : b * b ^ (α / 3) = b ^ (α / 3) * b := by ring
    have h5 : b * (a ^ (α / 3) - b ^ (α / 3)) = b * a ^ (α / 3) - b * b ^ (α / 3) := by ring
    have h1 : b * a ^ (α / 3) = b * (b * (1 + x)) ^ (α / 3) := by rw [hbx]
    have h1'' : b * (b * (1 + x)) ^ (α / 3) = b * (b ^ (α / 3) * (1 + x) ^ (α / 3)) := by
      rw [Real.mul_rpow (le_of_lt hbz) hx0]
    have h6 : b ^ (α / 3) * (a - b) ≤ a ^ (α / 3) * a := by
      have h1' : b ^ (α / 3) * (a - b) ≤ b ^ (α / 3) * a :=
        mul_le_mul_of_nonneg_left (by linarith) hbp
      have h2' : b ^ (α / 3) * a ≤ a ^ (α / 3) * a := mul_le_mul_of_nonneg_right hGa ha0
      linarith
    nlinarith [h1, h1'', h2, h3, h4, h5, h6, hp0]

/-! ## The elementary integral -/

/-- `∫_θ^{π/2} sin t cos²t dt = cos³θ/3`. -/
lemma integral_sin_cos_sq_eq (θ : ℝ) (hθ : θ ≤ Real.pi / 2) :
    ∫ t in θ..(Real.pi / 2), Real.sin t * Real.cos t ^ 2 = Real.cos θ ^ 3 / 3 := by
  have hderiv : ∀ x ∈ Set.Ioo θ (Real.pi / 2),
      HasDerivAt (fun t : ℝ => -(Real.cos t ^ 3 / 3)) (Real.sin x * Real.cos x ^ 2) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t ^ 3)
        (3 * Real.cos x ^ 2 * (-Real.sin x)) x := by
      have h := (Real.hasDerivAt_cos x).pow 3
      rw [show ((fun t : ℝ => Real.cos t) ^ 3) = (fun t : ℝ => Real.cos t ^ 3) from by
        funext t; rw [Pi.pow_apply]] at h
      simpa using h
    have hh : HasDerivAt (fun t : ℝ => -(Real.cos t ^ 3 / 3))
        (-(3 * Real.cos x ^ 2 * (-Real.sin x) / 3)) x := (h1.div_const 3).neg
    exact hh.congr_deriv (by ring)
  have hcont : ContinuousOn (fun t : ℝ => -(Real.cos t ^ 3 / 3)) (Set.Icc θ (Real.pi / 2)) := by
    fun_prop
  have hint : IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2) volume θ
      (Real.pi / 2) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.sin t * Real.cos t ^ 2)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ hcont hderiv hint
  rw [h, Real.cos_pi_div_two]
  ring

/-! ## The target estimate -/

theorem H1_bound {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1/4) (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    |3 * (∫ t in θ..(Real.pi / 2), Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t)
        / Real.cos θ ^ 3 - Work.Spaces.Gam α θ| ≤ 3 * α * Real.cos θ ^ (2 * α / 3) := by
  have hθ1 : Real.pi / 4 ≤ θ := le_of_lt hθ.1
  have hθ2 : θ ≤ Real.pi / 2 := le_of_lt hθ.2
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hGam_cont : Continuous (Work.Spaces.Gam α) := by
    change Continuous (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ (α / 3))
    exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).rpow_const
      (fun _ => Or.inr (by linarith))
  have hu_cont : Continuous (fun t : ℝ => Real.sin t * Real.cos t ^ 2) := by fun_prop
  have hInt1 : IntervalIntegrable
      (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t) volume θ
      (Real.pi / 2) := (hu_cont.mul hGam_cont).intervalIntegrable _ _
  have hInt2 : IntervalIntegrable
      (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α θ) volume θ
      (Real.pi / 2) := (hu_cont.mul continuous_const).intervalIntegrable _ _
  have hIntg : IntervalIntegrable
      (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        (Work.Spaces.Gam α t - Work.Spaces.Gam α θ)) volume θ (Real.pi / 2) :=
    (hu_cont.mul (hGam_cont.sub continuous_const)).intervalIntegrable _ _
  have hIntN : IntervalIntegrable
      (fun t : ℝ => -(Real.sin t * Real.cos t ^ 2 *
        (Work.Spaces.Gam α t - Work.Spaces.Gam α θ))) volume θ (Real.pi / 2) := hIntg.neg
  have hIu : (∫ t in θ..(Real.pi / 2), Real.sin t * Real.cos t ^ 2) = Real.cos θ ^ 3 / 3 :=
    integral_sin_cos_sq_eq θ hθ2
  set A := ∫ t in θ..(Real.pi / 2), Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t with hA
  set Q := ∫ t in θ..(Real.pi / 2),
      Real.sin t * Real.cos t ^ 2 * (Work.Spaces.Gam α t - Work.Spaces.Gam α θ) with hQ
  set P := Real.cos θ ^ 3 with hP
  have hPpos : 0 < P := by rw [hP]; positivity
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ := by
    rw [Work.Spaces.Gam]
    exact Real.rpow_nonneg (mul_nonneg hsin0 (sq_nonneg _)) _
  have hGθint : (∫ t in θ..(Real.pi / 2),
        Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α θ)
      = Work.Spaces.Gam α θ * (Real.cos θ ^ 3 / 3) := by
    rw [show (∫ t in θ..(Real.pi / 2),
          Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α θ)
        = Work.Spaces.Gam α θ *
            (∫ t in θ..(Real.pi / 2), Real.sin t * Real.cos t ^ 2) from by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun t _ => by ring), hIu]
  have hId : A - Work.Spaces.Gam α θ * (P / 3) = Q := by
    rw [hA, hQ, hP, ← hGθint, ← intervalIntegral.integral_sub hInt1 hInt2]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have hQ_le : Q ≤ 0 := by
    rw [hQ]
    have h0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume θ (Real.pi / 2) :=
      intervalIntegrable_const
    have hle : ∀ t ∈ Set.Icc θ (Real.pi / 2),
        Real.sin t * Real.cos t ^ 2 * (Work.Spaces.Gam α t - Work.Spaces.Gam α θ) ≤ (0 : ℝ) := by
      intro t ht
      have hu0 : 0 ≤ Real.sin t * Real.cos t ^ 2 :=
        mul_nonneg
          (Real.sin_nonneg_of_mem_Icc ⟨by linarith [ht.1, hθ1, Real.pi_pos],
            by linarith [ht.2, Real.pi_pos]⟩)
          (sq_nonneg _)
      have hG : Work.Spaces.Gam α t - Work.Spaces.Gam α θ ≤ 0 := by
        have := Gam_anti hα hθ1 ht.1 ht.2
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos hu0 hG
    have hmono := intervalIntegral.integral_mono_on hθ2 hIntg h0 hle
    simpa using hmono
  have hQ_low : -Q ≤ (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) *
      (Real.pi / 2 - θ) := by
    rw [hQ, ← intervalIntegral.integral_neg]
    have hle : ∀ t ∈ Set.Icc θ (Real.pi / 2),
        -(Real.sin t * Real.cos t ^ 2 * (Work.Spaces.Gam α t - Work.Spaces.Gam α θ))
          ≤ (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) := by
      intro t ht
      have := key_pointwise hα hα1 hθ1 ht.1 ht.2
      linarith
    have hconst : IntervalIntegrable
        (fun _ : ℝ => (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2))
        volume θ (Real.pi / 2) := intervalIntegrable_const
    have h1 := intervalIntegral.integral_mono_on hθ2 hIntN hconst hle
    have h2 : (∫ _ in θ..(Real.pi / 2),
          (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2))
        = (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) *
            (Real.pi / 2 - θ) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rwa [h2] at h1
  have hkey : 3 * A / P - Work.Spaces.Gam α θ = 3 * Q / P := by
    have h1 : 3 * A - Work.Spaces.Gam α θ * P = 3 * Q := by linarith [hId]
    field_simp
    linarith
  have hcos2 : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  have hδ : Real.pi / 2 - θ ≤ (Real.pi / 2) * Real.cos θ := by
    have h := Real.mul_le_sin (x := Real.pi / 2 - θ) (by linarith) (by linarith)
    rw [Real.sin_pi_div_two_sub] at h
    have h' : (Real.pi / 2) * ((2 / Real.pi) * (Real.pi / 2 - θ)) ≤
        (Real.pi / 2) * Real.cos θ :=
      mul_le_mul_of_nonneg_left h (by linarith [Real.pi_pos])
    have h'' : (Real.pi / 2) * ((2 / Real.pi) * (Real.pi / 2 - θ)) = Real.pi / 2 - θ := by
      field_simp
    linarith [h', h''.le, h''.ge]
  have hup : Real.sin θ * Real.cos θ ^ 2 * (Real.pi / 2 - θ) ≤ (Real.pi / 2) * P := by
    rw [hP]
    have h1 : Real.sin θ * Real.cos θ ^ 2 ≤ Real.cos θ ^ 2 := by
      nlinarith [Real.sin_le_one θ, hcos2, hsin0]
    calc Real.sin θ * Real.cos θ ^ 2 * (Real.pi / 2 - θ)
        ≤ Real.cos θ ^ 2 * (Real.pi / 2 - θ) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ Real.cos θ ^ 2 * ((Real.pi / 2) * Real.cos θ) :=
          mul_le_mul_of_nonneg_left hδ hcos2
      _ = (Real.pi / 2) * Real.cos θ ^ 3 := by ring
  have hGam_le : Work.Spaces.Gam α θ ≤ Real.cos θ ^ (2 * α / 3) :=
    Gam_le_cos_rpow hα ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hcos23 : (0 : ℝ) ≤ Real.cos θ ^ (2 * α / 3) := Real.rpow_nonneg (le_of_lt hcos) _
  have hπ2le3 : Real.pi / 2 ≤ 3 := by linarith [Real.pi_lt_four]
  have habs : |3 * A / P - Work.Spaces.Gam α θ| = 3 * (-Q) / P := by
    rw [hkey, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_nonpos hQ_le,
      abs_of_pos hPpos]
  have hfinal : 3 * (-Q) / P ≤ 3 * α * Real.cos θ ^ (2 * α / 3) := by
    have hstep : 3 * (-Q) ≤ 3 * α * Real.cos θ ^ (2 * α / 3) * P := by
      have h1 : -Q ≤ (α / 3) * Work.Spaces.Gam α θ * ((Real.pi / 2) * P) := by
        have hAG : 0 ≤ (α / 3) * Work.Spaces.Gam α θ := mul_nonneg (by linarith) hGam0
        have h1' : (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) *
              (Real.pi / 2 - θ)
            ≤ (α / 3) * Work.Spaces.Gam α θ * ((Real.pi / 2) * P) := by
          have hE : (α / 3) * Work.Spaces.Gam α θ * (Real.sin θ * Real.cos θ ^ 2) *
                (Real.pi / 2 - θ)
              = (α / 3) * Work.Spaces.Gam α θ *
                (Real.sin θ * Real.cos θ ^ 2 * (Real.pi / 2 - θ)) := by ring
          rw [hE]
          exact mul_le_mul_of_nonneg_left hup hAG
        linarith [hQ_low, h1']
      have h2 : 3 * ((α / 3) * Work.Spaces.Gam α θ * ((Real.pi / 2) * P))
          ≤ 3 * α * Real.cos θ ^ (2 * α / 3) * P := by
        have hAG : 0 ≤ α * Work.Spaces.Gam α θ := mul_nonneg (le_of_lt hα) hGam0
        have h3 : (Real.pi / 2) * (α * Work.Spaces.Gam α θ) ≤
            3 * (α * Real.cos θ ^ (2 * α / 3)) := by
          have h4 : α * Work.Spaces.Gam α θ ≤ α * Real.cos θ ^ (2 * α / 3) :=
            mul_le_mul_of_nonneg_left hGam_le (le_of_lt hα)
          have h5 : 0 ≤ α * Real.cos θ ^ (2 * α / 3) := mul_nonneg (le_of_lt hα) hcos23
          nlinarith [h4, h5, hπ2le3]
        nlinarith [h3, le_of_lt hPpos]
      linarith [h1, h2]
    rw [div_le_iff₀ hPpos]
    linarith [hstep]
  rw [habs]
  exact hfinal

end Work.FTS.PhiStar.Psi0Est
