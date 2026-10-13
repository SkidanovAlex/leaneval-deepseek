/-
# Bounds for the angular tail `∫_θ^{π/2} cos²t · Γ(α,t) / sin t dt`

With `Γ(α,t) = (sin t · cos²t)^{α/3}` (`Work.Spaces.Gam`), the integrand
`cos²t · Γ(α,t) / sin t = cos(t)^{2+2α/3} · sin(t)^{α/3-1}` has an integrable
singularity at `t = 0` and vanishes like `cos(t)^{2+2α/3}` at `t = π/2`.

The two estimates proved here (with the universal constant `K = 100`):

* on `[0, 2/3]` the whole tail is `O(1/α)`: the mass concentrates at the lower
  end, where `∫_0^{2/3} sin^{α/3-1} ≤ (π/2)^{1-α/3}(2/3)^{α/3}/(α/3)` by
  Jordan's inequality `sin t ≥ 2t/π`, and the remaining piece `[2/3,π/2]` is
  bounded by `4/3`;
* on `[2/3, π/2]` the tail is dominated by `cos³θ · Γ(α,θ)`: the pointwise
  bound `cos^{2+2α/3}t sin^{α/3-1}t ≤ 4 cos^{2+2α/3}t sin t` together with the
  fundamental theorem of calculus gives
  `∫_θ^{π/2} ≤ 4 cos(θ)^{3+2α/3}/(3+2α/3)`, and `sin(θ)^{α/3} ≥ 1/2` on this
  range, which converts the right-hand side into `100 cos³θ Γ(α,θ)`.

Both integrals are evaluated with `integral_rpow` and the FTC (the antiderivative
of `cos^{2+2p}t sin t` being `-cos^{3+2p}t/(3+2p)`); the comparison of a possibly
non-integrable integrand with an integrable majorant is via
`MeasureTheory.integral_mono_of_nonneg`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The integrand `cos²t · Γ(α,t) / sin t` of the angular tail integral. -/
def Igr (α t : ℝ) : ℝ := Real.cos t ^ 2 * Work.Spaces.Gam α t / Real.sin t

/-! ## Elementary identities and pointwise bounds -/

/-- The basic rewrite `c² (s c²)^p / s = c^{2+2p} s^{p-1}` for `c, s > 0`. -/
lemma rpow_id (p c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    c ^ 2 * (s * c ^ 2) ^ p / s = c ^ (2 + 2 * p) * s ^ (p - 1) := by
  rw [show (c ^ 2 : ℝ) = c ^ (2 : ℝ) by norm_num [Real.rpow_ofNat]]
  have hc2 : (0 : ℝ) < c ^ (2 : ℝ) := Real.rpow_pos_of_pos hc 2
  have h1 : (s * c ^ (2 : ℝ)) ^ p = s ^ p * (c ^ (2 : ℝ)) ^ p :=
    Real.mul_rpow (le_of_lt hs) (le_of_lt hc2)
  rw [h1, ← Real.rpow_mul (le_of_lt hc) (2 : ℝ) p]
  have h3 : c ^ (2 + 2 * p) = c ^ (2 : ℝ) * c ^ (2 * p) := Real.rpow_add hc 2 (2 * p)
  rw [h3, show s ^ (p - 1) = s ^ p / s ^ (1 : ℝ) by rw [Real.rpow_sub hs p 1], Real.rpow_one]
  ring

/-- For `t ∈ (0,π/2)` the integrand equals `cos(t)^{2+2α/3} sin(t)^{α/3-1}`. -/
lemma Igr_eq (α t : ℝ) (ht0 : 0 < t) (ht1 : t < π / 2) :
    Igr α t = Real.cos t ^ (2 + 2 * (α / 3)) * Real.sin t ^ (α / 3 - 1) := by
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht1⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
  rw [Igr, Work.Spaces.Gam]
  exact rpow_id (α / 3) (Real.cos t) (Real.sin t) hc hs

/-- The integrand is nonnegative on `(0,π/2]`. -/
lemma Igr_nonneg (α t : ℝ) (_hα : 0 < α) (ht : t ∈ Set.Ioc 0 (π / 2)) : 0 ≤ Igr α t := by
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · obtain ⟨ht0, _⟩ := ht
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
    have hG : 0 ≤ Work.Spaces.Gam α t :=
      Real.rpow_nonneg (mul_nonneg (le_of_lt hs) (sq_nonneg _)) _
    rw [Igr]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hG) (le_of_lt hs)
  · subst heq
    rw [Igr, Real.cos_pi_div_two]
    simp

/-- On `(0,π/2]` the integrand is dominated by `sin(t)^{α/3-1}`. -/
lemma Igr_le_sin (α t : ℝ) (hα : 0 < α) (ht : t ∈ Set.Ioc 0 (π / 2)) :
    Igr α t ≤ Real.sin t ^ (α / 3 - 1) := by
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · obtain ⟨ht0, _⟩ := ht
    have hc : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
    rw [Igr_eq α t ht0 hlt]
    have h1 : Real.cos t ^ (2 + 2 * (α / 3)) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hc) (Real.cos_le_one t) (by positivity)
    calc Real.cos t ^ (2 + 2 * (α / 3)) * Real.sin t ^ (α / 3 - 1)
        ≤ 1 * Real.sin t ^ (α / 3 - 1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (le_of_lt hs) _)
      _ = Real.sin t ^ (α / 3 - 1) := one_mul _
  · subst heq
    rw [Igr, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp

/-- Jordan-type linear majorant: `sin(t)^{p-1} ≤ (π/2)^{1-p} t^{p-1}` on `(0,π/2]`
for `p ≤ 1`. -/
lemma sin_rpow_le_lin (p t : ℝ) (hp1 : p ≤ 1) (ht : t ∈ Set.Ioc 0 (π / 2)) :
    Real.sin t ^ (p - 1) ≤ (π / 2) ^ (1 - p) * t ^ (p - 1) := by
  obtain ⟨ht0, ht1⟩ := ht
  have hsin : 2 / π * t ≤ Real.sin t := Real.mul_le_sin (le_of_lt ht0) ht1
  have hpos : 0 < 2 / π * t := by positivity
  have hp2 : p - 1 ≤ 0 := by linarith
  have key := Real.rpow_le_rpow_of_nonpos hpos hsin hp2
  have hmr : (2 / π * t) ^ (p - 1) = (2 / π) ^ (p - 1) * t ^ (p - 1) :=
    Real.mul_rpow (by positivity) (le_of_lt ht0)
  have hcoef : (2 / π : ℝ) ^ (p - 1) = (π / 2) ^ (1 - p) := by
    rw [show (2 / π : ℝ) = (π / 2)⁻¹ by ring, Real.inv_rpow (by positivity : (0 : ℝ) ≤ π / 2),
      show (1 : ℝ) - p = -(p - 1) by ring, Real.rpow_neg (by positivity : (0 : ℝ) ≤ π / 2)]
  rw [hmr, hcoef] at key
  exact key

/-- On `[2/3, π/2]` the integrand is dominated by `4 cos(t)^{2+2α/3} sin t`. -/
lemma Igr_le_hard (α t : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (ht : t ∈ Set.Icc (2 / 3) (π / 2)) :
    Igr α t ≤ 4 * (Real.cos t ^ (2 + 2 * (α / 3)) * Real.sin t) := by
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · obtain ⟨ht2, _⟩ := ht
    have ht0 : 0 < t := by linarith
    have hsl : (1 : ℝ) / 2 ≤ Real.sin t := by
      have h1 : Real.pi / 6 ≤ t := by have := Real.pi_lt_four; linarith
      have h2 := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 6) (y := t)
        (by linarith [Real.pi_pos]) hlt.le h1
      rwa [Real.sin_pi_div_six] at h2
    rw [Igr_eq α t ht0 hlt]
    have hpow : Real.sin t ^ (α / 3 - 1) ≤ 4 * Real.sin t := by
      have h1 : Real.sin t ^ (α / 3 - 1) ≤ (1 / 2 : ℝ) ^ (α / 3 - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hsl (by linarith)
      have h2 : (1 / 2 : ℝ) ^ (α / 3 - 1) = 2 ^ (1 - α / 3) := by
        rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
        rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (α / 3 - 1),
          show -(α / 3 - 1) = 1 - α / 3 by ring]
      have h3 : (2 : ℝ) ^ (1 - α / 3) ≤ 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
          (by linarith : 1 - α / 3 ≤ 1)
        rwa [Real.rpow_one] at this
      linarith [hsl]
    have hc0 : 0 ≤ Real.cos t ^ (2 + 2 * (α / 3)) :=
      Real.rpow_nonneg (le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩)) _
    calc Real.cos t ^ (2 + 2 * (α / 3)) * Real.sin t ^ (α / 3 - 1)
        ≤ Real.cos t ^ (2 + 2 * (α / 3)) * (4 * Real.sin t) :=
          mul_le_mul_of_nonneg_left hpow hc0
      _ = 4 * (Real.cos t ^ (2 + 2 * (α / 3)) * Real.sin t) := by ring
  · subst heq
    rw [Igr, Real.cos_pi_div_two]
    simp [Real.zero_rpow (by linarith : 2 + 2 * (α / 3) ≠ 0)]

/-- The right-hand-side comparison for the second estimate:
`4 cos(θ)^{3+2p}/(3+2p) ≤ 100 cos³θ (sinθ cos²θ)^p` on `[2/3, π/2]`. -/
lemma hard_compare (p θ : ℝ) (hp0 : 0 < p) (hple : p ≤ 1) (hθ : θ ∈ Set.Icc (2 / 3) (π / 2)) :
    4 * (Real.cos θ) ^ (3 + 2 * p) / (3 + 2 * p)
      ≤ 100 * (Real.cos θ) ^ 3 * (Real.sin θ * Real.cos θ ^ 2) ^ p := by
  obtain ⟨hθ0, hθ2⟩ := hθ
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [hθ2, Real.pi_pos]⟩
  have hs12 : (1 : ℝ) / 2 ≤ Real.sin θ := by
    have h1 : Real.pi / 6 ≤ θ := by have := Real.pi_lt_four; linarith
    have h2 := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi / 6) (y := θ)
      (by linarith [Real.pi_pos]) hθ2 h1
    rwa [Real.sin_pi_div_six] at h2
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [hθ2, Real.pi_pos]⟩
  have hsp : (1 : ℝ) / 2 ≤ Real.sin θ ^ p := by
    have h1 : (1 / 2 : ℝ) ^ p ≤ Real.sin θ ^ p :=
      Real.rpow_le_rpow (by norm_num) hs12 (le_of_lt hp0)
    have h2 : (1 : ℝ) / 2 ≤ (1 / 2 : ℝ) ^ p := by
      have := Real.rpow_le_rpow_of_exponent_ge (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hple
      rwa [Real.rpow_one] at this
    linarith
  have hcoeff : 4 / (3 + 2 * p) ≤ 100 * Real.sin θ ^ p := by
    have h1 : 4 / (3 + 2 * p) ≤ 4 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    linarith
  rcases eq_or_lt_of_le hcos0 with hzero | hpos
  · rw [← hzero, Real.zero_rpow (by linarith : 3 + 2 * p ≠ 0)]
    simp
  · have h1 : (Real.cos θ) ^ (3 + 2 * p) = (Real.cos θ) ^ 3 * (Real.cos θ) ^ (2 * p) := by
      rw [Real.rpow_add hpos 3 (2 * p)]
      norm_num [Real.rpow_ofNat]
    have h2 : (Real.sin θ * Real.cos θ ^ 2) ^ p = Real.sin θ ^ p * (Real.cos θ) ^ (2 * p) := by
      rw [show (Real.cos θ ^ 2 : ℝ) = (Real.cos θ) ^ (2 : ℝ) by norm_num [Real.rpow_ofNat],
        Real.mul_rpow hsin0 (Real.rpow_nonneg hcos0 2), ← Real.rpow_mul hcos0 2 p]
    calc 4 * (Real.cos θ) ^ (3 + 2 * p) / (3 + 2 * p)
        = (4 / (3 + 2 * p)) * ((Real.cos θ) ^ 3 * (Real.cos θ) ^ (2 * p)) := by rw [h1]; ring
      _ ≤ (100 * Real.sin θ ^ p) * ((Real.cos θ) ^ 3 * (Real.cos θ) ^ (2 * p)) :=
          mul_le_mul_of_nonneg_right hcoeff
            (mul_nonneg (pow_nonneg hcos0 3) (Real.rpow_nonneg hcos0 _))
      _ = 100 * (Real.cos θ) ^ 3 * (Real.sin θ * Real.cos θ ^ 2) ^ p := by rw [h2]; ring

/-! ## The two integrals -/

/-- `∫_a^b t^{p-1} dt = (b^p - a^p)/p` for `p > 0`. -/
lemma integral_rpow_sub (p a b : ℝ) (hp : 0 < p) :
    ∫ t in a..b, t ^ (p - 1) = (b ^ p - a ^ p) / p := by
  have h := integral_rpow (a := a) (b := b) (r := p - 1) (Or.inl (by linarith : -1 < p - 1))
  rw [show p - 1 + 1 = p by ring] at h
  exact h

/-- `∫_a^b cos(t)^{2+2p} sin t dt = (cos a^{3+2p} - cos b^{3+2p})/(3+2p)`. -/
lemma integral_cos_sin (p a b : ℝ) (hp : 0 < p) (hab : a ≤ b) :
    ∫ t in a..b, Real.cos t ^ (2 + 2 * p) * Real.sin t
      = (Real.cos a ^ (3 + 2 * p) - Real.cos b ^ (3 + 2 * p)) / (3 + 2 * p) := by
  have hden : 3 + 2 * p ≠ 0 := by linarith
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun t : ℝ => -(Real.cos t ^ (3 + 2 * p)) / (3 + 2 * p))
        (Real.cos x ^ (2 + 2 * p) * Real.sin x) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t ^ (3 + 2 * p))
        ((-Real.sin x) * (3 + 2 * p) * Real.cos x ^ (2 + 2 * p)) x := by
      have h := (Real.hasDerivAt_cos x).rpow_const (Or.inr (by linarith : (1 : ℝ) ≤ 3 + 2 * p))
      rwa [show 3 + 2 * p - 1 = 2 + 2 * p by ring] at h
    have h2 : HasDerivAt (fun t : ℝ => -(Real.cos t ^ (3 + 2 * p)) / (3 + 2 * p))
        (-((-Real.sin x) * (3 + 2 * p) * Real.cos x ^ (2 + 2 * p)) / (3 + 2 * p)) x :=
      h1.neg.div_const (3 + 2 * p)
    convert h2 using 1
    field_simp
  have hcast : Continuous (fun t : ℝ => Real.cos t ^ (3 + 2 * p)) :=
    (Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 3 + 2 * p)).comp Real.continuous_cos
  have hcont : ContinuousOn (fun t : ℝ => -(Real.cos t ^ (3 + 2 * p)) / (3 + 2 * p))
      (Set.Icc a b) := ((hcast.neg).div_const _).continuousOn
  have hint : IntervalIntegrable (fun t : ℝ => Real.cos t ^ (2 + 2 * p) * Real.sin t)
      volume a b :=
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 + 2 * p)).comp
      Real.continuous_cos).mul Real.continuous_sin).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
  rw [h]
  ring

/-- Comparison of an interval integral with an integrable majorant, without
integrability of the integrand itself. -/
lemma integral_le_of_majorant {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Ioc a b, 0 ≤ f t) (hg : IntegrableOn g (Set.Ioc a b))
    (hle : ∀ t ∈ Set.Ioc a b, f t ≤ g t) :
    ∫ t in a..b, f t ≤ ∫ t in a..b, g t := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hg ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hf t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hle t ht

/-! ## The two estimates -/

/-- The first estimate: on `[0, 2/3]` the tail is `≤ 100/α`. -/
theorem conjunct1 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (2 / 3)) :
    ∫ t in θ..(π / 2), Igr α t ≤ 100 / α := by
  obtain ⟨hθ0, hθ2⟩ := hθ
  have hθle : θ ≤ π / 2 := by linarith [hθ2, Real.pi_gt_three]
  set p : ℝ := α / 3 with hpdef
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hple : p ≤ 1 := by rw [hpdef]; linarith
  have hhalf : (0 : ℝ) < π / 2 := by positivity
  have hpip : (π / 2) ^ (1 - p) * (π / 2) ^ p = π / 2 := by
    rw [← Real.rpow_add hhalf (1 - p) p, show 1 - p + p = 1 by ring, Real.rpow_one]
  set M : ℝ → ℝ :=
    fun t => (π / 2) ^ (1 - p) * t ^ (p - 1) + 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t)
    with hMdef
  have hint1 : IntegrableOn (fun t : ℝ => (π / 2) ^ (1 - p) * t ^ (p - 1)) (Set.Ioc θ (π / 2)) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := θ) (b := π / 2)
        (by linarith : -1 < p - 1) :
        IntervalIntegrable (fun t : ℝ => t ^ (p - 1)) volume θ (π / 2)).1).const_mul _
  have hint2 : IntegrableOn (fun t : ℝ => 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t))
      (Set.Ioc θ (π / 2)) :=
    ((continuous_const.mul (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 + 2 * p)).comp
      Real.continuous_cos).mul Real.continuous_sin)).intervalIntegrable θ (π / 2)).1
  have hMint : IntegrableOn M (Set.Ioc θ (π / 2)) := hint1.add hint2
  have key : ∫ t in θ..(π / 2), Igr α t ≤ ∫ t in θ..(π / 2), M t := by
    apply integral_le_of_majorant hθle
    · intro t ht
      exact Igr_nonneg α t hα ⟨by linarith [ht.1, hθ0], ht.2⟩
    · exact hMint
    · intro t ht
      obtain ⟨ht0, ht1⟩ := ht
      have htpos : 0 < t := by linarith [ht0, hθ0]
      have hsin0 : 0 ≤ Real.sin t :=
        Real.sin_nonneg_of_mem_Icc ⟨le_of_lt htpos, by linarith [ht1, Real.pi_pos]⟩
      have hcos0 : 0 ≤ Real.cos t :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [ht1, Real.pi_pos]⟩
      have hM : M t = (π / 2) ^ (1 - p) * t ^ (p - 1)
          + 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t) := rfl
      rcases le_total t (2 / 3) with hcase | hcase
      · have h1 : Igr α t ≤ (π / 2) ^ (1 - p) * t ^ (p - 1) :=
          le_trans (Igr_le_sin α t hα ⟨htpos, ht1⟩)
            (sin_rpow_le_lin p t hple ⟨htpos, ht1⟩)
        have h2 : 0 ≤ 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t) :=
          mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg hcos0 _) hsin0)
        rw [hM]; linarith
      · have h4 : Igr α t ≤ 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t) :=
          Igr_le_hard α t hα hα1 ⟨hcase, ht1⟩
        have h5 : 0 ≤ (π / 2) ^ (1 - p) * t ^ (p - 1) :=
          mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (le_of_lt htpos) _)
        rw [hM]; linarith
  have hMval : ∫ t in θ..(π / 2), M t
      = (π / 2) ^ (1 - p) * (((π / 2) ^ p - θ ^ p) / p)
        + 4 * ((Real.cos θ) ^ (3 + 2 * p) - (Real.cos (π / 2)) ^ (3 + 2 * p)) / (3 + 2 * p) := by
    have h1 : IntervalIntegrable (fun t : ℝ => (π / 2) ^ (1 - p) * t ^ (p - 1)) volume θ (π / 2) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := θ) (b := π / 2)
        (by linarith : -1 < p - 1)).const_mul _
    have h2 : IntervalIntegrable (fun t : ℝ => 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t))
        volume θ (π / 2) :=
      (continuous_const.mul (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 + 2 * p)).comp
        Real.continuous_cos).mul Real.continuous_sin)).intervalIntegrable θ (π / 2)
    rw [hMdef]
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_rpow_sub p θ (π / 2) hp0,
      integral_cos_sin p θ (π / 2) hp0 hθle]
    ring
  have hMle : ∫ t in θ..(π / 2), M t ≤ (π / 2) / p + 4 / (3 + 2 * p) := by
    rw [hMval]
    have h1 : (π / 2) ^ (1 - p) * (((π / 2) ^ p - θ ^ p) / p)
        ≤ (π / 2) ^ (1 - p) * ((π / 2) ^ p / p) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
      apply div_le_div_of_nonneg_right _ (le_of_lt hp0)
      linarith [Real.rpow_nonneg hθ0 p]
    have h2 : 4 * ((Real.cos θ) ^ (3 + 2 * p) - (Real.cos (π / 2)) ^ (3 + 2 * p)) / (3 + 2 * p)
        ≤ 4 / (3 + 2 * p) := by
      rw [Real.cos_pi_div_two, Real.zero_rpow (by linarith : 3 + 2 * p ≠ 0), sub_zero]
      apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ 3 + 2 * p)
      have hc0 : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [hθle, Real.pi_pos]⟩
      have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
      have := Real.rpow_le_one hc0 hc1 (by linarith : (0 : ℝ) ≤ 3 + 2 * p)
      linarith
    have h3 : (π / 2) ^ (1 - p) * ((π / 2) ^ p / p) = (π / 2) / p := by
      rw [← mul_div_assoc, hpip]
    linarith
  have hfin : (π / 2) / p + 4 / (3 + 2 * p) ≤ 100 / α := by
    have hA : (π / 2) / p ≤ 6 / α := by
      rw [hpdef]
      rw [show (π / 2) / (α / 3) = (3 * π / 2) / α by ring]
      apply div_le_div_of_nonneg_right _ (le_of_lt hα)
      linarith [Real.pi_lt_four]
    have hB : 4 / (3 + 2 * p) ≤ 94 / α := by
      rw [hpdef]
      have hb1 : 4 / (3 + 2 * (α / 3)) ≤ 4 / 3 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        linarith
      have hb2 : (4 : ℝ) / 3 ≤ 94 / α := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hα]
        linarith
      linarith
    have hsum : 6 / α + 94 / α = 100 / α := by ring
    linarith
  linarith

/-- The second estimate: on `[2/3, π/2]` the tail is `≤ 100 cos³θ Γ(α,θ)`. -/
theorem conjunct2 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (2 / 3) (π / 2)) :
    ∫ t in θ..(π / 2), Igr α t ≤ 100 * Real.cos θ ^ 3 * Work.Spaces.Gam α θ := by
  obtain ⟨hθ0, hθ2⟩ := hθ
  set p : ℝ := α / 3 with hpdef
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hple : p ≤ 1 := by rw [hpdef]; linarith
  have key : ∫ t in θ..(π / 2), Igr α t
      ≤ ∫ t in θ..(π / 2), 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t) := by
    apply integral_le_of_majorant hθ2
    · intro t ht
      exact Igr_nonneg α t hα ⟨by linarith [ht.1, hθ0], ht.2⟩
    · exact ((continuous_const.mul (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 + 2 * p)).comp
        Real.continuous_cos).mul Real.continuous_sin)).intervalIntegrable θ (π / 2)).1
    · intro t ht
      obtain ⟨ht0, ht1⟩ := ht
      exact Igr_le_hard α t hα hα1 ⟨by linarith [ht0, hθ0], ht1⟩
  have hval : ∫ t in θ..(π / 2), 4 * (Real.cos t ^ (2 + 2 * p) * Real.sin t)
      = 4 * ((Real.cos θ) ^ (3 + 2 * p) - (Real.cos (π / 2)) ^ (3 + 2 * p)) / (3 + 2 * p) := by
    rw [intervalIntegral.integral_const_mul, integral_cos_sin p θ (π / 2) hp0 hθ2]
    ring
  have hzero : (Real.cos (π / 2)) ^ (3 + 2 * p) = 0 := by
    rw [Real.cos_pi_div_two, Real.zero_rpow (by linarith : 3 + 2 * p ≠ 0)]
  calc ∫ t in θ..(π / 2), Igr α t
      ≤ 4 * ((Real.cos θ) ^ (3 + 2 * p) - (Real.cos (π / 2)) ^ (3 + 2 * p)) / (3 + 2 * p) := by
        rw [← hval]; exact key
    _ = 4 * (Real.cos θ) ^ (3 + 2 * p) / (3 + 2 * p) := by rw [hzero, sub_zero]
    _ ≤ 100 * (Real.cos θ) ^ 3 * (Real.sin θ * Real.cos θ ^ 2) ^ p :=
          hard_compare p θ hp0 hple ⟨hθ0, hθ2⟩
    _ = 100 * Real.cos θ ^ 3 * Work.Spaces.Gam α θ := by rw [Work.Spaces.Gam, ← hpdef]

/-- **The angular tail bounds.**  There is a universal constant `K` such that for every
`0 < α ≤ 1/4` the tail `∫_θ^{π/2} cos²t Γ(α,t)/sin t dt` is `≤ K/α` for `θ ∈ [0,2/3]`
and `≤ K cos³θ Γ(α,θ)` for `θ ∈ [2/3, π/2]`. -/
theorem cos_sq_Gam_div_sin_bounds : ∃ K : ℝ, 0 < K ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Icc (0 : ℝ) (2 / 3),
      (∫ t in θ..(Real.pi / 2), Real.cos t ^ 2 * Work.Spaces.Gam α t / Real.sin t) ≤ K / α) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Icc (2 / 3 : ℝ) (Real.pi / 2),
      (∫ t in θ..(Real.pi / 2), Real.cos t ^ 2 * Work.Spaces.Gam α t / Real.sin t)
        ≤ K * Real.cos θ ^ 3 * Work.Spaces.Gam α θ) := by
  refine ⟨100, by norm_num, ?_, ?_⟩
  · intro α hα hα1 θ hθ
    simpa only [Igr] using conjunct1 α hα hα1 θ hθ
  · intro α hα hα1 θ hθ
    simpa only [Igr] using conjunct2 α hα hα1 θ hθ

end Work.FTS.PhiStar.Psi0Aux
