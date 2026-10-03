/-
# Regularity and compact support of the §6 lattice phase `Ψ(t) = F(|t₁²z₂ − t₂²z₁|²/|Δ|²)`

`Work.FIArea2.PsiC F z₁ z₂` is the complex-valued smooth phase of the Poisson step (6.7): on the
plane it is `t ↦ F (|t₁²z₂ − t₂²z₁|²/|Δ|²)`, so that on the parametrising lattice point `(c₁,c₂)`
it takes the value `F(|w|²)`, `w = wOf z₁ z₂ c₁ c₂` (`Work.FIArea2.gphase_wOf`).  Poisson summation
(`Work.FIArea2.poisson_coset_2d`) needs it to be `C³` with compact support; this file supplies both.

* The `C³` statement is a composition: `t ↦ (t₁²z₂ − t₂²z₁)` is a polynomial (hence `C⁴`), `F` is
  `C⁴`, and the inclusion `ℝ ↪ ℂ` is smooth.

* Compact support is where `Δ(z₁,z₂) = Im(z̄₁z₂) ≠ 0` is used: writing the phase as
  `|t₁²z₂ − t₂²z₁|²/Δ²` and letting `Δr = r₁s₂ − s₁r₂` (the coordinates of `Δ`), the identity
  `Δr²(t₁⁴ + t₂⁴) = (r₁v − s₁u)² + (r₂v − s₂u)²` (with `u = t₁²r₂ − t₂²r₁`, `v = t₁²s₂ − t₂²s₁`)
  bounds the quartic `t₁⁴ + t₂⁴` by a positive multiple of the phase.  Since `F` has compact
  support, the level sets of the phase on which `F` can be nonzero are bounded, so `Ψ` vanishes
  outside a ball.
-/
import Mathlib
import Submission.Work.FIArea2.CCountPoissonDefs
import Submission.Work.FIArea4.S15delta

set_option autoImplicit false

namespace Work.FIArea2

open Work.FIPlan

/-- In coordinates `z₁ = r₁ + i s₁`, `z₂ = r₂ + i s₂` the phase `gphase z₁ z₂ t` is the rational
function `((t₁²r₂ − t₂²r₁)² + (t₁²s₂ − t₂²s₁)²) / (r₁s₂ − s₁r₂)²`; the denominator is `|Δ|²`
rewritten through `Work.FIArea4.Delta_eq`. -/
private lemma gphase_eq_form (z1 z2 : GaussianInt) (t : ℝ × ℝ) :
    gphase z1 z2 t
      = (((t.1^2 * (z2.re:ℝ) - t.2^2 * (z1.re:ℝ))^2
          + (t.1^2 * (z2.im:ℝ) - t.2^2 * (z1.im:ℝ))^2)
         / ((z1.re:ℝ)*(z2.im:ℝ) - (z1.im:ℝ)*(z2.re:ℝ))^2) := by
  rw [gphase]
  have hD2 : ((absDelta z1 z2 : ℕ) : ℝ)^2
      = ((z1.re:ℝ)*(z2.im:ℝ) - (z1.im:ℝ)*(z2.re:ℝ))^2 := by
    rw [absDelta, Nat.cast_natAbs, Int.cast_abs, sq_abs, Work.FIArea4.Delta_eq]
    push_cast; ring
  rw [hD2]

/-- **Coercivity of the quartic form.**  If `a₁b₂ − b₁a₂ ≠ 0`, the level set where
`((t₁²a₂ − t₂²a₁)² + (t₁²b₂ − t₂²b₁)²)/(a₁b₂ − b₁a₂)² ≤ R₀` is contained in a ball of radius
`(K R₀)^{1/4} + 1`, `K = a₁² + b₁² + a₂² + b₂²`.

The two linear forms `u = t₁²a₂ − t₂²a₁`, `v = t₁²b₂ − t₂²b₁` invert the quartic:
`(a₁b₂ − b₁a₂)·t₁² = a₁v − b₁u` and `(a₁b₂ − b₁a₂)·t₂² = a₂v − b₂u`, whence by Cauchy–Schwarz
`(a₁b₂ − b₁a₂)²(t₁⁴ + t₂⁴) ≤ K(u² + v²)`. -/
private lemma quartic_coercive (a1 a2 b1 b2 R₀ : ℝ) (hΔr : a1*b2 - b1*a2 ≠ 0) (hR₀ : 0 ≤ R₀) :
    ∀ t : ℝ×ℝ,
      ((t.1^2*a2 - t.2^2*a1)^2 + (t.1^2*b2 - t.2^2*b1)^2)/(a1*b2-b1*a2)^2 ≤ R₀ →
      ‖t‖ ≤ Real.sqrt (Real.sqrt ((a1^2+b1^2+a2^2+b2^2)*R₀)) + 1 := by
  intro t ht
  set U : ℝ := t.1^2*a2 - t.2^2*a1 with hU
  set V : ℝ := t.1^2*b2 - t.2^2*b1 with hV
  have hΔr2 : 0 < (a1*b2-b1*a2)^2 := sq_pos_of_ne_zero hΔr
  have ht5 : U^2 + V^2 ≤ R₀ * (a1*b2-b1*a2)^2 := by
    rw [div_le_iff₀ hΔr2] at ht; exact ht
  have hQ : (a1*b2-b1*a2)^2 * (t.1^4 + t.2^4) = (a1*V - b1*U)^2 + (a2*V - b2*U)^2 := by
    rw [hU, hV]; ring
  have hineq : (a1*b2-b1*a2)^2 * (t.1^4 + t.2^4)
      ≤ (a1^2+b1^2+a2^2+b2^2)*(U^2+V^2) := by
    nlinarith [sq_nonneg (a1*U + b1*V), sq_nonneg (a2*U + b2*V), hQ]
  have hnorm : ‖t‖^4 ≤ t.1^4 + t.2^4 := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total |t.1| |t.2| with h | h
    · rw [max_eq_right h]
      have h2n : |t.2|^4 = t.2^4 := by
        rw [← abs_pow]; exact abs_of_nonneg (by positivity)
      nlinarith [h2n, sq_nonneg (t.1^2)]
    · rw [max_eq_left h]
      have h1n : |t.1|^4 = t.1^4 := by
        rw [← abs_pow]; exact abs_of_nonneg (by positivity)
      nlinarith [h1n, sq_nonneg (t.2^2)]
  have hfin : ‖t‖^4 ≤ (a1^2+b1^2+a2^2+b2^2)*R₀ := by
    have h1 : (a1*b2-b1*a2)^2 * ‖t‖^4 ≤ (a1^2+b1^2+a2^2+b2^2)*(U^2+V^2) := by
      have hmono := mul_le_mul_of_nonneg_left hnorm (le_of_lt hΔr2)
      linarith [hmono, hineq]
    have h2 : (a1^2+b1^2+a2^2+b2^2)*(U^2+V^2)
        ≤ (a1^2+b1^2+a2^2+b2^2)*(R₀*(a1*b2-b1*a2)^2) :=
      mul_le_mul_of_nonneg_left ht5 (by positivity)
    have h3 : ‖t‖^4 * (a1*b2-b1*a2)^2
        ≤ ((a1^2+b1^2+a2^2+b2^2)*R₀) * (a1*b2-b1*a2)^2 := by
      nlinarith [h1, h2]
    exact le_of_mul_le_mul_right h3 hΔr2
  have hKnn : 0 ≤ (a1^2+b1^2+a2^2+b2^2)*R₀ := by positivity
  have hb : 0 ≤ Real.sqrt (Real.sqrt ((a1^2+b1^2+a2^2+b2^2)*R₀)) := Real.sqrt_nonneg _
  have h4eq : (Real.sqrt (Real.sqrt ((a1^2+b1^2+a2^2+b2^2)*R₀)))^4
      = (a1^2+b1^2+a2^2+b2^2)*R₀ := by
    rw [show (4:ℕ)=2*2 from by norm_num, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
        Real.sq_sqrt hKnn]
  have habs1 : |t.1| ≤ ‖t‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_left _ _
  have habs2 : |t.2| ≤ ‖t‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_right _ _
  have h1 : |t.1|^4 ≤ (a1^2+b1^2+a2^2+b2^2)*R₀ :=
    le_trans (pow_le_pow_left₀ (abs_nonneg _) habs1 4) hfin
  have h2 : |t.2|^4 ≤ (a1^2+b1^2+a2^2+b2^2)*R₀ :=
    le_trans (pow_le_pow_left₀ (abs_nonneg _) habs2 4) hfin
  have hb1 : |t.1| ≤ Real.sqrt (Real.sqrt ((a1^2+b1^2+a2^2+b2^2)*R₀)) := by
    rw [← pow_le_pow_iff_left₀ (abs_nonneg _) hb (by norm_num : (4:ℕ) ≠ 0), h4eq]; exact h1
  have hb2 : |t.2| ≤ Real.sqrt (Real.sqrt ((a1^2+b1^2+a2^2+b2^2)*R₀)) := by
    rw [← pow_le_pow_iff_left₀ (abs_nonneg _) hb (by norm_num : (4:ℕ) ≠ 0), h4eq]; exact h2
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact le_trans (max_le hb1 hb2) (by linarith)

/-- **`gphase` is coercive when `Δ ≠ 0`**: the sublevel sets of the phase are bounded. -/
private lemma gphase_coercive (z1 z2 : GaussianInt) (hΔ : Delta z1 z2 ≠ 0) (R₀ : ℝ)
    (hR₀ : 0 ≤ R₀) :
    ∀ t : ℝ × ℝ, gphase z1 z2 t ≤ R₀ →
      ‖t‖ ≤ Real.sqrt (Real.sqrt (((z1.re:ℝ)^2+(z1.im:ℝ)^2+(z2.re:ℝ)^2+(z2.im:ℝ)^2)*R₀)) + 1 := by
  intro t ht
  rw [gphase_eq_form] at ht
  have hΔr : (z1.re:ℝ)*(z2.im:ℝ) - (z1.im:ℝ)*(z2.re:ℝ) ≠ 0 := by
    intro h
    apply hΔ
    have h' : ((z1.re*z2.im - z2.re*z1.im : ℤ) : ℝ) = 0 := by push_cast; linarith
    have h'' : z1.re*z2.im - z2.re*z1.im = 0 := by exact_mod_cast h'
    rw [Work.FIArea4.Delta_eq]; exact h''
  exact quartic_coercive (z1.re:ℝ) (z2.re:ℝ) (z1.im:ℝ) (z2.im:ℝ) R₀ hΔr hR₀ t ht

/-- **Regularity and compact support of the §6 phase `Ψ`.**  For `F : ℝ → ℝ` of class `C⁴` with
compact support, and `z₁,z₂ ∈ ℤ[i]` with `Δ(z₁,z₂) = Im(z̄₁z₂) ≠ 0`, the complex phase
`Ψ(t) = F(|t₁²z₂ − t₂²z₁|²/|Δ|²)` is `C³` and of compact support. -/
theorem PsiC_contDiff_hasCompactSupport (F : ℝ → ℝ) (z1 z2 : GaussianInt)
    (hF : ContDiff ℝ 4 F) (hcs : HasCompactSupport F) (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) :
    ContDiff ℝ 3 (Work.FIArea2.PsiC F z1 z2) ∧ HasCompactSupport (Work.FIArea2.PsiC F z1 z2) := by
  constructor
  · -- `C³`: the phase is a polynomial and `F` is `C⁴`; the coercion to `ℂ` is smooth.
    unfold PsiC phiOf
    have h2 : ContDiff ℝ 4 (fun t : ℝ×ℝ => (((t.1 ^ 2 * (z2.re : ℝ) - t.2 ^ 2 * (z1.re : ℝ)) ^ 2
        + (t.1 ^ 2 * (z2.im : ℝ) - t.2 ^ 2 * (z1.im : ℝ)) ^ 2)
      / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2)) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp ((hF.comp h2).of_le (by norm_num))
  · -- Compact support: extract a ball outside which `F` vanishes, then use coercivity of `gphase`.
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact]
    have hev : F =ᶠ[Filter.coclosedCompact ℝ] 0 := hasCompactSupport_iff_eventuallyEq.mp hcs
    rw [Filter.coclosedCompact_eq_cocompact] at hev
    have hm : {x : ℝ | F x = 0} ∈ Filter.cocompact ℝ := hev
    rw [Metric.mem_cocompact_iff_closedBall_compl_subset (0:ℝ)] at hm
    obtain ⟨r, hr⟩ := hm
    set R₀ : ℝ := max r 0 with hR₀def
    have hR₀0 : 0 ≤ R₀ := le_max_right _ _
    have hFzero : ∀ x : ℝ, R₀ < |x| → F x = 0 := by
      intro x hx
      apply hr
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      linarith [le_max_left r 0]
    have hm2 : {t : ℝ × ℝ | PsiC F z1 z2 t = 0} ∈ Filter.cocompact (ℝ × ℝ) := by
      rw [Metric.mem_cocompact_iff_closedBall_compl_subset (0:ℝ×ℝ)]
      refine ⟨Real.sqrt (Real.sqrt (((z1.re:ℝ)^2+(z1.im:ℝ)^2+(z2.re:ℝ)^2+(z2.im:ℝ)^2)*R₀)) + 1, ?_⟩
      intro t ht
      have ht' : Real.sqrt (Real.sqrt (((z1.re:ℝ)^2+(z1.im:ℝ)^2+(z2.re:ℝ)^2+(z2.im:ℝ)^2)*R₀)) + 1
          < ‖t‖ := by
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at ht
        exact not_le.mp ht
      have hg : R₀ < gphase z1 z2 t := by
        by_contra hcon
        push Not at hcon
        have := gphase_coercive z1 z2 hΔ R₀ hR₀0 t hcon
        linarith
      have hgnn : 0 ≤ gphase z1 z2 t := by rw [gphase]; positivity
      have hFz : F (gphase z1 z2 t) = 0 := hFzero _ (by rw [abs_of_nonneg hgnn]; exact hg)
      simp only [Set.mem_ofPred_eq, PsiC]
      rw [phiOf_eq_gphase F z1 z2 t, hFz]
      simp
    exact hm2

end Work.FIArea2
