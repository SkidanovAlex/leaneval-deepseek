import Mathlib

namespace Work.RPB1a.RMT

open Complex Set Metric
open scoped ContDiff Real

/-- The derivative of a holomorphic function is holomorphic: a function differentiable on an
open set is analytic there, and the derivative of an analytic function is analytic. -/
lemma differentiableOn_deriv {U : Set ℂ} (hUo : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) : DifferentiableOn ℂ (deriv g) U :=
  ((hg.analyticOnNhd hUo).deriv_of_isOpen hUo).differentiableOn

/-- The logarithmic derivative `g' / g` of a holomorphic nonvanishing `g` is holomorphic. -/
lemma differentiableOn_logDeriv {U : Set ℂ} (hUo : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (hgn : ∀ z ∈ U, g z ≠ 0) :
    DifferentiableOn ℂ (logDeriv g) U :=
  (differentiableOn_deriv hUo hg).div hg hgn

/-- For holomorphic `L`, the logarithmic derivative of `exp ∘ L` is `L'`. -/
lemma logDeriv_cexp {U : Set ℂ} (hUo : IsOpen U) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L U) :
    EqOn (logDeriv (fun z => Complex.exp (L z))) (deriv L) U := by
  intro z hz
  rw [logDeriv_apply]
  have hLd : DifferentiableAt ℂ L z := hL.differentiableAt (hUo.mem_nhds hz)
  have hd : deriv (fun z => Complex.exp (L z)) z = Complex.exp (L z) * deriv L z := by
    have h := deriv_comp z (Complex.differentiableAt_exp) hLd
    rw [Complex.deriv_exp] at h
    exact h
  rw [hd, mul_div_cancel_left₀ (deriv L z) (Complex.exp_ne_zero (L z))]

/-- From `hprim` (a form of simple connectivity: every holomorphic function on `U` has a primitive)
every holomorphic nonvanishing `g` on a connected open `U` has a holomorphic logarithm and a
holomorphic square root. -/
theorem log_sqrt_of_primitive {U : Set ℂ} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    (hprim : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ EqOn (deriv g) f U) :
    (∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → (∀ z ∈ U, g z ≠ 0) →
      ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ EqOn (fun z => Complex.exp (L z)) g U) ∧
    (∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → (∀ z ∈ U, g z ≠ 0) →
      ∃ s : ℂ → ℂ, DifferentiableOn ℂ s U ∧ EqOn (fun z => s z ^ 2) g U) := by
  -- Step 1: construct a holomorphic logarithm.
  have hlog : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → (∀ z ∈ U, g z ≠ 0) →
      ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ EqOn (fun z => Complex.exp (L z)) g U := by
    intro g hg hgn
    -- `g' / g` is holomorphic on `U`, so `hprim` supplies a primitive `L` of it.
    obtain ⟨L, hLd, hLderiv⟩ := hprim (logDeriv g) (differentiableOn_logDeriv hUo hg hgn)
    -- `logDeriv (exp ∘ L) = deriv L = logDeriv g` on `U`.
    have hkey : EqOn (logDeriv (fun z => Complex.exp (L z))) (logDeriv g) U :=
      fun z hz => by rw [logDeriv_cexp hUo hLd hz, hLderiv hz]
    -- Hence `exp ∘ L` is a nonzero constant multiple of `g` on `U`.
    have hfe : DifferentiableOn ℂ (fun z => Complex.exp (L z)) U := hLd.cexp
    have hfne : ∀ z ∈ U, Complex.exp (L z) ≠ 0 := fun z _ => Complex.exp_ne_zero _
    obtain ⟨c, hc0, hc⟩ := (logDeriv_eqOn_iff hfe hg hUo hUpc hgn hfne).mp hkey
    -- Adjust `L` by a constant to make the ratio exactly `1`.
    refine ⟨fun z => L z - Complex.log c, hLd.sub_const _, ?_⟩
    intro z hz
    change Complex.exp (L z - Complex.log c) = g z
    have hcz : Complex.exp (L z) = c * g z := by simpa [smul_eq_mul] using hc hz
    rw [Complex.exp_sub, Complex.exp_log hc0, hcz, mul_div_cancel_left₀ (g z) hc0]
  refine ⟨hlog, ?_⟩
  -- Step 2: take the square root as `exp (L / 2)`.
  intro g hg hgn
  obtain ⟨L, hLd, hLeq⟩ := hlog g hg hgn
  refine ⟨fun z => Complex.exp (L z / 2), (hLd.div_const 2).cexp, ?_⟩
  intro z hz
  change Complex.exp (L z / 2) ^ 2 = g z
  have h2 : Complex.exp (L z / 2) ^ 2 = Complex.exp (L z) := by
    rw [← Complex.exp_nat_mul (L z / 2) 2]
    congr 1
    ring
  rw [h2]
  simpa using hLeq hz

end Work.RPB1a.RMT
