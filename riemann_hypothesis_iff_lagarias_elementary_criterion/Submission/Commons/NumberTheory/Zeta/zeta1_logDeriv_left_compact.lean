import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open Complex Filter Metric Set
open scoped Real Topology

namespace Commons.NumberTheory.Zeta

/-- Under the Riemann hypothesis the logarithmic derivative of the entire function `ζ₁` is bounded
on the compact rectangle `1/4 ≤ Re s ≤ 3/8`, `|Im s| ≤ 2`.

Indeed, on that rectangle `ζ` has no zeros: they are neither trivial zeros (their real part is
`≤ -2`) nor, by the Riemann hypothesis, nontrivial zeros off the critical line `Re s = 1/2`.
Since `ζ₁ = (s-1)·ζ` there, `ζ₁` is zero-free on the compact set, so `logDeriv ζ₁ = ζ₁'/ζ₁`
is continuous there and hence bounded. -/
theorem zeta1_logDeriv_left_compact (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ (3 / 8 : ℝ) → |s.im| ≤ 2 →
      ‖logDeriv riemannZeta₁ s‖ ≤ C := by
  let K : Set ℂ := {s : ℂ | (1 / 4 : ℝ) ≤ s.re ∧ s.re ≤ (3 / 8 : ℝ) ∧ |s.im| ≤ 2}
  -- `K` is a compact rectangle.
  have hKcompact : IsCompact K := by
    have himg : K = (fun p : ℝ × ℝ => ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))) ''
        (Set.Icc (1 / 4 : ℝ) (3 / 8) ×ˢ Set.Icc (-2 : ℝ) 2) := by
      ext s
      constructor
      · rintro ⟨h1, h2, h3⟩
        rw [abs_le] at h3
        exact ⟨(s.re, s.im), ⟨⟨h1, h2⟩, h3⟩, by
          apply Complex.ext <;> simp⟩
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
        have hre : (((p.1 : ℂ) + Complex.I * (p.2 : ℂ))).re = p.1 := by simp
        have him : (((p.1 : ℂ) + Complex.I * (p.2 : ℂ))).im = p.2 := by simp
        refine ⟨?_, ?_, ?_⟩
        · rw [hre]; exact hp1
        · rw [hre]; exact hp2
        · rw [him, abs_le]; exact ⟨hp3, hp4⟩
    rw [himg]
    exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hKne : K.Nonempty := ⟨(((1 / 4 : ℝ)) : ℂ), by
    refine ⟨by norm_num, by norm_num, by norm_num⟩⟩
  -- `ζ₁` does not vanish on `K`.
  have hne : ∀ s ∈ K, riemannZeta₁ s ≠ 0 := by
    intro s hs hz
    have h1 : (1 / 4 : ℝ) ≤ s.re := hs.1
    have h2 : s.re ≤ (3 / 8 : ℝ) := hs.2.1
    have hs1 : s ≠ 1 := by
      intro hh
      have : s.re = 1 := by rw [hh]; simp
      linarith
    have hzeta : riemannZeta s = 0 := by
      rw [riemannZeta_eq_inv_sub_mul hs1, hz, mul_zero]
    have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      rw [hn] at h1
      have hre : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by norm_num
      rw [hre] at h1
      have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      nlinarith
    have hhalf : s.re = 1 / 2 := h s hzeta htriv hs1
    linarith
  -- `logDeriv ζ₁` is continuous on `K`.
  have hcont : ContinuousOn (fun s : ℂ => ‖logDeriv riemannZeta₁ s‖) K := by
    have hderiv : Continuous (deriv riemannZeta₁) :=
      (differentiable_riemannZeta₁.contDiff (n := ⊤)).continuous_deriv le_top
    have hdiv : ContinuousOn (logDeriv riemannZeta₁) K :=
      hderiv.continuousOn.div differentiable_riemannZeta₁.continuous.continuousOn hne
    exact hdiv.norm
  rcases hKcompact.exists_isMaxOn hKne hcont with ⟨a, _haK, hmax⟩
  refine ⟨‖logDeriv riemannZeta₁ a‖ + 1, by positivity, ?_⟩
  intro s hs1 hs2 hs3
  have hsK : s ∈ K := ⟨hs1, hs2, hs3⟩
  have hle : ‖logDeriv riemannZeta₁ s‖ ≤ ‖logDeriv riemannZeta₁ a‖ := hmax hsK
  linarith

end Commons.NumberTheory.Zeta