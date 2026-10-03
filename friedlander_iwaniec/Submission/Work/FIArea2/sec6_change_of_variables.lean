import Mathlib
import Submission.Work.FIArea2.Sec6Defs
import Submission.Work.FIArea2.integral_comp_diag_scaling
import Submission.Work.FIArea2.phiOf_comp_secScale

namespace Work.FIArea2

open scoped BigOperators

/-- The change of variables of the §6 Poisson step (**with the direction corrected** as the two
referees of this statement indicated).  With the two scalings `s₁ = √(|Δ|/|z₂|)`,
`s₂ = √(|Δ|/|z₁|)` (`Work.FIArea2.secScale₁/₂`), the lattice phase
`φ(t) = f(|t₁²z₂ − t₂²z₁|²/|Δ|²)` (`Work.FIArea2.phiOf`) satisfies
`φ(s₁τ₁, s₂τ₂) = f(g(τ))` with `g(τ) = τ₁⁴ − 2γτ₁²τ₂² + τ₂⁴` (`Work.FIArea2.gQuartic`),
`γ = Re(z̄₁z₂)/|z₁z₂|` (`Work.FIArea2.gamOf`); since `φ(t) = ψ(t₁/s₁, t₂/s₂)` with `ψ = f∘g`, the
Fourier transform (`𝓕ψ(u) = ∫_{ℝ²}ψ(t)e(−u·t)dt`, `Work.FIArea2.ft2real`) satisfies

  `𝓕φ(u₁,u₂) = s₁s₂·𝓕(f∘g)(s₁u₁, s₂u₂)`.

With `u_j = h_j/|Δ|` this is the identity that feeds (6.9): the right-hand side is
`s₁s₂·F(−s₁h₁/|Δ|, −s₂h₂/|Δ|) = s₁s₂·F(−h₁|Δz₂|^{−1/2}, −h₂|Δz₁|^{−1/2})` for the paper's `F` of
(6.8) (`Work.FIArea2.Fint_eq_ft2real`), and `s₁s₂ = |Δ|/|z₁z₂|^{1/2}` supplies exactly the factor
`|z₁z₂|^{−1/2}` of (6.9).

Route: the pointwise identity `φ(s₁τ₁,s₂τ₂) = f(g(τ))` is pure algebra (expand
`|t₁²z₂−t₂²z₁|²` through the real and imaginary parts, use `s₁² = |Δ|/|z₂|`, `s₂² = |Δ|/|z₁|`,
`Real.sq_sqrt`, and `γ = Re(z̄₁z₂)/(|z₁||z₂|)`); the Fourier identity is the diagonal linear
substitution `t_j = s_jτ_j` (Jacobian `s₁s₂`), via `MeasureTheory.integral_comp_mul_left` in each
variable or `MeasureTheory.Measure.map_smul`. -/
theorem sec6_change_of_variables (f : ℝ → ℝ) (z1 z2 : GaussianInt)
    (hd : Work.FIPlan.absDelta z1 z2 ≠ 0) (u₁ u₂ : ℝ) :
    Work.FIArea2.ft2real (fun t => ((Work.FIArea2.phiOf f z1 z2 t : ℝ) : ℂ)) u₁ u₂
      = (Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2)
        * Work.FIArea2.ft2real
            (fun t => ((f (Work.FIArea2.gQuartic (Work.FIArea2.gamOf z1 z2) t) : ℝ) : ℂ))
            (Work.FIArea2.secScale₁ z1 z2 * u₁) (Work.FIArea2.secScale₂ z1 z2 * u₂) := by
  -- `|Δ| > 0`, and therefore `z₁ ≠ 0 ≠ z₂`
  have hApos : (0 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  have hz1 : z1 ≠ 0 := by
    intro h
    exact hd (by simp [Work.FIPlan.absDelta, Work.FIPlan.Delta, h])
  have hz2 : z2 ≠ 0 := by
    intro h
    exact hd (by simp [Work.FIPlan.absDelta, Work.FIPlan.Delta, h])
  have hn1pos : (0 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_of_ne_zero hz1
  have hn2pos : (0 : ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast gnorm_pos_of_ne_zero hz2
  -- abbreviate the two scalings, the cosine and the phase `ψ = f ∘ g`
  set S1 : ℝ := secScale₁ z1 z2 with hS1def
  set S2 : ℝ := secScale₂ z1 z2 with hS2def
  set G : ℝ := gamOf z1 z2 with hGdef
  have hs1 : 0 < S1 := by
    rw [hS1def, secScale₁]
    exact Real.sqrt_pos.2 (div_pos hApos (Real.sqrt_pos.2 hn2pos))
  have hs2 : 0 < S2 := by
    rw [hS2def, secScale₂]
    exact Real.sqrt_pos.2 (div_pos hApos (Real.sqrt_pos.2 hn1pos))
  -- the pointwise substitution identity `φ(s₁τ₁, s₂τ₂) = f(g(τ))`
  have hpt : ∀ τ : ℝ × ℝ, phiOf f z1 z2 (S1 * τ.1, S2 * τ.2) = f (gQuartic G τ) := by
    intro τ
    rw [hS1def, hS2def, hGdef]
    exact phiOf_comp_secScale f z1 z2 hd τ
  -- the integrand of the right-hand side
  set Ψ : ℝ × ℝ → ℂ := fun τ => ((f (gQuartic G τ) : ℝ) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I) * ((S1 * u₁) * τ.1 + (S2 * u₂) * τ.2)) with hΨdef
  -- the left-hand integral is `∫ Ψ(t₁/s₁, t₂/s₂)`
  have hL : ft2real (fun t => ((phiOf f z1 z2 t : ℝ) : ℂ)) u₁ u₂
      = ∫ t : ℝ × ℝ, Ψ (t.1 / S1, t.2 / S2) := by
    rw [ft2real]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hΨdef]
    have h2 := hpt (t.1 / S1, t.2 / S2)
    rw [show S1 * (t.1 / S1) = t.1 by field_simp,
        show S2 * (t.2 / S2) = t.2 by field_simp] at h2
    rw [h2]
    have hargC : (↑u₁ * ↑t.1 + ↑u₂ * ↑t.2 : ℂ)
        = ↑S1 * ↑u₁ * ↑(t.1 / S1) + ↑S2 * ↑u₂ * ↑(t.2 / S2) := by
      push_cast
      have h1' : (↑S1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs1)
      have h2' : (↑S2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs2)
      field_simp
    rw [hargC]
  -- the right-hand integral is `∫ Ψ`
  have hR : ft2real (fun t => ((f (gQuartic G t) : ℝ) : ℂ)) (S1 * u₁) (S2 * u₂)
      = ∫ τ : ℝ × ℝ, Ψ τ := by
    rw [ft2real]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [hΨdef]
    congr 1
    congr 1
    push_cast
    ring
  rw [hL, hR]
  exact integral_comp_diag_scaling S1 S2 hs1 hs2 Ψ

end Work.FIArea2
