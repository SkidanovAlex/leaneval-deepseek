import Mathlib
import Submission.Work.LinnikAreas.vonMangoldtTsum_eq_neg_zeta_logDeriv_re
import Submission.Work.LinnikAreas.re_logDeriv_LFunction_le_vonMangoldtTsum
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound

namespace Work.LinnikAreas

open scoped BigOperators

/-!
# Upper bound for `Re (Λ′/Λ)` on the real segment `(1, 5/4]`

For every non-principal Dirichlet character `χ` modulo `N` and every real `σ ∈ (1, 5/4]`,

`Re (Λ′/Λ)(σ, χ) ≤ 1/(σ − 1) + C`

with an absolute constant `C`, where `Λ(·, χ) = completedLFunction χ` is the completed
`L`-function (with the archimedean gamma factor of
`DirichletCharacter.gammaFactor`, which carries no `N`-dependence).

The proof splits `Λ′/Λ = L′/L + (gammaFactor)′/gammaFactor` on `Re s > 1` (where
`L(σ,χ) ≠ 0`), and bounds the two pieces separately:

* `Re (L′/L)(σ, χ) ≤ ∑ Λ(n) n^{-σ} = Re(−ζ′/ζ)(σ) ≤ 1/(σ−1) + O(1)`, because
  `L′/L` is the negative of the twisted von Mangoldt series and `|χ(n)| ≤ 1`; the resulting
  von Mangoldt series is that of `−ζ′/ζ`, for which the right-of-one bound holds;
* `Re ((gammaFactor)′/gammaFactor)(σ, χ) = O(1)`, since on `(1, 5/4]` the argument of the
  `Γ`-factor stays in the compact set `[1/2, 16]`, where the digamma bound applies.
-/

/-- The real part of the logarithmic derivative of the Archimedean gamma factor is bounded
on the real segment `(1, 5/4]`, uniformly in the character (the gamma factor only depends on
the parity of `χ`). -/
private lemma logDeriv_gammaFactor_re_le : ∃ C : ℝ, ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (σ : ℝ), 1 < σ → σ ≤ 5 / 4 →
    (logDeriv (DirichletCharacter.gammaFactor χ) (σ : ℂ)).re ≤ C := by
  refine ⟨Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log 2 + 8) + 1, ?_⟩
  intro N _ χ σ hσ hσ5
  have key : ∀ x : ℝ, (1 : ℝ) / 2 ≤ x → x ≤ 16 →
      ‖logDeriv Complex.Gammaℝ (x : ℂ)‖ ≤
        Real.log Real.pi / 2 + (1 / 2 : ℝ) * (Real.log 2 + 8) := by
    intro x hx1 hx2
    have h := Commons.NumberTheory.DirichletCharacter.norm_logDeriv_Gammaℝ_le x 0 hx1 hx2
    have h0 : |(0 : ℝ)| = 0 := abs_zero
    rw [h0, show (2 : ℝ) + 0 = 2 by norm_num] at h
    rw [show ((x : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) = (x : ℂ) by simp] at h
    exact h
  rcases χ.even_or_odd with hE | hO
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ :=
      funext fun z => hE.gammaFactor_def z
    rw [hfun]
    exact le_trans (Complex.re_le_norm _)
      (le_trans (key σ (by linarith) (by linarith)) (by linarith))
  · have hfun : DirichletCharacter.gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) :=
      funext fun z => hO.gammaFactor_def z
    rw [hfun]
    have hldcomp : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) (σ : ℂ) =
        logDeriv Complex.Gammaℝ ((σ : ℂ) + 1) := by
      have hs1 : 0 < ((σ : ℂ) + 1).re := by
        rw [Complex.add_re]
        simp
        linarith
      have hf :=
        Commons.NumberTheory.DirichletCharacter.differentiableAt_Gammaℝ ((σ : ℂ) + 1) hs1
      have hg : DifferentiableAt ℂ (fun z : ℂ => z + 1) (σ : ℂ) := by fun_prop
      have h := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => z + 1)
        (x := (σ : ℂ)) hf hg
      have hder : deriv (fun z : ℂ => z + 1) (σ : ℂ) = 1 := by simp
      rw [hder] at h
      simpa [Function.comp_def, mul_comm] using h
    rw [hldcomp]
    have hcast : (((σ + 1 : ℝ)) : ℂ) = (σ : ℂ) + 1 := by push_cast; ring
    rw [← hcast]
    exact le_trans (Complex.re_le_norm _)
      (le_trans (key (σ + 1) (by linarith) (by linarith)) (by linarith))

/-- **Upper bound for the logarithmic derivative of the completed `L`-function on the real
segment `(1, 5/4]`**, uniformly in the modulus and in the non-principal character. -/
theorem siegelZeroSimple_ldUpper : ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ ≠ 1 → ∀ σ : ℝ, 1 < σ → σ ≤ 5 / 4 →
    (logDeriv (DirichletCharacter.completedLFunction χ) (σ : ℂ)).re ≤ 1 / (σ - 1) + C := by
  obtain ⟨Cz, _hCzpos, hz⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
  obtain ⟨Cg, hg⟩ := logDeriv_gammaFactor_re_le
  refine ⟨Cz + Cg, ?_⟩
  intro N _ χ hχ σ hσ1 hσ2
  have hσre : (0 : ℝ) < (σ : ℂ).re := by rw [Complex.ofReal_re]; linarith
  have h1lt : (1 : ℝ) < (σ : ℂ).re := by rw [Complex.ofReal_re]; exact hσ1
  have hL0 : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ h1lt]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ h1lt
  have hsplit := Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_eq_add
    χ hχ (σ : ℂ) hσre hL0
  have hcre : (logDeriv (DirichletCharacter.completedLFunction χ) (σ : ℂ)).re
      = (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re
        + (logDeriv (DirichletCharacter.gammaFactor χ) (σ : ℂ)).re := by
    rw [hsplit, Complex.add_re]
  rw [hcre]
  have hmain : (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re ≤ 1 / (σ - 1) + Cz := by
    refine le_trans (re_logDeriv_LFunction_le_vonMangoldtTsum χ hσ1) ?_
    rw [vonMangoldtTsum_eq_neg_zeta_logDeriv_re σ hσ1]
    exact hz σ hσ1 (by linarith)
  have hgam := hg N χ σ hσ1 hσ2
  linarith

end Work.LinnikAreas
