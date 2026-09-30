import Mathlib
import Submission.Work.BMF.perron_twist_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open MeasureTheory intervalIntegral
open scoped Real Interval Topology

noncomputable section

/-- The twisted principal-character Perron integrand `w ↦ −(ζ′/ζ)(w + iu)·x^w/w`. -/
noncomputable def zetaTwG (u x : ℝ) (w : ℂ) : ℂ :=
  -(deriv riemannZeta (w + (u : ℂ) * Complex.I)) / riemannZeta (w + (u : ℂ) * Complex.I) *
    (x : ℂ) ^ w / w

/-- The twisted truncated Perron integral for the principal character, on the vertical line
`Re w = 1 + 1/log x`. -/
noncomputable def zetaTwPerron (u x T : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ t in (-T)..T,
    zetaTwG u x (((1 + 1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)

/-- The twisted von Mangoldt sum `Σ_{n ≤ x} Λ(n) n^{-iu}`. -/
noncomputable def zetaTwSum (u x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u))

/-- Top, bottom and left edges of the rectangle `[σ₁, 1 + 1/log x] × [-T, T]` applied to the
twisted integrand `zetaTwG u x`, in the normalization used by the rectangle identity
`zetaTwPerron = residue + top − bottom + left`. -/
noncomputable def zetaTwTop (u x T σ₁ : ℝ) : ℂ :=
  (1 / (2 * Real.pi * Complex.I)) *
    ∫ v in σ₁..(1 + 1 / Real.log x), zetaTwG u x ((v : ℂ) + (T : ℂ) * Complex.I)

noncomputable def zetaTwBot (u x T σ₁ : ℝ) : ℂ :=
  (1 / (2 * Real.pi * Complex.I)) *
    ∫ v in σ₁..(1 + 1 / Real.log x), zetaTwG u x ((v : ℂ) - (T : ℂ) * Complex.I)

noncomputable def zetaTwLeft (u x T σ₁ : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ t in (-T)..T, zetaTwG u x ((σ₁ : ℂ) + (t : ℂ) * Complex.I)

lemma chiLambdaTwist_one_eq (u : ℝ) :
    Work.BMF.chiLambdaTwist (1 : DirichletCharacter ℂ 1) u =
      fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * u)) := by
  funext n
  rw [Work.BMF.chiLambdaTwist, MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1))]
  ring

lemma LSeries_chiLambdaTwist_one (u : ℝ) {w : ℂ} (hw : 1 < w.re) :
    LSeries (Work.BMF.chiLambdaTwist (1 : DirichletCharacter ℂ 1) u) w =
      -deriv riemannZeta (w + (u : ℂ) * Complex.I) / riemannZeta (w + (u : ℂ) * Complex.I) := by
  rw [chiLambdaTwist_one_eq u, Work.BMF.LSeries_mul_cpow_neg_I]
  have hre : 1 < (w + (u : ℂ) * Complex.I).re := by simpa using hw
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre

/-- On the half-plane of convergence, the twisted integrand is the twisted `Λ`-series times
`x^w/w`. -/
lemma zetaTwG_eq_LSeries (u x : ℝ) {w : ℂ} (hw : 1 < w.re) :
    zetaTwG u x w = LSeries (Work.BMF.chiLambdaTwist (1 : DirichletCharacter ℂ 1) u) w *
      (x : ℂ) ^ w / w := by
  rw [zetaTwG, LSeries_chiLambdaTwist_one u hw]

/-- **Truncation error for the twisted principal Perron integral**: for `x ≥ 3` not a natural
number and `T ≥ 2`,
`‖zetaTwPerron u x T − Σ_{n ≤ x} Λ(n) n^{-iu}‖ ≤ C (x log²x/T + log x)`.
This is `Work.BMF.perron_twisted_uniform` at `χ = 1`. -/
theorem zetaTwPerron_sub_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ) (x T : ℝ), 3 ≤ x → (∀ n : ℕ, (n : ℝ) ≠ x) → 2 ≤ T →
      ‖zetaTwPerron u x T - zetaTwSum u x‖ ≤ C * (x * (Real.log x) ^ 2 / T + Real.log x) := by
  obtain ⟨C, hC, hper⟩ := Work.BMF.perron_twisted_uniform
  refine ⟨C, hC, ?_⟩
  intro u x T hx hxnat hT
  have hx1 : 1 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  set σ : ℝ := 1 + 1 / Real.log x with hσ
  have hσ1 : 1 < σ := by
    rw [hσ]
    have h : 0 < 1 / Real.log x := by positivity
    linarith
  have hline : (∫ t in (-T)..T,
        LSeries (Work.BMF.chiLambdaTwist (1 : DirichletCharacter ℂ 1) u)
            ((σ : ℂ) + (t : ℂ) * Complex.I) *
          (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I))
      = ∫ t in (-T)..T, zetaTwG u x ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    have hre : 1 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by
      have : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      rw [this]; exact hσ1
    exact (zetaTwG_eq_LSeries u x hre).symm
  have hsum : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        Work.BMF.chiLambdaTwist (1 : DirichletCharacter ℂ 1) u n) = zetaTwSum u x := by
    rw [zetaTwSum, chiLambdaTwist_one_eq u]
  have h := hper (1 : DirichletCharacter ℂ 1) u x T hx hxnat hT
  rw [hline, hsum] at h
  have hσ' : ((σ : ℂ)) = (((1 + 1 / Real.log x : ℝ)) : ℂ) := by rw [hσ]
  rw [hσ'] at h
  simpa only [zetaTwPerron] using h

end

end Work.BMF.liouville
