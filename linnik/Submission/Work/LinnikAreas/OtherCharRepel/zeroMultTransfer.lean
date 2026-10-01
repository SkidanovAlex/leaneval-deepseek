import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.completedLFunction_analyticOrderAt_ne_top
import Submission.Work.LinnikAreas.OtherCharRepel.LFunction_eq_primitiveCharacter_mul

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex
open scoped Classical

variable {N : ℕ} [NeZero N]

/-- Relation between the completed and the ordinary `L`-function: `completedLFunction` is the
ordinary `L`-function times the archimedean gamma factor.  This is the inversion of Mathlib's
`LFunction_eq_completed_div_gammaFactor`, valid wherever the gamma factor does not vanish. -/
theorem completedLFunction_eq_LFunction_mul_gammaFactor (ψ : DirichletCharacter ℂ N) (s : ℂ)
    (h : s ≠ 0 ∨ N ≠ 1) (hγ : ψ.gammaFactor s ≠ 0) :
    completedLFunction ψ s = LFunction ψ s * ψ.gammaFactor s := by
  rw [LFunction_eq_completed_div_gammaFactor ψ s h, div_mul_cancel₀ _ hγ]

/-- The archimedean gamma factor of a Dirichlet character never vanishes to the right of the
imaginary axis. -/
theorem gammaFactor_ne_zero_of_re_pos (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    ψ.gammaFactor s ≠ 0 := by
  rcases ψ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.one_re]; linarith)

/-- The primitive character inducing a non-trivial character is non-trivial. -/
theorem primitiveCharacter_ne_one (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) :
    ψ.primitiveCharacter ≠ 1 := by
  intro h
  apply hψ
  have hc := changeLevel_primitiveCharacter (χ := ψ)
  rw [h] at hc
  rw [← hc]
  exact (changeLevel_eq_one_iff ψ.conductor_dvd_level).mpr rfl

/-- Transfer facts between a `zeroMult`-zero and the ordinary `L`-function of the level-`q` character, non-vanishing of the divisor of the completed `L`-function of the primitive character, and the converse (a zero of the primitive `L`-function in the critical strip is a `zeroMult`-zero). -/
theorem zeroMultTransfer {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor]
    (hχ : χ ≠ 1) :
    (∀ ρ : ℂ, Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      DirichletCharacter.LFunction χ ρ = 0) ∧
    (∀ (ρ : ℂ) (R : ℝ), Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      ρ ∈ Metric.closedBall (0 : ℂ) R →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0 : ℂ) R)) ρ ≠ 0) ∧
    (∀ u : ℂ, DirichletCharacter.LFunction χ.primitiveCharacter u = 0 → 0 < u.re → u.re < 1 →
      Work.LinnikContract.zeroMult χ u ≠ 0) := by
  have hpc : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one χ hχ
  have hcond : χ.conductor ≠ 1 := (eq_one_iff_conductor_eq_one (χ := χ)).not.mp hχ
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: a `zeroMult`-zero is a zero of the ordinary `L`-function of `χ`.
    intro ρ hρ
    have hzero : completedLFunction χ.primitiveCharacter ρ = 0 := by
      have h := hρ
      rw [Work.LinnikContract.zeroMult] at h
      exact apply_eq_zero_of_analyticOrderNatAt_ne_zero h
    have hL : LFunction χ.primitiveCharacter ρ = 0 := by
      rw [LFunction_eq_completed_div_gammaFactor χ.primitiveCharacter ρ (Or.inr hcond), hzero]
      simp
    rw [LFunction_eq_primitiveCharacter_mul χ hχ ρ, hL, zero_mul]
  · -- Part 2: a `zeroMult`-zero contributes a nonzero divisor of the completed `L`-function.
    intro ρ R hρ hmem
    have hdiff : Differentiable ℂ (completedLFunction χ.primitiveCharacter) :=
      differentiable_completedLFunction hpc
    have han : AnalyticOnNhd ℂ (completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) R) := fun z _ => hdiff.analyticAt z
    have hmer : MeromorphicOn (completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0:ℂ) R) := han.meromorphicOn
    have hAn : AnalyticAt ℂ (completedLFunction χ.primitiveCharacter) ρ := hdiff.analyticAt ρ
    have htop : analyticOrderAt (completedLFunction χ.primitiveCharacter) ρ ≠ ⊤ :=
      completedLFunction_analyticOrderAt_ne_top χ.primitiveCharacter hpc ρ
    rw [MeromorphicOn.divisor_apply hmer hmem, hAn.meromorphicOrderAt_eq,
      ← Nat.cast_analyticOrderNatAt htop, ENat.map_natCast, WithTop.untop₀_coe]
    exact_mod_cast
      (show analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ ≠ 0 from hρ)
  · -- Part 3: a zero of the primitive `L`-function in the critical strip is a `zeroMult`-zero.
    intro u hu hre0 hre1
    have hu0 : u ≠ 0 := by rintro rfl; simp at hre0
    have hval : completedLFunction χ.primitiveCharacter u = 0 := by
      rw [completedLFunction_eq_LFunction_mul_gammaFactor χ.primitiveCharacter u (Or.inl hu0)
        (gammaFactor_ne_zero_of_re_pos χ.primitiveCharacter hre0), hu, zero_mul]
    rw [Work.LinnikContract.zeroMult]
    exact ne_of_gt (ENat.toNat_pos
      (by rw [analyticOrderAt_ne_zero]
          exact ⟨(differentiable_completedLFunction hpc).analyticAt u, hval⟩)
      (completedLFunction_analyticOrderAt_ne_top χ.primitiveCharacter hpc u))

end Work.LinnikAreas.OtherCharRepel
