import Mathlib
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.DhRepel

/-- A zero `u` of the primitive `L`-function of a non-principal character `χ` at level `q` which
sits in the "ball" `|Im u| ≤ |Im ρ₂| + 1` has real part at most `Re ρ₂`, provided `(χ,u)` is not
the exceptional pair `(χ₀,ρ₀)`: outside the critical strip the assertion is trivial because
`Re ρ₂ > 0` (zeros of non-principal Dirichlet `L`-functions with `|Im| ≤ 1` lie in the open
strip), while inside the strip `u` is a `zeroMult`-zero of `χ` and the ball hypothesis applies. -/
private lemma re_le_of_LFunction_eq_zero {q : ℕ} [NeZero q] (χ₀ χ₂ : DirichletCharacter ℂ q)
    (ρ₀ ρ₂ : ℂ) (hq : 2 ≤ q) (hχ₂ : χ₂ ≠ 1)
    (hzm₂ : Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0)
    (hball : ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 →
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ |ρ₂.im| + 1 → (ψ, u) ≠ (χ₀, ρ₀) →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u)
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1) {u : ℂ}
    (hne : (χ, u) ≠ (χ₀, ρ₀))
    (hzero : DirichletCharacter.LFunction χ.primitiveCharacter u = 0)
    (him : |u.im| ≤ |ρ₂.im| + 1) : u.re ≤ ρ₂.re := by
  have hρ₂ : 0 < ρ₂.re := (Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq hχ₂ hzm₂).1
  rcases lt_or_ge (0 : ℝ) u.re with hre | hre
  · -- `u` lies in the open right half-plane: it is a `zeroMult`-zero and the ball applies
    have hu0 : u ≠ 0 := by rintro rfl; simp at hre
    have hγ : χ.primitiveCharacter.gammaFactor u ≠ 0 :=
      Work.LinnikAreas.OtherCharRepel.gammaFactor_ne_zero_of_re_pos _ hre
    have hcomp : DirichletCharacter.completedLFunction χ.primitiveCharacter u = 0 := by
      rw [Work.LinnikAreas.OtherCharRepel.completedLFunction_eq_LFunction_mul_gammaFactor
        χ.primitiveCharacter u (Or.inl hu0) hγ, hzero, zero_mul]
    have hstrip : u.re < 1 :=
      (Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter
        (Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ hχ)
        (DirichletCharacter.primitiveCharacter_isPrimitive χ) hcomp).2
    have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 :=
      (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ hχ).2.2 u hzero hre hstrip
    have h := hball χ u hχ hzm him hne
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at h
    have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
    nlinarith [h, hlog]
  · -- `u` is not in the right half-plane, while `ρ₂` is
    exact le_trans hre hρ₂.le

theorem maximalityFromBall {q : ℕ} [NeZero q] (χ₀ χ₂ : DirichletCharacter ℂ q)
    [NeZero χ₀.conductor] [NeZero χ₂.conductor]
    [NeZero (χ₀ * χ₂).conductor] [NeZero (χ₀ * χ₂⁻¹).conductor] (ρ₀ ρ₂ : ℂ)
    (hq : 2 ≤ q) (hχ₀ : χ₀ ≠ 1) (hχ₂ : χ₂ ≠ 1) (hχ₂χ₀ : χ₂ ≠ χ₀) (hsq : χ₀ ^ 2 = 1)
    (hρ₀im : ρ₀.im = 0) (hzm₀ : Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0)
    (hzm₂ : Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0)
    (him₂ : |ρ₂.im| ≤ 1)
    (hχ₀χ₂ : χ₀ * χ₂ ≠ 1) (hχ₀χ₂' : χ₀ * χ₂⁻¹ ≠ 1)
    (hball : ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 →
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ |ρ₂.im| + 1 → (ψ, u) ≠ (χ₀, ρ₀) →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) :
    (∀ u : ℂ, DirichletCharacter.LFunction (χ₀ * χ₂).primitiveCharacter u = 0 →
        |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re) ∧
    (∀ u : ℂ, DirichletCharacter.LFunction (χ₀ * χ₂⁻¹).primitiveCharacter u = 0 →
        |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re) ∧
    (∀ u : ℂ, DirichletCharacter.LFunction χ₀.primitiveCharacter u = 0 →
        |u.im| ≤ |ρ₂.im| + 1 → u = ρ₀ ∨ u.re ≤ ρ₂.re) ∧
    (∀ u : ℂ, DirichletCharacter.LFunction χ₂.primitiveCharacter u = 0 →
        |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- zeros of `L(s, χ₀χ₂)`: `χ₀χ₂ ≠ χ₀`, so the ball hypothesis always applies
    intro u hzero him
    refine re_le_of_LFunction_eq_zero χ₀ χ₂ ρ₀ ρ₂ hq hχ₂ hzm₂ hball (χ₀ * χ₂) hχ₀χ₂ ?_ hzero him
    intro h
    have h1 : χ₀ * χ₂ = χ₀ * 1 := by
      rw [mul_one]; exact congrArg Prod.fst h
    exact hχ₂ (mul_left_cancel h1)
  · -- zeros of `L(s, χ₀χ₂⁻¹)`: again `χ₀χ₂⁻¹ ≠ χ₀` since `χ₂ ≠ 1`
    intro u hzero him
    refine re_le_of_LFunction_eq_zero χ₀ χ₂ ρ₀ ρ₂ hq hχ₂ hzm₂ hball (χ₀ * χ₂⁻¹) hχ₀χ₂' ?_ hzero him
    intro h
    have h1 : χ₀ * χ₂⁻¹ = χ₀ * 1 := by
      rw [mul_one]; exact congrArg Prod.fst h
    exact hχ₂ (inv_eq_one.mp (mul_left_cancel h1))
  · -- zeros of `L(s, χ₀)`: the pair `(χ₀, ρ₀)` is the single permitted exception
    intro u hzero him
    by_cases h : (χ₀, u) = (χ₀, ρ₀)
    · exact Or.inl (congrArg Prod.snd h)
    · exact Or.inr
        (re_le_of_LFunction_eq_zero χ₀ χ₂ ρ₀ ρ₂ hq hχ₂ hzm₂ hball χ₀ hχ₀ h hzero him)
  · -- zeros of `L(s, χ₂)`: `χ₂ ≠ χ₀`, so the ball hypothesis always applies
    intro u hzero him
    refine re_le_of_LFunction_eq_zero χ₀ χ₂ ρ₀ ρ₂ hq hχ₂ hzm₂ hball χ₂ hχ₂ ?_ hzero him
    intro h
    exact hχ₂χ₀ (congrArg Prod.fst h)

end Work.LinnikAreas.DhRepel
