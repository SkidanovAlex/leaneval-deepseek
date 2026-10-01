import Mathlib
import Submission.Work.LinnikAreas.triPerronDefs
import Submission.Work.LinnikAreas.LoneLowerDefs

/-!
# The residue decomposition of the Perron integrand `triFun`

Writing `F(s) = triFun ψ β x s = ζ(s+β) L(s+β,ψ) x^s/(s(s+1))`, the formula

`ζ(t) = (t-1)⁻¹ ζ₁(t)` and `L(s+β,ψ) = s · dslope(L(ψ,·+β), 0, s)` (valid because `L(ψ,β) = 0`)
exhibit `F` as `M(s)/(s-(1-β))`, where `M = triPerronM ψ β x` is holomorphic at `s = 1-β`.
Since `(s-(1-β)) · dslope M (1-β) s = M s - M(1-β)`, this gives

`F s = M(1-β)/(s-(1-β)) + dslope M (1-β) s`,

and `M(1-β) = ζ₁(1) · dslope(L,0,1-β) · x^{1-β}/(2-β) = L(ψ,1) x^{1-β}/((1-β)(2-β)) = triPerronRes ψ β x`.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped BigOperators

set_option linter.unusedVariables false

theorem triFun_residue_decomp {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    {β x : ℝ} (hβ1 : β < 1) (hx : 0 < x) (hL0 : DirichletCharacter.LFunction ψ (β : ℂ) = 0)
    {s : ℂ} (hs0 : s ≠ 0) (hsu : s ≠ triPerronU β) (hsm1 : s + 1 ≠ 0) :
    triFun ψ β x s
      = triPerronRes ψ β x / (s - triPerronU β)
        + dslope (triPerronM ψ β x) (triPerronU β) s := by
  -- the pole is at `1 - β`
  have huβ : triPerronU β + (β : ℂ) = 1 := by
    simp only [triPerronU]; push_cast; ring
  have hu0 : triPerronU β ≠ 0 := by
    intro h
    have hre : (1 - β : ℝ) = 0 := by simpa using congrArg Complex.re h
    linarith
  -- Step 1: `F s = M s / (s - (1-β))`
  have hF : triFun ψ β x s = triPerronM ψ β x s / (s - triPerronU β) := by
    have hsu1 : s + (β : ℂ) ≠ 1 := by
      intro h
      apply hsu
      rw [triPerronU]
      push_cast
      linear_combination h
    have hzeta : riemannZeta (s + (β : ℂ)) = (s - triPerronU β)⁻¹ * riemannZeta₁ (s + (β : ℂ)) := by
      rw [riemannZeta_eq_inv_sub_mul hsu1]
      congr 2
      simp only [triPerronU]
      push_cast
      ring
    have hLz : DirichletCharacter.LFunction ψ (s + (β : ℂ))
        = s * dslope (fun t : ℂ => DirichletCharacter.LFunction ψ (t + (β : ℂ))) 0 s := by
      have h := sub_smul_dslope_of_zero
        (f := fun t : ℂ => DirichletCharacter.LFunction ψ (t + (β : ℂ))) (a := 0) ?_ s
      · simpa using h.symm
      · simpa using hL0
    rw [triFun, zlFun, hzeta, hLz, triPerronM]
    field_simp
  -- Step 2: the `dslope` identity at the pole
  have hM : triPerronM ψ β x s
      = triPerronM ψ β x (triPerronU β)
        + (s - triPerronU β) * dslope (triPerronM ψ β x) (triPerronU β) s := by
    have h := sub_smul_dslope (triPerronM ψ β x) (triPerronU β) s
    rw [smul_eq_mul] at h
    rw [h]
    ring
  -- Step 3: `M (1-β) = triPerronRes`
  have hMu : triPerronM ψ β x (triPerronU β) = triPerronRes ψ β x := by
    have hLval : DirichletCharacter.LFunction ψ (triPerronU β + (β : ℂ))
        = DirichletCharacter.LFunction ψ 1 := by rw [huβ]
    have hLz0 : DirichletCharacter.LFunction ψ (0 + (β : ℂ)) = 0 := by simpa using hL0
    have hLds : dslope (fun t : ℂ => DirichletCharacter.LFunction ψ (t + (β : ℂ))) 0 (triPerronU β)
        = DirichletCharacter.LFunction ψ 1 / triPerronU β := by
      rw [dslope_of_ne _ (by simpa using hu0), slope_def_field, hLval, hLz0]
      simp
    have hzeta1 : riemannZeta₁ (triPerronU β + (β : ℂ)) = 1 := by rw [huβ, riemannZeta₁_one]
    rw [triPerronM, triPerronRes, hLds, hzeta1]
    simp only [one_mul, triPerronU]
    push_cast
    field_simp
    ring
  rw [hF, hM, hMu]
  field_simp

end Work.LinnikAreas
