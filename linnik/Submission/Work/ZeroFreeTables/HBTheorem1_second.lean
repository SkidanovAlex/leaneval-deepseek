/-
# `Work.ZeroFreeTables.HBTheorem1_second`

**Heath-Brown (1992), Theorem 1 (p. 3), real–real case**: for `q` large, a real
character `χ₁` mod `q` with a *real* zero `ρ₁` of `λ₁ = lamOf q ρ₁ < 0.348` which
realises the minimum of `λ` over the strip `|Im| ≤ 10` (`IsMin1WideAt 10 χ₁ ρ₁`)
has `ρ₁` a **simple** zero, and every other zero of the working region (`IsZ`, i.e.
`|Im| ≤ 1`, non-principal character, non-zero multiplicity) has `λ ≥ 0.348`.

The three ingredients are the `µ⁰ = 0` case of HB's §6 `F`-method, HB Lemma 8.2, and
the §6 positivity for a second zero, in each case under the *minimality of `λ₁` only*
(the minimality of the second zero is never assumed):

* **HB Lemma 8.2** (`Work.ZeroFreeTables.Table4.HB82`, proved from the §6 `µ⁰ = 0`
  inequality with `φ = 1/4` and HB Lemma 7.2's test function): for a real `χ₁` and a
  real `ρ₁`,
  `ρ₁` repeated `⟹ λ₁ ≥ 2.293`, and `λ₀ ≥ 2.293` for the real second zero of `χ₁`
  of minimal `λ`.  Since `0.348 < 2.293`, the repeated case is excluded — that *is*
  the simplicity of `ρ₁` — and any real second zero of `χ₁` is ruled out the same way.

* **The second zero of `χ₁`** is first replaced, by minimisation over the working
  region (`Work.LinnikAreas.boxMaxZeroH`), by the `λ`-minimal one; if that is real it
  is killed by HB Lemma 8.2, and if it is non-real it is killed by
  `Work.ZeroFreeTables.B1Nonreal` (HB §8.1's triangle method, `x = 2`).

* **Zeros of the other characters** are killed by `Work.ZeroFreeTables.B2OtherChar`
  (HB Lemma 6.2 at the convexity constant `φ = 1/2`, evaluated for HB Lemma 7.1's
  test function at `θ = π/4`).

All imported modules are axiom-clean.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Table4.HB82
import Submission.Work.LinnikAreas.boxMaxZeroH
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.ZeroFreeTables.B1Nonreal
import Submission.Work.ZeroFreeTables.B2OtherChar

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

theorem HBTheorem1_second : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      Work.LinnikContract.lamOf q ρ₁ < (348 : ℝ) / 1000 →
      Work.LinnikContract.zeroMult χ₁ ρ₁ = 1 ∧
        ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.IsZ χ ρ →
          (χ ≠ χ₁ ∨ ρ ≠ ρ₁) →
          (348 : ℝ) / 1000 ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨qA, hA⟩ := Work.ZeroFreeTables.Table4.HB82
  obtain ⟨qN, hN⟩ := Work.ZeroFreeTables.B1Nonreal
  obtain ⟨qB, hB⟩ := Work.ZeroFreeTables.B2OtherChar
  refine ⟨max (max qA (max qN qB)) 2, ?_⟩
  intro q hq _inst χ₁ ρ₁ hm hsq him hlt
  have hqA : qA ≤ q := by omega
  have hqN : qN ≤ q := by omega
  have hqB : qB ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hZ1 : Work.LinnikContract.IsZ χ₁ ρ₁ := hm.1.1
  have hχ1ne : χ₁ ≠ 1 := hZ1.1
  have hzm1 : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hZ1.2.1
  obtain ⟨hβpos, hβlt1, hlampos⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos (q := q) hq2 hχ1ne hzm1
  have hmspec := hA q hqA χ₁ ρ₁ hm hsq hχ1ne him hZ1
  have hcast : (((ρ₁.re : ℝ)) : ℂ) = ρ₁ := Complex.ext (by simp) (by simp [him])
  have hsimple : Work.LinnikContract.zeroMult χ₁ ρ₁ = 1 := by
    by_contra hcon
    have h2 : 2 ≤ Work.LinnikContract.zeroMult χ₁ ρ₁ := by omega
    have h2293 := hmspec.1 h2
    linarith
  refine ⟨hsimple, ?_⟩
  intro χ ρ hZ hne
  by_contra hcon
  push_neg at hcon
  have hχ1inv : χ₁⁻¹ = χ₁ := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq)
  by_cases hχeq : χ = χ₁
  · have hρne : ρ ≠ ρ₁ := by
      rcases hne with h | h
      · exact absurd hχeq h
      · exact h
    have hZ' : Work.LinnikContract.IsZ χ₁ ρ := by rw [hχeq] at hZ; exact hZ
    obtain ⟨ρ₂, hzm₂, him₂, hne₂, hle₂, hmin₂⟩ :=
      Work.LinnikAreas.boxMaxZeroH hq2 χ₁ ρ₁ ρ (H := 1) (by norm_num) hZ'.2.1 hZ'.2.2 hρne
    have hZ₂ : Work.LinnikContract.IsZ χ₁ ρ₂ := ⟨hχ1ne, hzm₂, him₂⟩
    have hlt₂ : Work.LinnikContract.lamOf q ρ₂ < (348 : ℝ) / 1000 := lt_of_le_of_lt hle₂ hcon
    by_cases h₂ : ρ₂.im = 0
    · have hmin' : ∀ ρ' : ℂ, Work.LinnikContract.IsZ χ₁ ρ' → ρ' ≠ ρ₁ →
          Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ' := by
        intro ρ' hZ' hne'
        exact hmin₂ ρ' hZ'.2.1 hZ'.2.2 hne'
      have h2293 := hmspec.2 ρ₂ hZ₂ hne₂ h₂ hmin'
      linarith
    · exact hN q hqN χ₁ ρ₁ ρ₂ hm hsq him hsimple hlt hZ₂ hne₂ h₂ hlt₂
  · exact hB q hqB χ₁ χ ρ₁ ρ hm hsq him hlt hZ (by simpa [hχ1inv] using hχeq) hcon

end Work.ZeroFreeTables
