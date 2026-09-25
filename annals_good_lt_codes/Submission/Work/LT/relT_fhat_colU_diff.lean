import Mathlib
import Submission.Work.LT.relT_defs
import Submission.Work.LT.chi_basic
import Submission.Work.LT.relT_sl3E_basic

namespace Work.LT

/-! **The `χ_z`-component of the difference `g ↦ f(u(st)·g) − f(g)`.**

For `u(st) = colU p a b c st` in the column subgroup `U` and the eigenrelation
`fhat p a b c z f (u(st)·g) = χ_z(st) · fhat p a b c z f g`, the Fourier coefficient along `U` is
linear in the function, and translating the function by `u(st)` is the same as translating its
argument (because `U` is abelian, `relT_sl3E_basic`). Hence

`fhat_z (f ∘ L_{u(st)} − f) = (χ_z(st) − 1) · fhat_z f`. -/

/-- The column subgroup is closed under multiplication: `u(st)·u(st') = u(st + st')`. -/
lemma relT_fhat_colU_diff_mul {p : ℕ} (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (st st' : ZMod p × ZMod p) :
    colU p a b c st * colU p a b c st' = colU p a b c (st + st') := by
  obtain ⟨-, -, -, -, hprod⟩ := relT_sl3E_basic
  exact hprod p hab hac hbc st.1 st'.1 st.2 st'.2

/-- The column subgroup is abelian. -/
lemma relT_fhat_colU_diff_comm {p : ℕ} (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (st st' : ZMod p × ZMod p) :
    colU p a b c st * colU p a b c st' = colU p a b c st' * colU p a b c st := by
  rw [relT_fhat_colU_diff_mul a b c hab hac hbc st st',
      relT_fhat_colU_diff_mul a b c hab hac hbc st' st]
  congr 1
  exact Prod.ext (add_comm _ _) (add_comm _ _)

/-- `fhat` is additive in its function argument (differences). -/
lemma relT_fhat_colU_diff_sub {p : ℕ} [NeZero p] (a b c : Fin 3) (z : ZMod p × ZMod p)
    (h₁ h₂ : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ) :
    fhat p a b c z (h₁ - h₂) = fhat p a b c z h₁ - fhat p a b c z h₂ := by
  funext g
  simp only [fhat, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_div]

/-- Translating the function by `u(st)` and translating the argument by `u(st)` give the same
Fourier coefficient along `U`. -/
lemma relT_fhat_colU_diff_translate {p : ℕ} [NeZero p] (a b c : Fin 3) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
    (z st : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) :
    fhat p a b c z (fun x => f (colU p a b c st * x)) g
      = fhat p a b c z f (colU p a b c st * g) := by
  simp only [fhat]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [← mul_assoc, relT_fhat_colU_diff_comm a b c hab hac hbc st x, mul_assoc]

theorem relT_fhat_colU_diff :
    ∀ (p : ℕ) [NeZero p] {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c →
      ∀ f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ,
        (∀ (st z : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
            fhat p a b c z f (colU p a b c st * g) = chi p z st * fhat p a b c z f g) →
        ∀ (st z : ZMod p × ZMod p) (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
          fhat p a b c z (fun g' => f (colU p a b c st * g') - f g') g
            = (chi p z st - 1) * fhat p a b c z f g := by
  intro p hp a b c hab hac hbc f hf st z g
  -- linearity of `fhat` in the function, then the eigenrelation
  have hlin : fhat p a b c z (fun g' => f (colU p a b c st * g') - f g') g
      = fhat p a b c z (fun g' => f (colU p a b c st * g')) g - fhat p a b c z f g := by
    simp only [fhat, mul_sub, Finset.sum_sub_distrib, sub_div]
  rw [hlin, relT_fhat_colU_diff_translate a b c hab hac hbc f z st g, hf st z g]
  ring

end Work.LT
