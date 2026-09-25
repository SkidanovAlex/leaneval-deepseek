import Mathlib
import Submission.Work.LT.relT_defs
import Submission.Work.LT.relT_chi
import Submission.Work.LT.relT_sl3E_basic
import Submission.Work.LT.chi_orth

/-! **Fourier inversion for the `U`-Fourier coefficients `fhat`.**

`fhat p a b c z f g = (p²)⁻¹ ∑_{s,t} conj (χ_z(s,t)) · f (u(s,t)·g)` is the `χ_z`-isotypic
component of `f` along the column subgroup `U = {u(s,t) = E_ac(s)E_bc(t)} ≅ (ℤ/p)²`
(see `relT_defs`).  Summing over all characters `z ∈ (ℤ/p)²` recovers `f g`: swapping the two
sums produces the character-orthogonality sum `∑_z conj (χ_z(s,t)) = p²·[s = t = 0]`
(`chi_orth`), and the only surviving term is `s = t = 0`, where `u(0,0) = 1`
(`relT_sl3E_basic`). -/

namespace Work.LT

theorem relT_fhat_inversion :
    ∀ (p : ℕ) [NeZero p] {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c →
      ∀ (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
        (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)),
        ∑ z : ZMod p × ZMod p, fhat p a b c z f g = f g := by
  intro p _ a b c hab hac hbc f g
  -- `p` is invertible in `ℂ`.
  have hne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  -- Character orthogonality: summing `conj (χ_z st)` over the character index `z` kills `st ≠ 0`.
  have horth : ∀ w : ZMod p × ZMod p,
      ∑ uv : ZMod p × ZMod p, star (chi p uv w)
        = if w = 0 then (p : ℂ) ^ 2 else 0 :=
    fun w => (chi_orth p).2.2.1 w
  -- The column element at `(0,0)` is the identity.
  have hcol0 : colU p a b c (0 : ZMod p × ZMod p) = 1 := by
    simp [colU, relT_sl3E_basic.1]
  -- The double sum collapses onto `st = 0`.
  have hsum : (∑ z : ZMod p × ZMod p, ∑ st : ZMod p × ZMod p,
        star (chi p z st) * f (colU p a b c st * g))
      = (p : ℂ) ^ 2 * f (colU p a b c (0 : ZMod p × ZMod p) * g) := by
    rw [Finset.sum_comm]
    trans ∑ st : ZMod p × ZMod p,
        (∑ z : ZMod p × ZMod p, star (chi p z st)) * f (colU p a b c st * g)
    · exact Finset.sum_congr rfl fun st _ => by rw [Finset.sum_mul]
    · rw [Finset.sum_congr rfl (fun st _ => by rw [horth st])]
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq']
      simp
  calc ∑ z : ZMod p × ZMod p, fhat p a b c z f g
      = (∑ z : ZMod p × ZMod p, ∑ st : ZMod p × ZMod p,
            star (chi p z st) * f (colU p a b c st * g)) / (p : ℂ) ^ 2 := by
        simp only [fhat, Finset.sum_div]
    _ = ((p : ℂ) ^ 2 * f (colU p a b c (0 : ZMod p × ZMod p) * g)) / (p : ℂ) ^ 2 := by
        rw [hsum]
    _ = f g := by
        rw [hcol0, one_mul]
        exact mul_div_cancel_left₀ (f g) (pow_ne_zero 2 hne)

end Work.LT
