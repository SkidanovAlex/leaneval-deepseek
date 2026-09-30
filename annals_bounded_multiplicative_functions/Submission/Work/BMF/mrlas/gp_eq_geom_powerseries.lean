import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.mrlas.Psi2_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local Euler factor at `p = 2` as a geometric power series

For `s = σ + τ i` the local variable `u 2 s = exp (-(log 2) s)` factors as
`2^{-σ} · exp (-(τ log 2) i)`, so the Euler factor
`gp f 2 s = Σ_e f (2^e) (u 2 s)^e` becomes the geometric power series
`Σ_e f (2^e) (2^{-σ} exp (-(τ log 2) i))^e`.
-/

namespace Work.BMF.mrlas

open Complex

/-- At `s = σ + τ i`, `u 2 s = 2^{-σ} · exp (-(τ log 2) i)`. -/
lemma u_two_eq (σ τ : ℝ) :
    u 2 ((σ : ℂ) + (τ : ℂ) * Complex.I)
      = (((2 : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-(τ * Real.log 2)) : ℝ) * Complex.I) := by
  have harg : -(Real.log 2 : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I)
      = ((-(Real.log 2 * σ) : ℝ) : ℂ) + (((-(τ * Real.log 2)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [u]
  simp only [Nat.cast_ofNat]
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  congr 1
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring_nf

lemma gp_eq_geom_powerseries (f : ℕ → ℂ) (σ τ : ℝ) :
    Work.BMF.gp f 2 ((σ : ℂ) + (τ : ℂ) * Complex.I)
      = ∑' e : ℕ, f (2 ^ e) * ((((2 : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (((-(τ * Real.log 2)) : ℝ) * Complex.I)) ^ e := by
  rw [gp_eq f Nat.prime_two]
  exact tsum_congr (fun e => by rw [u_two_eq])

end Work.BMF.mrlas
