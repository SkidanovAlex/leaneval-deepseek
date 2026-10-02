import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology
/-- For `n ≥ 1` and `a ≠ 0` there is a unit complex number `d` with `Re (a * d ^ n) > 0`.
Hint: write `a = ‖a‖ * exp (arg a * I)` (`Complex.norm_mul_exp_arg_mul_I`) and take
`d = exp (-(arg a) / n * I)`, so that `d ^ n = exp (-(arg a) * I) = conj a / ‖a‖`. -/
theorem exists_unit_pow_pos {n : ℕ} (hn : 0 < n) {a : ℂ} (ha : a ≠ 0) :
    ∃ d : ℂ, ‖d‖ = 1 ∧ 0 < (a * d ^ n).re := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  refine ⟨Complex.exp (-((a.arg : ℂ) / (n : ℂ) * Complex.I)), ?_, ?_⟩
  · rw [Complex.norm_exp]
    have hre : (-((a.arg : ℂ) / (n : ℂ) * Complex.I)).re = 0 := by simp
    rw [hre, Real.exp_zero]
  · have hpow : (Complex.exp (-((a.arg : ℂ) / (n : ℂ) * Complex.I))) ^ n
        = Complex.exp (-((a.arg : ℂ) * Complex.I)) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      field_simp [hnC]
    have hval :
        a * (Complex.exp (-((a.arg : ℂ) / (n : ℂ) * Complex.I))) ^ n = (‖a‖ : ℂ) := by
      rw [hpow]
      nth_rewrite 1 [← Complex.norm_mul_exp_arg_mul_I a]
      rw [mul_assoc, ← Complex.exp_add]
      have hzz : (a.arg : ℂ) * Complex.I + -((a.arg : ℂ) * Complex.I) = 0 := by ring
      rw [hzz, Complex.exp_zero, mul_one]
    rw [hval, Complex.ofReal_re]
    exact norm_pos_iff.mpr ha

end Work.LandLeaves
