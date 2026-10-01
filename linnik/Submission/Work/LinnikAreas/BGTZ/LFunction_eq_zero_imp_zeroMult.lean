import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer

namespace Work.LinnikAreas.BGTZ

open DirichletCharacter

/-- **Bridge: a zero of the ordinary `L`-function of a non-principal character is a
`zeroMult`-zero.**

If `0 < Re ρ < 1` and `L(ρ,χ) = 0` for a non-principal `χ` mod `q`, then `ρ` is a zero of the
completed `L`-function of the primitive character inducing `χ` (`zeroMult χ ρ ≠ 0`).

Route: with `ψ = χ.primitiveCharacter` (primitive by `primitiveCharacter_isPrimitive`, and
`ψ ≠ 1` because `χ ≠ 1`), Mathlib's `LFunction_changeLevel` gives
`L(s,χ) = L(s,ψ) · ∏_{p ∈ q.primeFactors} (1 - ψ(p) p^{-s})`, whose correction factors are non-zero
for `0 < Re s < 1`; hence `L(ρ,ψ) = 0`.  On the strip the ordinary and the completed `L`-function
have the same vanishing order
(`Commons.NumberTheory.DirichletCharacter.lFunction_order_eq_completed_order_on_strip`), and
`L(ρ,ψ) = 0` with `L` analytic at `ρ` and not locally identically zero gives
`analyticOrderNatAt (LFunction ψ) ρ ≠ 0` (Mathlib: `analyticOrderAt_ne_zero`), which transfers to
`analyticOrderNatAt (completedLFunction ψ) ρ ≠ 0`, i.e. `zeroMult χ ρ ≠ 0`. -/
theorem LFunction_eq_zero_imp_zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (h : DirichletCharacter.LFunction χ ρ = 0) :
    Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
  classical
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  -- the primitive character inducing a non-principal character is non-principal
  have hψne : χ.primitiveCharacter ≠ 1 := by
    intro h1'
    exact hχ (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1',
      DirichletCharacter.changeLevel_one χ.conductor_dvd_level])
  -- the change-of-level correction factor does not vanish at `ρ` (where `0 < Re ρ < 1`)
  have hprod : (∏ p ∈ q.primeFactors,
      (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-ρ))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hpos : (0 : ℝ) < p := by linarith
    have hnorm : ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-ρ)‖ < 1 := by
      have h1' : ‖(p : ℂ) ^ (-ρ)‖ = (p : ℝ) ^ (-ρ.re) := by
        simpa using Complex.norm_natCast_cpow_of_pos hpp.pos (-ρ)
      calc ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-ρ)‖
          ≤ ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * ‖(p : ℂ) ^ (-ρ)‖ :=
            norm_mul_le _ _
        _ ≤ 1 * ((p : ℝ) ^ (-ρ.re)) := by
              rw [h1']
              exact mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (by positivity)
        _ < 1 := by
              rw [one_mul, Real.rpow_neg hpos.le]
              exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp1 h0)
    intro hzero
    have ha : χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-ρ) = 1 :=
      (sub_eq_zero.mp hzero).symm
    rw [ha, norm_one] at hnorm
    exact absurd hnorm (lt_irrefl 1)
  -- hence `ρ` is a zero of the ordinary `L`-function of the primitive character
  have hLψ : DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 := by
    have hcl := Work.LinnikAreas.OtherCharRepel.LFunction_eq_primitiveCharacter_mul χ hχ ρ
    rw [hcl] at h
    exact (mul_eq_zero.mp h).resolve_right hprod
  -- and a zero of the primitive `L`-function in the critical strip is a `zeroMult`-zero
  exact (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ hχ).2.2 ρ hLψ h0 h1

end Work.LinnikAreas.BGTZ
