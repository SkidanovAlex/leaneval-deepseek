import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero

namespace Work.LinnikAreas

open DirichletCharacter

/-- **Bridge between `zeroMult`-zeros and zeros of the ordinary `L`-function.**

If `ρ = β` is a real zero of a non-principal Dirichlet character `χ` in the sense of the Linnik
contract (`zeroMult χ β ≠ 0`, i.e. `β` is a zero of the *completed* `L`-function of the primitive
character inducing `χ`), then `β` is a genuine zero of the ordinary Dirichlet `L`-function at the
level of `χ` itself.

Proof.  Write `χ = changeLevel χ.conductor_dvd_level χ.primitiveCharacter` (Mathlib's
`changeLevel_primitiveCharacter`).  Mathlib's `LFunction_changeLevel` gives, for every `s ≠ 1`
in fact for all `s` since `χ.primitiveCharacter ≠ 1`,

`L(s,χ) = L(s,χ*) · ∏_{p ∈ q.primeFactors} (1 - χ*(p) p^{-s})`.

The finite correction factor is non-zero on the critical strip: for a prime `p ≥ 2` and
`0 < β < 1` we have `‖χ*(p) p^{-β}‖ ≤ p^{-β} < 1`, so `1 - χ*(p) p^{-β} ≠ 0`.  Finally
`zeroMult χ β ≠ 0` with `χ ≠ 1` makes `β` a zero of `L(s,χ*)` by
`Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero`, and the product of a zero with a non-zero
number is zero. -/
theorem LFunction_eq_zero_of_zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hzm : Work.LinnikContract.zeroMult χ (β : ℂ) ≠ 0) :
    DirichletCharacter.LFunction χ (β : ℂ) = 0 := by
  have hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  -- the primitive character inducing a non-principal character is non-principal
  have hχc : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    have h' : (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ :=
      changeLevel_primitiveCharacter χ
    rw [h, changeLevel_one] at h'
    exact h'.symm
  -- `β` is a zero of the `L`-function of the primitive character inducing `χ`
  have hL : DirichletCharacter.LFunction χ.primitiveCharacter (β : ℂ) = 0 :=
    Work.LinnikAreas.DhCapped.LFunctionPrimitiveZero χ hχ (u := (β : ℂ)) hzm
  -- the local correction factor at the primes dividing `q` does not vanish at `β`
  have hprod : (∏ p ∈ q.primeFactors,
      (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-(β : ℂ)))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hpos : (0 : ℝ) < p := by linarith
    have hnorm : ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-(β : ℂ))‖ < 1 := by
      have h1 : ‖(p : ℂ) ^ (-(β : ℂ))‖ = (p : ℝ) ^ (-β) := by
        have := Complex.norm_cpow_eq_rpow_re_of_pos hpos (-(β : ℂ))
        simpa using this
      calc ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-(β : ℂ))‖
          ≤ ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * ‖(p : ℂ) ^ (-(β : ℂ))‖ :=
            norm_mul_le _ _
        _ ≤ 1 * ((p : ℝ) ^ (-β)) := by
              rw [h1]
              exact mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (by positivity)
        _ < 1 := by
              rw [one_mul, Real.rpow_neg hpos.le]
              exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow hp1 hβ0)
    intro h
    have ha : χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-(β : ℂ)) = 1 :=
      (sub_eq_zero.mp h).symm
    rw [ha, norm_one] at hnorm
    exact absurd hnorm (lt_irrefl 1)
  -- Mathlib's `LFunction_changeLevel` relates `L(s,χ)` to `L(s,χ*)`
  have hcl := DirichletCharacter.LFunction_changeLevel (M := χ.conductor) (N := q)
      χ.conductor_dvd_level χ.primitiveCharacter (s := (β : ℂ)) (Or.inl hχc)
  rw [changeLevel_primitiveCharacter] at hcl
  rw [hcl, hL, zero_mul]

end Work.LinnikAreas
