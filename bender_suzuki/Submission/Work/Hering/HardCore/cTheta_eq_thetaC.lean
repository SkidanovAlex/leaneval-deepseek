import Mathlib
import Submission.Work.Hering.AppVIII.CTwoStepDefs
import Submission.Work.Hering.AppVIII.FrobField
import Submission.Work.Hering.AppVIII.cType_mixed
import Submission.Work.Hering.HardCore.ringAut_GF8_frobPow_lt
import Submission.Work.Hering.HardCore.thetaC_one_apply
import Submission.Work.Hering.HardCore.exists_ne_zero_ne_one_pow_seven

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The automorphism `θ` of `GF(8)` with `(θ (θ a))² = a` is the Frobenius `x ↦ x²`

In Higman's table the group `C(3,ε)` of type `C` lives over `K = GF(2³)`, and Higman's map `θ`
is the Frobenius `x ↦ x ^ 2 = thetaC 1`.  Here we show that this is *forced* by the relation
`(θ (θ a))² = a`: the relation says `θ² = (x ↦ x²)⁻¹ = (x ↦ x²)²` in `Aut(GF(8)) ≅ ℤ/3`, whose
only element with square the Frobenius square is the Frobenius itself.

Concretely: every ring automorphism of `GF(2³)` is `x ↦ x ^ (2 ^ i)` with `i < 3`
(`ringAut_GF8_frobPow_lt`), and the relation forces `i = 1`: for `x₀ ∉ {0,1}` one gets
`x₀ ^ (2 ^ (2i+1)) = x₀`, i.e. `x₀ ^ (2 ^ (2i+1) - 1) = 1`, so `orderOf x₀` divides both `7`
(one has `x₀ ^ 7 = 1`) and `2 ^ (2i+1) - 1`; for `i = 0, 2` the gcd is `1`, forcing `x₀ = 1`.
-/

set_option autoImplicit false

namespace Work.Hering.HardCore

/-- If `θ : GF(8) → GF(8)` is the Frobenius power `x ↦ x ^ (2 ^ i)` and `(θ (θ a))² = a` for all
`a`, then the exponent satisfies `i = 1` (for `i < 3`, i.e. for the three honest possibilities). -/
theorem frobPow_exp_eq_one_of_sq (θ : GaloisField 2 3 ≃+* GaloisField 2 3)
    (hθ2 : ∀ a : GaloisField 2 3, (θ (θ a)) ^ 2 = a)
    (i : ℕ) (hi : i < 3) (hpow : ∀ x : GaloisField 2 3, θ x = x ^ (2 ^ i))
    (x₀ : GaloisField 2 3) (hx0 : x₀ ≠ 0) (hx1 : x₀ ≠ 1) (h7 : x₀ ^ 7 = 1) : i = 1 := by
  -- `2 ^ i * 2 ^ i * 2 = 2 ^ (2 * i + 1)`
  have harith : (2 : ℕ) ^ i * 2 ^ i * 2 = 2 ^ (2 * i + 1) := by
    calc (2 : ℕ) ^ i * 2 ^ i * 2 = (2 ^ i) ^ 2 * 2 := by ring
      _ = 2 ^ (i * 2) * 2 := by rw [← pow_mul]
      _ = 2 ^ (i * 2 + 1) := by rw [← pow_succ]
      _ = 2 ^ (2 * i + 1) := by congr 1; ring
  -- `θ (θ x₀) = x₀ ^ (2 ^ i * 2 ^ i)`
  have hstep : θ (θ x₀) = x₀ ^ (2 ^ i * 2 ^ i) := by
    rw [hpow (θ x₀), hpow x₀, ← pow_mul]
  -- hence `x₀ ^ (2 ^ i * 2 ^ i * 2) = x₀`, i.e. `x₀ ^ (2 ^ (2i+1)) = x₀`
  have hmain : x₀ ^ (2 ^ i * 2 ^ i * 2) = x₀ := by
    have h := hθ2 x₀
    rw [hstep, ← pow_mul] at h
    exact h
  have hm : x₀ ^ (2 ^ i * 2 ^ i * 2 - 1) = 1 := by
    have hge : 1 ≤ 2 ^ i * 2 ^ i * 2 := by
      have hpos : 0 < 2 ^ i * 2 ^ i * 2 := by positivity
      omega
    have h1 : x₀ ^ (2 ^ i * 2 ^ i * 2 - 1) * x₀ = x₀ ^ (2 ^ i * 2 ^ i * 2) := by
      rw [← pow_succ, Nat.sub_add_cancel hge]
    have h2 : x₀ ^ (2 ^ i * 2 ^ i * 2 - 1) * x₀ = 1 * x₀ := by rw [h1, hmain, one_mul]
    exact mul_right_cancel₀ hx0 h2
  have hm' : x₀ ^ (2 ^ (2 * i + 1) - 1) = 1 := by rw [harith] at hm; exact hm
  -- `orderOf x₀` divides `gcd 7 (2 ^ (2i+1) - 1)`, which is `1` for `i = 0` and `i = 2`
  have hdvd : orderOf x₀ ∣ Nat.gcd 7 (2 ^ (2 * i + 1) - 1) :=
    Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr h7) (orderOf_dvd_iff_pow_eq_one.mpr hm')
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with h | h | h
  · exfalso
    rw [h] at hdvd
    norm_num at hdvd
    exact hx1 hdvd
  · exact h
  · exfalso
    rw [h] at hdvd
    norm_num at hdvd
    exact hx1 hdvd

theorem cTheta_eq_thetaC (θ : GaloisField 2 3 ≃+* GaloisField 2 3)
    (hθ2 : ∀ a : GaloisField 2 3, (θ (θ a)) ^ 2 = a) :
    θ = Work.Hering.AppVIII.thetaC 1 := by
  -- every ring automorphism of `GF(8)` is a Frobenius power `x ↦ x ^ (2 ^ i)`, `i < 3`
  obtain ⟨i, hi, hpow⟩ := ringAut_GF8_frobPow_lt θ
  -- an element of `GF(8)` different from `0` and `1` (it has multiplicative order `7`)
  obtain ⟨x₀, hx0, hx1, h7⟩ := exists_ne_zero_ne_one_pow_seven
  -- the relation `(θ (θ a))² = a` forces `i = 1`
  have hi1 : i = 1 := frobPow_exp_eq_one_of_sq θ hθ2 i hi hpow x₀ hx0 hx1 h7
  rw [hi1] at hpow
  refine RingEquiv.ext fun x => ?_
  rw [hpow x]
  norm_num
  exact (thetaC_one_apply x).symm

end Work.Hering.HardCore
