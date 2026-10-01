import Mathlib
import Submission.Work.LinnikBurgess.ddSqZeroPow
import Submission.Work.LinnikBurgess.ddKernelUnitsMap
import Submission.Work.LinnikBurgess.ddGPowEqOne
import Submission.Work.LinnikBurgess.ddGPowEq

/-!
# The value of a primitive Dirichlet character at `1 + p^j`

For `p` an odd prime, `1 ≤ j ≤ e - 1` and `χ` a primitive Dirichlet character of level `p ^ e`,
the number `χ (1 + p ^ j)` is a primitive `p ^ (e - j)`-th root of unity.

The two halves of the proof are:

* **Arithmetic.** `(1 + p^j) ^ (p ^ (e - j)) ≡ 1` and
  `(1 + p^j) ^ (p ^ (e - j - 1)) ≡ 1 + p ^ (e - 1) · u (mod p^e)` with `p ∤ u`;
  both are the lifting-the-exponent computation `v_p ((1+p^j)^{p^k} - 1) = j + k`
  (`ddGPowEqOne`, `ddGPowEq`).

* **Character theory.** A primitive `χ` of level `p^e` is nontrivial at every principal unit
  `1 + p ^ (e-1) · u` with `p ∤ u` (`ddChiPrincipalNeOne`): if `χ` vanished there, then
  `χ (1 + p^(e-1) t) = 1` for *every* `t` (because `(1 + p^(e-1) u)^m = 1 + p^(e-1) (m u)`,
  `ddPowOneAddMul`, and `u` is invertible mod `p`), whence `χ` is trivial on the kernel of
  `(ZMod (p^e))ˣ → (ZMod (p^(e-1)))ˣ` (`ddKernelUnitsMap`), i.e. `χ` factors through level
  `p ^ (e-1)`, contradicting primitivity.

Hence `χ (1 + p^j) ^ (p ^ (e-j)) = 1` while `χ (1 + p^j) ^ (p ^ (e-j-1)) = χ (1 + p^(e-1) u) ≠ 1`,
so the order of `χ (1 + p^j)` is exactly `p ^ (e - j)`.
-/

namespace Work.LinnikBurgess

open DirichletCharacter

/-- In `ZMod (p ^ e)` with `2 ≤ e`, taking the `m`-th power of a principal unit
`1 + p ^ (e-1) · u` only multiplies its parameter:
`(1 + p^(e-1) u) ^ m = 1 + p^(e-1) (m u)`.

Indeed the parameter `x = p^(e-1) u` satisfies `x ^ 2 = 0` in `ZMod (p ^ e)`, because
`p ^ (2 (e-1))` is divisible by `p ^ e`; then `ddSqZeroPow` applies. -/
theorem ddPowOneAddMul {p e : ℕ} (he : 2 ≤ e) (u m : ℕ) :
    (((1 + p ^ (e - 1) * u : ℕ) : ZMod (p ^ e)) ^ m)
      = ((1 + p ^ (e - 1) * (m * u) : ℕ) : ZMod (p ^ e)) := by
  have hx2 : (((p ^ (e - 1) * u : ℕ) : ZMod (p ^ e)) ^ 2 = 0) := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    have h : (p ^ (e - 1) * u) ^ 2 = p ^ ((e - 1) * 2) * u ^ 2 := by
      rw [mul_pow, ← pow_mul]
    rw [h]
    exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow p (by omega)) _
  have hcast : ((1 + p ^ (e - 1) * u : ℕ) : ZMod (p ^ e))
      = 1 + ((p ^ (e - 1) * u : ℕ) : ZMod (p ^ e)) := by push_cast; ring
  have hcast2 : ((1 + p ^ (e - 1) * (m * u) : ℕ) : ZMod (p ^ e))
      = 1 + ((p ^ (e - 1) * (m * u) : ℕ) : ZMod (p ^ e)) := by push_cast; ring
  rw [hcast, hcast2, ddSqZeroPow hx2 m]
  congr 1
  push_cast
  ring

/-- **Primitivity kills the principal units.**  If `p` is prime, `2 ≤ e`, `χ` is a Dirichlet
character of level `p ^ e` and `p ∤ u`, then a primitive `χ` does not vanish at `1 + p^(e-1) u`.

Contrapositively, `χ (1 + p^(e-1) u) = 1` forces `χ` to be trivial on every principal unit
`1 + p^(e-1) t`, hence to factor through level `p ^ (e-1)`, hence `conductor χ ∣ p ^ (e-1)`. -/
theorem ddChiPrincipalNeOne {p e : ℕ} [Fact p.Prime] (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) {u : ℕ} (hu : ¬ p ∣ u) :
    χ (((1 + p ^ (e - 1) * u : ℕ) : ZMod (p ^ e))) ≠ 1 := by
  intro h1
  have hp : p.Prime := Fact.out
  have hd : p ^ (e - 1) ∣ p ^ e := by
    rw [show e = (e - 1) + 1 by omega, pow_succ]
    exact dvd_mul_right _ _
  -- `χ` vanishes on *every* principal unit `1 + p^(e-1) t`
  have htriv : ∀ t : ℕ, χ (((1 + p ^ (e - 1) * t : ℕ) : ZMod (p ^ e))) = 1 := by
    intro t
    -- choose `m` with `m * u ≡ t (mod p)`
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ZMod p) * (u : ZMod p) = (t : ZMod p) := by
      have hu0 : (u : ZMod p) ≠ 0 := fun h => hu ((ZMod.natCast_eq_zero_iff u p).mp h)
      refine ⟨(((t : ZMod p) / (u : ZMod p))).val, ?_⟩
      have hm' : ((((t : ZMod p) / (u : ZMod p))).val : ZMod p) = (t : ZMod p) / (u : ZMod p) :=
        ZMod.natCast_zmod_val _
      rw [hm']
      exact div_mul_cancel₀ _ hu0
    have hmod : m * u ≡ t [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff (m * u) t p, Nat.cast_mul]
      exact hm
    have hmod' : p ^ (e - 1) * (m * u) ≡ p ^ (e - 1) * t [MOD p ^ (e - 1) * p] :=
      hmod.mul_left' _
    have hpe : p ^ (e - 1) * p = p ^ e := by rw [← pow_succ]; congr 1; omega
    have heq : ((p ^ (e - 1) * (m * u) : ℕ) : ZMod (p ^ e))
        = ((p ^ (e - 1) * t : ℕ) : ZMod (p ^ e)) := by
      rw [ZMod.natCast_eq_natCast_iff, ← hpe]
      exact hmod'
    have heq2 : (((1 + p ^ (e - 1) * (m * u) : ℕ)) : ZMod (p ^ e))
        = (((1 + p ^ (e - 1) * t : ℕ)) : ZMod (p ^ e)) := by
      rw [show (((1 + p ^ (e - 1) * (m * u) : ℕ)) : ZMod (p ^ e))
            = 1 + ((p ^ (e - 1) * (m * u) : ℕ) : ZMod (p ^ e)) from by push_cast; ring,
          show (((1 + p ^ (e - 1) * t : ℕ)) : ZMod (p ^ e))
            = 1 + ((p ^ (e - 1) * t : ℕ) : ZMod (p ^ e)) from by push_cast; ring,
          heq]
    rw [← heq2, ← ddPowOneAddMul he u m, map_pow, h1, one_pow]
  -- hence `χ` is trivial on the kernel of the reduction to level `p^(e-1)`
  have hker : (ZMod.unitsMap hd).ker ≤ χ.toUnitHom.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    obtain ⟨t, ht⟩ := ddKernelUnitsMap hp he hd hx
    apply Units.ext
    rw [MulChar.coe_toUnitHom, Units.val_one, ht]
    exact htriv t
  have hft : χ.FactorsThrough (p ^ (e - 1)) := (factorsThrough_iff_ker_unitsMap hd).mpr hker
  have hcdvd : χ.conductor ∣ p ^ (e - 1) := (mem_conductorSet_iff_conductor_dvd χ hd).mp hft
  rw [hχ] at hcdvd
  have hle : p ^ e ≤ p ^ (e - 1) := Nat.le_of_dvd (pow_pos hp.pos _) hcdvd
  have hlt : p ^ (e - 1) < p ^ e := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

/-- **The value of a primitive character at `1 + p^j` is a primitive `p^(e-j)`-th root of
unity.**  Here `p` is an odd prime and `1 ≤ j ≤ e - 1`. -/
theorem ddChiLevelPrimitive {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {j : ℕ} (hj : 1 ≤ j)
    (hje : j ≤ e - 1) (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive) :
    IsPrimitiveRoot (χ ((1 + p ^ j : ℕ) : ZMod (p ^ e))) (p ^ (e - j)) := by
  have he : 2 ≤ e := by omega
  have hpow1 : (χ ((1 + p ^ j : ℕ) : ZMod (p ^ e))) ^ (p ^ (e - j)) = 1 := by
    rw [← map_pow, ddGPowEqOne hp2 hj hje, map_one]
  have hpow2 : (χ ((1 + p ^ j : ℕ) : ZMod (p ^ e))) ^ (p ^ (e - j - 1)) ≠ 1 := by
    intro h
    obtain ⟨u, hu, hueq⟩ := ddGPowEq hp2 hj hje
    rw [← map_pow, hueq] at h
    exact ddChiPrincipalNeOne he χ hχ hu h
  have hord : orderOf (χ ((1 + p ^ j : ℕ) : ZMod (p ^ e))) = p ^ (e - j) := by
    have hdvd : orderOf (χ ((1 + p ^ j : ℕ) : ZMod (p ^ e))) ∣ p ^ (e - j) :=
      orderOf_dvd_of_pow_eq_one hpow1
    obtain ⟨s, hsle, hsp⟩ :=
      (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
    have hseq : s = e - j := by
      rcases lt_or_eq_of_le hsle with hlt | heq
      · exfalso
        have hdvd' : orderOf (χ ((1 + p ^ j : ℕ) : ZMod (p ^ e))) ∣ p ^ (e - j - 1) := by
          rw [hsp]
          exact Nat.pow_dvd_pow p (by omega)
        exact hpow2 (orderOf_dvd_iff_pow_eq_one.mp hdvd')
      · exact heq
    rw [hsp, hseq]
  exact ⟨hpow1, fun l hl => by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hl⟩

end Work.LinnikBurgess
