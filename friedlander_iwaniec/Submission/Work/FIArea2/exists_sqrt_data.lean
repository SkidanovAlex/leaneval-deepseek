import Mathlib
import Submission.Work.FIArea2.Tsum_odd_defs
import Submission.Work.FIArea2.sqRoots_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

/-- **Pure ring algebra behind `exists_sqrt_data`.**  If `ρ` is a square root of `a` with a
one-sided inverse `ρ'` (`ρ * ρ' = 1`) and `2` is invertible, then halving `h₂ ∓ h₁ρ'` produces
`α, β` with `2α = h₂ - h₁ρ'`, `2β = h₂ + h₁ρ'` and `4aαβ = -(h₁² - a h₂²)`. -/
theorem ring_sqrt_data {R : Type*} [CommRing R] (a h1 h2 ρ ρ' : R)
    (hρ : ρ ^ 2 = a) (hρρ' : ρ * ρ' = 1) (h2u : IsUnit (2 : R)) :
    ∃ α β : R, (2 : R) * α = h2 - h1 * ρ' ∧ (2 : R) * β = h2 + h1 * ρ' ∧
      (4 : R) * a * α * β = -(h1 ^ 2 - a * h2 ^ 2) := by
  have hmul : ∀ x : R, (2 : R) * (x * ↑(h2u.unit⁻¹)) = x := by
    intro x
    rw [mul_comm (2 : R) (x * ↑(h2u.unit⁻¹)), mul_assoc,
      mul_comm (↑(h2u.unit⁻¹)) (2 : R), IsUnit.mul_val_inv h2u, mul_one]
  refine ⟨(h2 - h1 * ρ') * ↑(h2u.unit⁻¹), (h2 + h1 * ρ') * ↑(h2u.unit⁻¹), ?_, ?_, ?_⟩
  · exact hmul _
  · exact hmul _
  · have haρ' : a * ρ' ^ 2 = 1 := by
      have h : (ρ * ρ') ^ 2 = (1 : R) := by rw [hρρ', one_pow]
      rw [mul_pow, hρ] at h
      exact h
    have key : ((2 : R) * ((h2 - h1 * ρ') * ↑(h2u.unit⁻¹)))
        * ((2 : R) * ((h2 + h1 * ρ') * ↑(h2u.unit⁻¹))) = h2 ^ 2 - h1 ^ 2 * ρ' ^ 2 := by
      rw [hmul, hmul]; ring
    have e : (4 : R) * a * ((h2 - h1 * ρ') * ↑(h2u.unit⁻¹))
        * ((h2 + h1 * ρ') * ↑(h2u.unit⁻¹))
        = a * (((2 : R) * ((h2 - h1 * ρ') * ↑(h2u.unit⁻¹)))
            * ((2 : R) * ((h2 + h1 * ρ') * ↑(h2u.unit⁻¹)))) := by ring
    rw [e, key, mul_sub]
    have e2 : a * (h1 ^ 2 * ρ' ^ 2) = h1 ^ 2 := by
      calc a * (h1 ^ 2 * ρ' ^ 2) = h1 ^ 2 * (a * ρ' ^ 2) := by ring
        _ = h1 ^ 2 * 1 := by rw [haρ']
        _ = h1 ^ 2 := by ring
    rw [e2]
    ring

/-- **Hensel lifting of a square root, and the resulting `α, β`.**  Let `p` be an odd prime,
`ν ≥ 1`, `a` a unit modulo `p^ν` which is a square modulo `p`.  Then there are `ρ, ρ', α, β` in
`ZMod (p^ν)` with

* `ρ ^ 2 = a` and `ρ * ρ' = 1` (so `ρ` is a unit with inverse `ρ'`),
* `2 α = h₂ - h₁ ρ'` and `2 β = h₂ + h₁ ρ'`,
* `4 a α β = -(h₁ ^ 2 - a h₂ ^ 2)`.

Route: lift the square root of `a` modulo `p` to a square root `ρ₀ : ℤ` of `a` modulo `p^ν` by
`Work.FIArea2.henselSqDvdAux` (its hypotheses are `Odd p`, `k = ν > 0`, `¬ (p : ℤ) ∣ a` — which
follows from `ha` — and `∃ x : ℤ, (p:ℤ) ∣ x^2 - a`, which follows from `hsq` by taking the `val`
of a square root), put `ρ := (ρ₀ : ZMod (p^ν))` and `ρ' := ρ⁻¹`; `ρ` is a unit because
`ρ ^ 2 = a` is one, so `ρ * ρ' = 1`.  `2` is a unit modulo `p^ν` (odd `p`), so
`α := (h₂ - h₁ρ') · 2⁻¹`, `β := (h₂ + h₁ρ') · 2⁻¹` exist and satisfy the two linear identities;
finally `(2α)(2β) = h₂² - h₁²ρ'² = h₂² - h₁² a⁻¹` (since `ρρ' = 1` gives `a ρ'² = (ρρ')² = 1`), so
`4aαβ = a h₂² - h₁² = -(h₁² - a h₂²)`. -/
theorem exists_sqrt_data {p ν : ℕ} (hp : p.Prime) (hodd : Odd p) (hν : 1 ≤ ν) [NeZero (p ^ ν)]
    (a h1 h2 : ℤ) (ha : IsUnit (a : ZMod (p ^ ν))) (hsq : IsSquare ((a : ZMod p))) :
    ∃ ρ ρ' α β : ZMod (p ^ ν),
      ρ ^ 2 = (a : ZMod (p ^ ν)) ∧ ρ * ρ' = 1 ∧
      (2 : ZMod (p ^ ν)) * α = (h2 : ZMod (p ^ ν)) - (h1 : ZMod (p ^ ν)) * ρ' ∧
      (2 : ZMod (p ^ ν)) * β = (h2 : ZMod (p ^ ν)) + (h1 : ZMod (p ^ ν)) * ρ' ∧
      (4 : ZMod (p ^ ν)) * (a : ZMod (p ^ ν)) * α * β
        = -(((h1 ^ 2 - a * h2 ^ 2 : ℤ)) : ZMod (p ^ ν)) := by
  -- `a` is not divisible by `p`, using that it is a unit modulo `p^ν`.
  have ha' : ¬ (p : ℤ) ∣ a := by
    intro hpa
    have hcop : IsCoprime ((p : ℤ) ^ ν) a := by
      have h := ha
      rw [ZMod.coe_int_isUnit_iff_isCoprime] at h
      simpa [Nat.cast_pow] using h
    have hnat : Nat.Coprime (p ^ ν) a.natAbs := by
      have := Int.isCoprime_iff_nat_coprime.mp hcop
      simpa [Int.natAbs_pow] using this
    have hp_dvd_a : p ∣ a.natAbs := by
      simpa using Int.natAbs_dvd_natAbs.mpr hpa
    have hp_dvd_pow : p ∣ p ^ ν := dvd_pow_self p (by omega)
    have hg : p ∣ Nat.gcd (p ^ ν) a.natAbs := Nat.dvd_gcd hp_dvd_pow hp_dvd_a
    rw [Nat.coprime_iff_gcd_eq_one.mp hnat] at hg
    have hle : p ≤ 1 := Nat.le_of_dvd (by norm_num) hg
    have h2 := hp.two_le
    omega
  -- `2` is a unit modulo `p^ν` because `p` is odd.
  have hpnotdvd2 : ¬ p ∣ 2 := by
    intro hd
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have h2 := hp.two_le
    have hpne2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hodd
    omega
  have h2unit : IsUnit (2 : ZMod (p ^ ν)) := by
    have h := (ZMod.isUnit_natCast_iff_not_dvd_pow (p := p) (d := ν) (a := 2) hp
      (by omega)).mpr hpnotdvd2
    simpa using h
  -- Lift the square root of `a` mod `p` to a square root of `a` mod `p^ν`.
  obtain ⟨x, hx⟩ := (isSquare_iff_exists_sq ((a : ZMod p))).mp hsq
  obtain ⟨x0, hx0⟩ := ZMod.intCast_surjective x
  have hxdvd : (p : ℤ) ∣ x0 ^ 2 - a := by
    have h : (((x0 : ℤ) ^ 2 : ℤ) : ZMod p) = ((a : ℤ) : ZMod p) := by
      rw [Int.cast_pow, hx0]; exact hx.symm
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    have hh := dvd_neg.mpr h
    rwa [neg_sub] at hh
  obtain ⟨z, hz⟩ := henselSqDvdAux p hp hodd ν (by omega) a ha' ⟨x0, hxdvd⟩
  set rho : ZMod (p ^ ν) := ((z : ℤ) : ZMod (p ^ ν)) with hrhodef
  have hrho : rho ^ 2 = (a : ZMod (p ^ ν)) := by
    rw [hrhodef]
    have h : (((z : ℤ) ^ 2 : ℤ) : ZMod (p ^ ν)) = ((a : ℤ) : ZMod (p ^ ν)) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub, Nat.cast_pow]
      have hh := dvd_neg.mpr hz
      rwa [neg_sub] at hh
    rwa [Int.cast_pow] at h
  have hrhounit : IsUnit rho := by
    have h2 : IsUnit (rho * rho) := by rw [← pow_two, hrho]; exact ha
    exact (IsUnit.mul_iff.mp h2).1
  have hrho' : rho * ↑(hrhounit.unit⁻¹) = 1 := IsUnit.mul_val_inv hrhounit
  obtain ⟨α, β, hα, hβ, hfin⟩ :=
    ring_sqrt_data (a : ZMod (p ^ ν)) (h1 : ZMod (p ^ ν)) (h2 : ZMod (p ^ ν))
      rho ↑(hrhounit.unit⁻¹) hrho hrho' h2unit
  refine ⟨rho, ↑(hrhounit.unit⁻¹), α, β, hrho, hrho', hα, hβ, ?_⟩
  rw [hfin]
  push_cast
  ring

end Work.FIArea2
