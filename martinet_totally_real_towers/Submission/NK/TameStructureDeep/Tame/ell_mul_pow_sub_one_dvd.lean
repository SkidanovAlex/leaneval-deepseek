import Mathlib

namespace NK.TameStructureDeep.Tame

open Finset

/-- Auxiliary number-theoretic lemma: for a prime `ℓ` and a positive integer `x` coprime
to `ℓ`, the product `ℓ * (x - 1)` divides `x ^ (ℓ * (ℓ - 1)) - 1`.

Indeed, writing `u = x ^ (ℓ - 1)`, we have `x ^ (ℓ * (ℓ - 1)) - 1 = u ^ ℓ - 1`, which by
the geometric sum identity equals `(∑ i ∈ range ℓ, u ^ i) * (u - 1)`.  Since `ℓ ∣ u - 1`
(Fermat's little theorem), every term of the sum is congruent to `1` modulo `ℓ`, so the
sum is congruent to `ℓ ≡ 0` modulo `ℓ`, giving the extra factor `ℓ`; finally
`x - 1 ∣ u - 1`. -/
lemma ell_mul_sub_one_dvd_pow {x ℓ : ℕ} (hℓ : ℓ.Prime) (hx : 0 < x) (hcop : x.Coprime ℓ) :
    ℓ * (x - 1) ∣ x ^ (ℓ * (ℓ - 1)) - 1 := by
  set u := x ^ (ℓ - 1) with hudef
  have hu1le : 1 ≤ u := by rw [hudef]; exact Nat.one_le_pow _ x hx
  have hF : u ≡ 1 [MOD ℓ] := by
    rw [hudef]; exact Nat.ModEq.pow_card_sub_one_eq_one hℓ hcop
  have hS : ℓ ∣ ∑ i ∈ Finset.range ℓ, u ^ i := by
    rw [← Nat.modEq_zero_iff_dvd]
    calc ∑ i ∈ Finset.range ℓ, u ^ i
        ≡ ∑ i ∈ Finset.range ℓ, (1 : ℕ) [MOD ℓ] :=
          Nat.ModEq.sum (fun i _ => by simpa using Nat.ModEq.pow i hF)
      _ = ℓ := by simp
      _ ≡ 0 [MOD ℓ] := Nat.modEq_zero_iff_dvd.mpr (dvd_refl ℓ)
  have hgeom : (∑ i ∈ Finset.range ℓ, u ^ i) * (u - 1) + 1 = u ^ ℓ := by
    have h := geom_sum_mul_add (u - 1) ℓ
    rwa [Nat.sub_add_cancel hu1le] at h
  have hkey : ℓ * (u - 1) ∣ u ^ ℓ - 1 := by
    have hN : u ^ ℓ - 1 = (∑ i ∈ Finset.range ℓ, u ^ i) * (u - 1) := by
      rw [← hgeom, Nat.add_sub_cancel]
    rw [hN]
    exact mul_dvd_mul_right hS (u - 1)
  have hxu : x - 1 ∣ u - 1 := by
    rw [hudef]; exact Nat.sub_one_dvd_pow_sub_one x (ℓ - 1)
  have hpow : u ^ ℓ = x ^ (ℓ * (ℓ - 1)) := by
    rw [hudef, ← pow_mul, mul_comm (ℓ - 1) ℓ]
  rw [← hpow]
  exact (mul_dvd_mul_left ℓ hxu).trans hkey

theorem ell_mul_pow_sub_one_dvd {q d ℓ : ℕ} (hℓ : ℓ.Prime) (hq : 2 ≤ q) (hd : 0 < d)
    (hcop : ℓ.Coprime q) : ℓ * (q ^ d - 1) ∣ q ^ (d * ℓ * (ℓ - 1)) - 1 := by
  have hq0 : 0 < q := by omega
  have hxpos : 0 < q ^ d := by
    have hd1 : 1 ≤ d := hd
    calc (0 : ℕ) < q := by omega
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ d := Nat.pow_le_pow_right hq0 hd1
  have hcopd : (q ^ d).Coprime ℓ := (Nat.Coprime.pow_right d hcop).symm
  have h := ell_mul_sub_one_dvd_pow hℓ hxpos hcopd
  have h2 : (q ^ d) ^ (ℓ * (ℓ - 1)) = q ^ (d * ℓ * (ℓ - 1)) := by
    rw [← pow_mul, mul_assoc]
  rwa [h2] at h

end NK.TameStructureDeep.Tame
