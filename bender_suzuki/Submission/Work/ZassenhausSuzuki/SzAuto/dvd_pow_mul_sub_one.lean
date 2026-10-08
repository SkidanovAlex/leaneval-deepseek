import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.SzAuto

/-- For `2 ≤ X`, the geometric sum `∑_{j < X-1} (X^N)^j` is divisible by `X - 1`:
each term is `≡ 1` modulo `X - 1`, and there are exactly `X - 1` terms. -/
private lemma sub_one_dvd_geom_sum (X N : ℕ) (hX : 2 ≤ X) :
    (X - 1) ∣ ∑ j ∈ Finset.range (X - 1), (X ^ N) ^ j := by
  have h1X : 1 ≤ X := by omega
  have hXmod : X ≡ 1 [MOD X - 1] := by
    have h : X - 1 ≡ 0 [MOD X - 1] := Nat.modulus_modEq_zero
    have h2 := h.add (Nat.ModEq.refl 1)
    simpa [Nat.sub_add_cancel h1X] using h2
  have hY : X ^ N ≡ 1 [MOD X - 1] := by simpa using hXmod.pow N
  have hsum : (∑ j ∈ Finset.range (X - 1), (X ^ N) ^ j) ≡ 0 [MOD X - 1] := by
    have h1 := Nat.ModEq.sum (s := Finset.range (X - 1)) (f := fun j => (X ^ N) ^ j)
      (g := fun _ => 1) (fun j _ => by simpa using (hY.pow j))
    have hcard : (∑ j ∈ Finset.range (X - 1), (1 : ℕ)) = X - 1 := by simp
    rw [hcard] at h1
    exact h1.trans Nat.modulus_modEq_zero
  exact Nat.modEq_zero_iff_dvd.mp hsum

/-- Second factor of the main argument: `(X ^ (a*b) - 1) * (X - 1)` divides
`X ^ (a*b*(X-1)) - 1`.  Indeed
`X ^ (a*b*(X-1)) - 1 = (X ^ (a*b) - 1) * ∑_{j < X-1} (X ^ (a*b))^j`,
and the geometric cofactor is divisible by `X - 1` (`sub_one_dvd_geom_sum`). -/
private lemma geom_piece (X a b : ℕ) (hX : 2 ≤ X) :
    (X ^ (a * b) - 1) * (X - 1) ∣ X ^ (a * b * (X - 1)) - 1 := by
  rcases Nat.eq_zero_or_pos (a * b) with hab0 | habpos
  · simp [hab0]
  · have h1 : 1 ≤ a * b := habpos
    have hY : 2 ≤ X ^ (a * b) := by
      have : X ≤ X ^ (a * b) := by
        simpa using Nat.pow_le_pow_right (show 0 < X by omega) h1
      exact hX.trans this
    obtain ⟨c, hc⟩ := sub_one_dvd_geom_sum X (a * b) hX
    refine ⟨c, ?_⟩
    have hprod : (X ^ (a * b) - 1) * (∑ j ∈ Finset.range (X - 1), (X ^ (a * b)) ^ j)
        = X ^ (a * b * (X - 1)) - 1 := by
      rw [Nat.geomSum_eq hY (X - 1),
        Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one (X ^ (a * b)) (X - 1)), ← pow_mul]
    rw [← hprod, hc]
    ac_rfl

/-- First factor of the main argument: for coprime `a b`,
`(X ^ a - 1) * (X ^ b - 1)` divides `(X ^ (a*b) - 1) * (X - 1)`.
Since `gcd (X^a - 1) (X^b - 1) = X - 1` and `lcm * gcd = product`,
it suffices that the `lcm` divides `X ^ (a*b) - 1`, which holds because both
`X ^ a - 1` and `X ^ b - 1` do. -/
private lemma lcm_piece (X a b : ℕ) (hab : Nat.Coprime a b) :
    (X ^ a - 1) * (X ^ b - 1) ∣ (X ^ (a * b) - 1) * (X - 1) := by
  have hgcd : Nat.gcd (X ^ a - 1) (X ^ b - 1) = X - 1 := by
    rw [Nat.pow_sub_one_gcd_pow_sub_one, hab.gcd_eq_one, pow_one]
  have hprod : (X - 1) * Nat.lcm (X ^ a - 1) (X ^ b - 1) = (X ^ a - 1) * (X ^ b - 1) := by
    rw [← hgcd, Nat.gcd_mul_lcm]
  have hA : (X ^ a - 1) ∣ X ^ (a * b) - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one X (dvd_mul_right a b)
  have hB : (X ^ b - 1) ∣ X ^ (a * b) - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one X (dvd_mul_left b a)
  have hlcm : Nat.lcm (X ^ a - 1) (X ^ b - 1) ∣ X ^ (a * b) - 1 := Nat.lcm_dvd hA hB
  have step : Nat.lcm (X ^ a - 1) (X ^ b - 1) * (X - 1) ∣ (X ^ (a * b) - 1) * (X - 1) :=
    Nat.mul_dvd_mul_right hlcm (X - 1)
  rw [mul_comm (Nat.lcm (X ^ a - 1) (X ^ b - 1)) (X - 1), hprod] at step
  exact step

theorem dvd_pow_mul_sub_one (X a b : ℕ) (hX : 2 ≤ X) (hab : Nat.Coprime a b) :
    (X ^ a - 1) * (X ^ b - 1) ∣ X ^ (a * b * (X - 1)) - 1 := by
  exact (lcm_piece X a b hab).trans (geom_piece X a b hX)

end Work.ZassenhausSuzuki.SzAuto
