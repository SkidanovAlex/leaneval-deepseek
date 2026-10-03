import Mathlib

namespace Work.FIArea6Hecke.R

open scoped BigOperators


set_option maxHeartbeats 2000000 in
/-- A sequence `(a e)` satisfying the second-order linear recurrence
`a (e+2) = s * a (e+1) - p * a e` (with `s = c₁ + c₂`, `p = c₁ * c₂`) and the
initial conditions `a 0 = 1`, `a 1 = s` has generating function satisfying
`(∑ e, a e * u^e) * (1 - s * u + p * u^2) = 1` for every `u` for which the
series converges.  This is the generating-function identity for the Hecke-type
polynomial `X² + Y⁴` (a `q`-expansion whose coefficients obey such a recurrence).

The proof identifies the "defect" sequence `e ↦ a (e+2) u^{e+2} - s a (e+1) u^{e+2}
+ p a e u^{e+2}`, which vanishes identically by the recurrence, and evaluates its
total sum by linearity against the tail identities
`∑' e, f (e+k) = (∑' e, f e) - ∑_{e<k} f e`. -/
theorem geoGenFunc (a : ℕ → ℂ) (u c₁ c₂ : ℂ)
    (h0 : a 0 = 1) (h1 : a 1 = c₁ + c₂)
    (hrec : ∀ e : ℕ, a (e + 2) = (c₁ + c₂) * a (e + 1) - (c₁ * c₂) * a e)
    (hsum : Summable (fun e : ℕ => a e * u ^ e)) :
    (∑' e : ℕ, a e * u ^ e) * (1 - (c₁ + c₂) * u + (c₁ * c₂) * u ^ 2) = 1 := by
  -- Tail identities: `1 + ∑' e, a (e+1) u^{e+1} = S` and `(1 + s u) + ∑' e, a (e+2) u^{e+2} = S`,
  -- where `S = ∑' e, a e u^e`.
  have hraw1 : (1 : ℂ) + (∑' e : ℕ, a (e+1) * u^(e+1)) = ∑' e : ℕ, a e * u^e := by
    have h := Summable.sum_add_tsum_nat_add 1 hsum
    simp only [Finset.sum_range_one, h0, pow_zero, mul_one] at h
    exact h
  have hraw2 : (1 + (c₁+c₂)*u) + (∑' e : ℕ, a (e+2) * u^(e+2)) = ∑' e : ℕ, a e * u^e := by
    have h := Summable.sum_add_tsum_nat_add 2 hsum
    rw [Finset.sum_range_succ, Finset.sum_range_one] at h
    simp only [h0, h1, pow_zero, pow_one, mul_one] at h
    exact h
  -- Summability of the shifted sequences appearing in the defect.
  have hA2s : Summable (fun e : ℕ => a (e+2) * u^(e+2)) := (summable_nat_add_iff 2).mpr hsum
  have hB0s : Summable (fun e : ℕ => a (e+1) * u^(e+1)) := (summable_nat_add_iff 1).mpr hsum
  have hBs : Summable (fun e : ℕ => a (e+1) * u^(e+2)) := by
    have h : (fun e : ℕ => a (e+1) * u^(e+2)) = (fun e : ℕ => (a (e+1) * u^(e+1)) * u) := by
      funext e; rw [pow_succ]; ring
    rw [h]; exact hB0s.mul_right u
  have hCs : Summable (fun e : ℕ => a e * u^(e+2)) := by
    have h : (fun e : ℕ => a e * u^(e+2)) = (fun e : ℕ => (a e * u^e) * u^2) := by
      funext e; rw [pow_add]; ring
    rw [h]; exact hsum.mul_right (u^2)
  -- The defect sequence vanishes identically, so its total sum is `0`.
  have hz : (∑' e : ℕ,
      (a (e+2)*u^(e+2) - (c₁+c₂)*(a (e+1)*u^(e+2)) + (c₁*c₂)*(a e*u^(e+2)))) = 0 := by
    have hzero : ∀ e : ℕ,
        (a (e+2)*u^(e+2) - (c₁+c₂)*(a (e+1)*u^(e+2)) + (c₁*c₂)*(a e*u^(e+2))) = 0 := by
      intro e; rw [hrec e]; ring
    rw [tsum_congr hzero, tsum_zero]
  -- Linearity: expand the total sum of the defect.
  have hexp : (∑' e : ℕ,
        (a (e+2)*u^(e+2) - (c₁+c₂)*(a (e+1)*u^(e+2)) + (c₁*c₂)*(a e*u^(e+2))))
      = (∑' e, a (e+2)*u^(e+2)) - (c₁+c₂) * (∑' e, a (e+1)*u^(e+2))
        + (c₁*c₂) * (∑' e, a e*u^(e+2)) := by
    have hsplit : (∑' e : ℕ,
          (a (e+2)*u^(e+2) - (c₁+c₂)*(a (e+1)*u^(e+2)) + (c₁*c₂)*(a e*u^(e+2))))
        = (∑' e, (a (e+2)*u^(e+2) - (c₁+c₂)*(a (e+1)*u^(e+2))))
          + (∑' e, (c₁*c₂)*(a e*u^(e+2))) :=
      Summable.tsum_add (f := fun e => a (e+2)*u^(e+2) - (c₁+c₂)*(a (e+1)*u^(e+2)))
        (g := fun e => (c₁*c₂)*(a e*u^(e+2)))
        (hA2s.sub (hBs.mul_left (c₁+c₂))) (hCs.mul_left (c₁*c₂))
    have hsub : (∑' e, (a (e+2)*u^(e+2) - (c₁+c₂)*(a (e+1)*u^(e+2))))
        = (∑' e, a (e+2)*u^(e+2)) - (∑' e, (c₁+c₂)*(a (e+1)*u^(e+2))) :=
      Summable.tsum_sub (f := fun e => a (e+2)*u^(e+2))
        (g := fun e => (c₁+c₂)*(a (e+1)*u^(e+2))) hA2s (hBs.mul_left (c₁+c₂))
    have hm1 : (∑' e, (c₁+c₂)*(a (e+1)*u^(e+2))) = (c₁+c₂) * (∑' e, a (e+1)*u^(e+2)) :=
      tsum_mul_left (f := fun e => a (e+1)*u^(e+2))
    have hm2 : (∑' e, (c₁*c₂)*(a e*u^(e+2))) = (c₁*c₂) * (∑' e, a e*u^(e+2)) :=
      tsum_mul_left (f := fun e => a e*u^(e+2))
    rw [hsplit, hsub, hm1, hm2]
  -- Evaluate the three shifted sums.
  have hA2 : (∑' e, a (e+2)*u^(e+2)) = (∑' e, a e*u^e) - (1 + (c₁+c₂)*u) := by
    rw [eq_sub_iff_add_eq, add_comm]; exact hraw2
  have hB1 : (∑' e, a (e+1)*u^(e+2)) = u * ((∑' e, a e*u^e) - 1) := by
    have hcongr : (∑' e, a (e+1)*u^(e+2)) = (∑' e, u * (a (e+1)*u^(e+1))) := by
      apply tsum_congr; intro e; rw [pow_succ]; ring
    rw [hcongr]
    have hb : (∑' e, a (e+1)*u^(e+1)) = (∑' e, a e*u^e) - 1 := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hraw1
    rw [tsum_mul_left (f := fun e => a (e+1)*u^(e+1)), hb]
  have hC : (∑' e, a e*u^(e+2)) = (∑' e, a e*u^e) * u^2 := by
    have hcongr : (∑' e, a e*u^(e+2)) = (∑' e, (a e*u^e) * u^2) := by
      apply tsum_congr; intro e; rw [pow_add]; ring
    rw [hcongr]
    exact tsum_mul_right (f := fun e => a e*u^e) (a := u^2)
  -- Combine to the numerical identity.
  have hval : (∑' e, a e*u^e) - (1 + (c₁+c₂)*u) - (c₁+c₂) * (u * ((∑' e, a e*u^e) - 1))
      + (c₁*c₂) * ((∑' e, a e*u^e) * u^2) = 0 := by
    rw [hexp] at hz
    rw [hA2, hB1, hC] at hz
    exact hz
  have key : (∑' e, a e*u^e) * (1 - (c₁+c₂)*u + (c₁*c₂)*u^2)
      = 1 + ((∑' e, a e*u^e) - (1 + (c₁+c₂)*u) - (c₁+c₂) * (u * ((∑' e, a e*u^e) - 1))
        + (c₁*c₂) * ((∑' e, a e*u^e) * u^2)) := by ring
  rw [key, hval, add_zero]

end Work.FIArea6Hecke.R
