import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CycLevel

/-- **An arithmetic fact about `q`-parts.**  Let `q` be a prime, `e > 0`, and let `O, f, H, m` be
positive naturals with `f ∣ O`, `f ∣ H`, `q ^ e * H ∣ m` and — this is the hypothesis encoding
"`O` has the full `q`-part of `m`" — `q ^ j ∣ m → q ^ j ∣ O` for every `j`.  Then `q ^ e ∣ O / f`.

Proof sketch: put `d := (Nat.factorization f) q` (so `f = q ^ d * f'` with `q ∤ f'`).  Then
`q ^ (e + d) ∣ q ^ e * H ∣ m`, so `q ^ (e + d) ∣ O` by the last hypothesis; and `f' ∣ f ∣ O` with
`Nat.Coprime (q ^ (e + d)) f'`, so `q ^ (e + d) * f' = q ^ e * f ∣ O`.  As `f ∣ O`, write
`O = (O / f) * f`; cancelling `f > 0` gives `q ^ e ∣ O / f`.
Useful API: `Nat.factorization`, `Nat.Prime.pow_dvd_iff_le_factorization`,
`Nat.factorization_mul`, `Nat.Coprime.pow_left`, `Nat.Coprime.mul_dvd_of_dvd_of_dvd`,
`Nat.mul_dvd_mul_iff_right`, `Nat.div_mul_cancel`, `Nat.dvd_div_iff_mul_dvd`. -/
theorem div_dvd_of_qpow_mul_dvd {q e O f H m : ℕ} (hq : q.Prime) (he : 0 < e)
    (hO : 0 < O) (hf : 0 < f) (h1 : f ∣ O) (h2 : f ∣ H) (h3 : q ^ e * H ∣ m)
    (h4 : ∀ j : ℕ, q ^ j ∣ m → q ^ j ∣ O) : q ^ e ∣ O / f := by
  -- Decompose `f = q ^ d * f'` with `d` the `q`-adic valuation of `f` and `q ∤ f'`.
  set d := f.factorization q with hd
  have hfne : f ≠ 0 := hf.ne'
  have hqd : q ^ d ∣ f := (hq.pow_dvd_iff_le_factorization hfne).mpr le_rfl
  set f' := f / q ^ d with hf'_def
  have hf_eq : f = q ^ d * f' := by
    rw [hf'_def, mul_comm]
    exact (Nat.div_mul_cancel hqd).symm
  have hqndvd : ¬ q ∣ f' := by
    intro hdiv
    have h1' : q ^ (d + 1) ∣ f := by
      rw [pow_succ, hf_eq]
      exact Nat.mul_dvd_mul_left (q ^ d) hdiv
    have := (hq.pow_dvd_iff_le_factorization hfne).mp h1'
    omega
  -- `q ^ (e + d)` and `f'` are coprime.
  have hcop : Nat.Coprime (q ^ (e + d)) f' :=
    Nat.Coprime.pow_left (e + d) ((hq.coprime_iff_not_dvd).mpr hqndvd)
  -- `q ^ (e + d) ∣ m`, hence `∣ O` by `h4`.
  have hqdvdm : q ^ (e + d) ∣ m := by
    have hqe : q ^ e * q ^ d ∣ q ^ e * H := Nat.mul_dvd_mul_left (q ^ e) (Nat.dvd_trans hqd h2)
    rw [← pow_add] at hqe
    exact hqe.trans h3
  have hdivO : q ^ (e + d) ∣ O := h4 (e + d) hqdvdm
  -- `f' ∣ f ∣ O`, so the coprime product divides `O`.
  have hf'dvdO : f' ∣ O := Nat.dvd_trans (Nat.div_dvd_of_dvd hqd) h1
  have hmul : q ^ (e + d) * f' ∣ O := hcop.mul_dvd_of_dvd_of_dvd hdivO hf'dvdO
  have hprod : q ^ e * f ∣ O := by
    rw [hf_eq, ← mul_assoc, ← pow_add]
    exact hmul
  -- Cancel `f` from `q ^ e * f ∣ O = (O / f) * f`.
  have key : q ^ e * f ∣ O / f * f := by rw [Nat.div_mul_cancel h1]; exact hprod
  exact (Nat.mul_dvd_mul_iff_right hf).mp key

end Work.SSGRoute.CycLevel
