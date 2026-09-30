import Mathlib
import Submission.Work.BMF.adi_const

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- A product of factorials of numbers `≤ k` divides `(k!)^{card}`. -/
lemma prod_factorial_dvd (k : ℕ) (s : Finset ℕ) (hs : ∀ i ∈ s, i ≤ k) :
    (∏ i ∈ s, i.factorial) ∣ (k.factorial) ^ s.card := by
  rw [← Finset.prod_const]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i hi => Nat.factorial_dvd_factorial (hs i hi)

/-- The final modulus `Qfin` is divisible by `D_m · m! · q_m` raised to the `m`-th power. -/
theorem qfin_dvd (k : ℕ) (a b a2 b2 : ℕ) (m : ℕ) (hm : m ∈ Finset.Icc 1 k)
    (hQ : 0 < Qfin k a b a2 b2) :
    (Dfac k m * m.factorial * qj a b m) ∣ (Qfin k a b a2 b2) ^ m := by
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hmk : m ≤ k := (Finset.mem_Icc.mp hm).2
  -- `D_m = ∏_{i=m+1}^{k} i!` divides `(k!)^{k-m}`, because `i! ∣ k!` for every `i ≤ k`.
  have hDfac : Dfac k m ∣ (k.factorial) ^ (k - m) := by
    unfold Dfac
    have h := prod_factorial_dvd k (Finset.Icc (m+1) k) (fun i hi => (Finset.mem_Icc.mp hi).2)
    have hcard : (Finset.Icc (m+1) k).card = k - m := by rw [Nat.card_Icc]; omega
    rw [hcard] at h
    exact h
  -- hence `D_m · m!` divides `(k!)^{k+1}`.
  have hmain1 : Dfac k m * m.factorial ∣ (k.factorial) ^ (k+1) := by
    have hmf : m.factorial ∣ (k.factorial)^1 := by
      simpa using Nat.factorial_dvd_factorial hmk
    have h := mul_dvd_mul hDfac hmf
    rw [← pow_add] at h
    refine dvd_trans h (pow_dvd_pow _ ?_)
    omega
  -- `q_m` is a factor of `qprod k a b = ∏_{i=1}^{k} q_i`.
  have hqj : qj a b m ∣ qprod k a b := by
    unfold qprod
    exact Finset.dvd_prod_of_mem (fun i => qj a b i) hm
  have hXY : Dfac k m * m.factorial * qj a b m ∣
      (k.factorial)^(k+1) * qprod k a b :=
    mul_dvd_mul hmain1 hqj
  -- the whole base `(k!)^{k+1} · qprod` divides every positive power of `Qfin`.
  have hbase : ∀ N : ℕ, 1 ≤ N →
      (k.factorial)^(k+1) * qprod k a b ∣
        ((k.factorial)^(k+1) * qprod k a b * qprod k a2 b2)^N := by
    intro N hN
    rw [mul_pow]
    exact dvd_mul_of_dvd_left
      (by simpa using pow_dvd_pow ((k.factorial)^(k+1) * qprod k a b) hN) _
  have hQfin : (k.factorial)^(k+1) * qprod k a b ∣ (Qfin k a b a2 b2)^m := by
    unfold Qfin
    rw [← pow_mul]
    exact hbase ((k+1) * m) (by nlinarith [hm1])
  exact dvd_trans hXY hQfin

end Work.BMF
