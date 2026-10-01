import Mathlib

namespace Work.LinnikBurgess

/-- Key refinement step: if `a = 1 + p^(j+m) * t`, then `p^(j+m+1) ∣ a^p - 1`
(provided `1 ≤ j`), obtained by expanding `(1+y)^p` binomially:
the `k = 1` term is `p * y` and every term with `k ≥ 2` already contains
`y^k` with `y = p^(j+m) * t`, hence a factor `p^(j+m+1)`. -/
lemma dvd_pow_step (p j m : ℕ) (hj : 1 ≤ j) (t : ℤ) :
    (p : ℤ) ^ (j + m + 1) ∣ (1 + (p : ℤ) ^ (j + m) * t) ^ p - 1 := by
  set y : ℤ := (p : ℤ) ^ (j + m) * t with hy
  have hbin : (1 + y)^p - 1 = ∑ k ∈ Finset.range p, y^(k+1) * ((p.choose (k+1) : ℕ) : ℤ) := by
    have h1 : (1 + y)^p = ∑ k ∈ Finset.range (p+1), y^k * ((p.choose k : ℕ) : ℤ) := by
      rw [add_comm 1 y, add_pow]
      simp
    rw [h1, Finset.sum_range_succ']
    simp
  rw [hbin]
  apply Finset.dvd_sum
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    have h0 : y^(0+1) * ((p.choose (0+1) : ℕ) : ℤ) = (p:ℤ)^(j+m+1) * t := by
      rw [hy, Nat.choose_one_right, pow_succ]
      ring
    rw [h0]
    exact dvd_mul_right _ _
  · have hk1 : 1 ≤ k := by omega
    have hm : 1 ≤ j + m := by omega
    have hle : j + m + 1 ≤ (j+m)*(k+1) := by
      have a : (j+m)*2 ≤ (j+m)*(k+1) := Nat.mul_le_mul_left _ (by omega)
      have b : j+m+1 ≤ (j+m)*2 := by omega
      omega
    have hdvd1 : (p:ℤ)^(j+m+1) ∣ y^(k+1) := by
      rw [hy]
      have h1 : (p:ℤ)^(j+m+1) ∣ ((p:ℤ)^(j+m))^(k+1) := by
        rw [← pow_mul]
        exact pow_dvd_pow _ hle
      have h2 : ((p:ℤ)^(j+m))^(k+1) ∣ ((p:ℤ)^(j+m) * t)^(k+1) :=
        pow_dvd_pow_of_dvd (dvd_mul_right _ _) _
      exact dvd_trans h1 h2
    exact dvd_mul_of_dvd_left hdvd1 _

/-- For every `m`, `p^(j+m) ∣ (1+p^j)^(p^m) - 1`, by induction on `m`
using the refinement step `dvd_pow_step`. -/
lemma ddGPowAux (p j : ℕ) (hj : 1 ≤ j) (m : ℕ) :
    (p : ℤ) ^ (j + m) ∣ (1 + (p : ℤ) ^ j) ^ (p ^ m) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      obtain ⟨t, ht⟩ := ih
      have hA : (1 + (p:ℤ)^j)^(p^m) = 1 + (p:ℤ)^(j+m) * t := by linarith
      have hstep := dvd_pow_step p j m hj t
      rw [pow_succ, pow_mul]
      rw [hA]
      exact hstep

/-- In `ZMod (p^e)`, the element `1 + p^j` has `(p^(e-j))`-th power equal to `1`
whenever `1 ≤ j ≤ e-1`. -/
theorem ddGPowEqOne {p e j : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hj : 1 ≤ j) (hje : j ≤ e - 1) :
    (((1 + p ^ j : ℕ) : ZMod (p ^ e)) ^ (p ^ (e - j)) = 1) := by
  have hdvd := ddGPowAux p j hj (e - j)
  have hje' : j + (e - j) = e := by omega
  rw [hje'] at hdvd
  have hX1 : (((1 + (p:ℤ)^j)^(p^(e-j)) : ℤ) : ZMod (p^e)) = 1 := by
    have h : (((1:ℤ) : ZMod (p^e)) = (((1 + (p:ℤ)^j)^(p^(e-j)) : ℤ) : ZMod (p^e))) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      rw [Int.natCast_pow]
      exact hdvd
    rw [← h]
    simp
  have hcast : ((1 + (p:ℤ)^j : ℤ) : ZMod (p^e)) ^ (p^(e-j)) = 1 := by
    rw [← Int.cast_pow]
    exact hX1
  have hbase : ((1 + (p:ℤ)^j : ℤ) : ZMod (p^e)) = ((1 + p^j : ℕ) : ZMod (p^e)) := by
    push_cast
    ring
  rwa [hbase] at hcast

end Work.LinnikBurgess
