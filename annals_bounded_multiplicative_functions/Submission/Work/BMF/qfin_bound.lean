import Mathlib
import Submission.Work.BMF.adi_const

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset

/-- Each factor `qj a b m = a^m - b^m` of the modulus is bounded by `a^m`. -/
lemma qj_cast_le (a b m : ℕ) : ((qj a b m : ℕ) : ℝ) ≤ (a : ℝ) ^ m := by
  have h : qj a b m ≤ a ^ m := by
    unfold qj
    exact Nat.sub_le _ _
  calc ((qj a b m : ℕ) : ℝ) ≤ ((a ^ m : ℕ) : ℝ) := by exact_mod_cast h
    _ = (a : ℝ) ^ m := by push_cast; ring

/-- The modulus product `qprod k a b = ∏_{m=1}^{k} (a^m - b^m)` is at most `Z^{k·k}` when
`a ≤ Z` and `1 ≤ Z`. -/
lemma qprod_le (k a b : ℕ) {Z : ℝ} (hZ1 : 1 ≤ Z) (ha : (a : ℝ) ≤ Z) :
    ((qprod k a b : ℕ) : ℝ) ≤ Z ^ (k * k) := by
  rw [qprod, Nat.cast_prod]
  have hterm : ∀ m ∈ Finset.Icc 1 k, ((qj a b m : ℕ) : ℝ) ≤ Z ^ k := by
    intro m hm
    have hmk : m ≤ k := (Finset.mem_Icc.mp hm).2
    have h1 := qj_cast_le a b m
    have h2 : (a : ℝ) ^ m ≤ Z ^ m := pow_le_pow_left₀ (by positivity) ha m
    have h3 : Z ^ m ≤ Z ^ k := pow_le_pow_right₀ hZ1 hmk
    linarith
  have hnn : ∀ m ∈ Finset.Icc 1 k, (0:ℝ) ≤ ((qj a b m : ℕ) : ℝ) := by
    intro m hm; positivity
  calc ∏ m ∈ Finset.Icc 1 k, ((qj a b m : ℕ) : ℝ)
      ≤ ∏ m ∈ Finset.Icc 1 k, Z ^ k := Finset.prod_le_prod₀ hnn hterm
    _ = (Z ^ k) ^ (Finset.Icc 1 k).card := Finset.prod_const _
    _ = Z ^ (k * k) := by rw [Nat.card_Icc]; simp [pow_mul]

/-- The final modulus `Qfin` is bounded by `Z^{K₀}` whenever `Z ≥ 2` dominates the two bases
`a₁`, `a₂`. -/
theorem qfin_bound (k : ℕ) (a1 b1 a2 b2 : ℕ) {Z : ℝ} (hZ : 2 ≤ Z)
    (ha1 : (a1 : ℝ) ≤ Z) (ha2 : (a2 : ℝ) ≤ Z) :
    ((Qfin k a1 b1 a2 b2 : ℕ) : ℝ) ≤ Z ^ (K0c k) := by
  have hZ1 : (1 : ℝ) ≤ Z := by linarith
  have hq1 := qprod_le k a1 b1 hZ1 ha1
  have hq2 := qprod_le k a2 b2 hZ1 ha2
  -- the factorial factor
  have hf : ((k.factorial : ℕ) : ℝ) ^ (k + 1) ≤ Z ^ (k.factorial * (k + 1)) := by
    have hbase : ((k.factorial : ℕ) : ℝ) ≤ Z ^ (k.factorial) := by
      have h1 : k.factorial ≤ 2 ^ k.factorial := le_of_lt Nat.lt_two_pow_self
      have h2 : ((2:ℝ) ^ k.factorial) ≤ Z ^ k.factorial :=
        pow_le_pow_left₀ (by norm_num) hZ k.factorial
      calc ((k.factorial : ℕ) : ℝ) ≤ ((2 ^ k.factorial : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (2:ℝ) ^ k.factorial := by push_cast; ring
        _ ≤ Z ^ k.factorial := h2
    calc ((k.factorial : ℕ) : ℝ) ^ (k+1) ≤ (Z ^ k.factorial) ^ (k+1) :=
          pow_le_pow_left₀ (by positivity) hbase (k+1)
      _ = Z ^ (k.factorial * (k+1)) := by rw [pow_mul]
  have hexp : (Z ^ (k.factorial * (k+1)) * Z ^ (k*k) * Z ^ (k*k))
      = Z ^ (k.factorial * (k+1) + k*k + k*k) := by
    rw [← pow_add, ← pow_add]
  have hA_le : (((k.factorial : ℕ) : ℝ) ^ (k+1) * ((qprod k a1 b1 : ℕ) : ℝ)
      * ((qprod k a2 b2 : ℕ) : ℝ)) ≤ Z ^ (k.factorial * (k+1) + k*k + k*k) := by
    rw [← hexp]
    exact mul_le_mul (mul_le_mul hf hq1 (by positivity) (by positivity)) hq2
      (by positivity) (by positivity)
  -- arithmetic comparison of the exponents
  have hE : (k.factorial * (k + 1) + k * k + k * k) * (k + 1) ≤ K0c k := by
    unfold K0c
    have hcast : (((k.factorial * (k+1) + k*k + k*k) * (k+1) : ℕ) : ℝ)
        ≤ ((k * (k+1)^2 + 100 * (k+1)^2 * (k.factorial + 1) : ℕ) : ℝ) := by
      push_cast
      have hkf : (k : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial k
      have hk0 : (0:ℝ) ≤ k := by positivity
      have hK0 : (0:ℝ) ≤ (k.factorial : ℝ) := by positivity
      nlinarith [hkf, hk0, hK0]
    exact_mod_cast hcast
  have hQ : ((Qfin k a1 b1 a2 b2 : ℕ) : ℝ)
      = (((k.factorial : ℕ) : ℝ) ^ (k+1) * ((qprod k a1 b1 : ℕ) : ℝ)
         * ((qprod k a2 b2 : ℕ) : ℝ)) ^ (k+1) := by
    unfold Qfin
    push_cast
    ring
  calc ((Qfin k a1 b1 a2 b2 : ℕ) : ℝ)
      = (((k.factorial : ℕ) : ℝ) ^ (k+1) * ((qprod k a1 b1 : ℕ) : ℝ)
         * ((qprod k a2 b2 : ℕ) : ℝ)) ^ (k+1) := hQ
    _ ≤ (Z ^ (k.factorial * (k+1) + k*k + k*k)) ^ (k+1) :=
        pow_le_pow_left₀ (by positivity) hA_le (k+1)
    _ = Z ^ ((k.factorial * (k+1) + k*k + k*k) * (k+1)) := by rw [pow_mul]
    _ ≤ Z ^ (K0c k) := pow_le_pow_right₀ hZ1 hE

end Work.BMF
