import Mathlib

namespace Work.LT

/-- **Pointwise factor bound.**  For `i < j ≤ k` the `i`-th factor of the two Gaussian products
satisfies `2^k - 2^i ≤ 2^{k-j+1} · (2^j - 2^i)`.

Indeed `2^j - 2^i ≥ 2^j - 2^{j-1} = 2^{j-1}`, so
`2^{k-j+1} · (2^j - 2^i) ≥ 2^{k-j+1} · 2^{j-1} = 2^k ≥ 2^k - 2^i`. -/
theorem gb_gaussian_factor_le (i j k : ℕ) (hij : i < j) (hjk : j ≤ k) :
    (2:ℕ)^k - 2^i ≤ 2^(k-j+1) * (2^j - 2^i) := by
  have hj1 : 1 ≤ j := by omega
  have h2 : (2:ℕ)^(j-1) ≤ 2^j - 2^i := by
    have hle : (2:ℕ)^i ≤ 2^(j-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow : (2:ℕ)^j = 2^(j-1) * 2 := by
      have : (2:ℕ)^j = 2^((j-1)+1) := by congr 1; omega
      rw [this, pow_succ]
    have hval : (2:ℕ)^j - 2^(j-1) = 2^(j-1) := by
      rw [hpow]; omega
    rw [← hval]
    exact Nat.sub_le_sub_left hle (2^j)
  calc (2:ℕ)^k - 2^i ≤ 2^k := Nat.sub_le _ _
    _ = 2^(k-j+1) * 2^(j-1) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2^(k-j+1) * (2^j - 2^i) := Nat.mul_le_mul_left _ h2

theorem gb_gaussian_prod_le {j k : ℕ} (hj : j ≤ k) :
    (∏ i : Fin j, ((2:ℕ)^k - 2^(i:ℕ))) ≤
      2^(j*(k-j)+j+2) * (∏ i : Fin j, ((2:ℕ)^j - 2^(i:ℕ))) := by
  have hfactor : ∀ i : Fin j, (2:ℕ)^k - 2^(i:ℕ) ≤ 2^(k-j+1) * (2^j - 2^(i:ℕ)) :=
    fun i => gb_gaussian_factor_le (i:ℕ) j k i.isLt hj
  have hprod : (∏ i : Fin j, ((2:ℕ)^k - 2^(i:ℕ))) ≤
      ∏ i : Fin j, (2^(k-j+1) * (2^j - 2^(i:ℕ))) :=
    Finset.prod_le_prod (fun i _ => hfactor i)
  have hR : (∏ i : Fin j, (2^(k-j+1) * (2^j - 2^(i:ℕ))))
      = 2^((k-j+1)*j) * (∏ i : Fin j, ((2:ℕ)^j - 2^(i:ℕ))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    congr 1
    rw [Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hexp : (k-j+1)*j = j*(k-j)+j := by
    have h1 : k-j+1 = (k-j)+1 := by omega
    calc (k-j+1)*j = ((k-j)+1)*j := by rw [h1]
      _ = (k-j)*j + 1*j := by rw [Nat.add_mul]
      _ = (k-j)*j + j := by rw [Nat.one_mul]
      _ = j*(k-j)+j := by rw [Nat.mul_comm]
  have hfinal : 2^((k-j+1)*j) * (∏ i : Fin j, ((2:ℕ)^j - 2^(i:ℕ)))
      ≤ 2^(j*(k-j)+j+2) * (∏ i : Fin j, ((2:ℕ)^j - 2^(i:ℕ))) := by
    apply Nat.mul_le_mul_right
    rw [hexp]
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  calc (∏ i : Fin j, ((2:ℕ)^k - 2^(i:ℕ)))
      ≤ ∏ i : Fin j, (2^(k-j+1) * (2^j - 2^(i:ℕ))) := hprod
    _ = 2^((k-j+1)*j) * (∏ i : Fin j, ((2:ℕ)^j - 2^(i:ℕ))) := hR
    _ ≤ 2^(j*(k-j)+j+2) * (∏ i : Fin j, ((2:ℕ)^j - 2^(i:ℕ))) := hfinal

end Work.LT
