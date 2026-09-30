import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset


private lemma arith_le_geom_deg {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hS : 0 < ∑ i, d i) :
    (∑ i, d i) / n ≤ ∏ i, (d i) ^ (d i / (∑ i, d i)) := by
  set S := ∑ i, d i with hSdef
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hSn : 0 < S / (n:ℝ) := div_pos hS hn'
  have hj := Real.convexOn_mul_log.map_sum_le (t := (Finset.univ : Finset (Fin n)))
      (w := fun _ : Fin n => (1:ℝ)/(n:ℝ)) (p := d)
      (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
      (fun i _ => by simpa only [Set.mem_Ici] using hd i)
  simp only [smul_eq_mul] at hj
  have hsum1 : (∑ i : Fin n, (1:ℝ)/(n:ℝ) * d i) = S / (n:ℝ) := by
    rw [hSdef, Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _; ring
  have hsum2 : (∑ i : Fin n, (1:ℝ)/(n:ℝ) * (d i * Real.log (d i)))
      = (∑ i : Fin n, d i * Real.log (d i)) / (n:ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hsum1, hsum2] at hj
  have hnn : (n:ℝ) ≠ 0 := ne_of_gt hn'
  have h2 : S * Real.log (S/(n:ℝ)) ≤ ∑ i : Fin n, d i * Real.log (d i) := by
    have h1 := mul_le_mul_of_nonneg_right hj (le_of_lt hn')
    have heq : ((S/(n:ℝ)) * Real.log (S/(n:ℝ))) * (n:ℝ) = S * Real.log (S/(n:ℝ)) := by
      rw [mul_assoc, mul_comm (Real.log (S/(n:ℝ))) (n:ℝ), ← mul_assoc, div_mul_cancel₀ S hnn]
    rw [heq, div_mul_cancel₀ _ hnn] at h1
    exact h1
  have hsum3 : (∑ i : Fin n, (d i/S) * Real.log (d i)) = (∑ i : Fin n, d i * Real.log (d i))/S := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _; ring
  have hlog : Real.log (S/(n:ℝ)) ≤ ∑ i : Fin n, (d i / S) * Real.log (d i) := by
    rw [hsum3, le_div_iff₀ hS]
    calc Real.log (S/(n:ℝ)) * S = S * Real.log (S/(n:ℝ)) := by ring
      _ ≤ ∑ i : Fin n, d i * Real.log (d i) := h2
  have e2 : Real.exp (∑ i : Fin n, (d i/S) * Real.log (d i)) = ∏ i, (d i) ^ (d i/S) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rcases eq_or_lt_of_le (hd i) with h | h
    · rw [← h]; simp
    · rw [Real.rpow_def_of_pos h]; congr 1; ring
  rw [← e2, ← Real.exp_log hSn]
  exact Real.exp_le_exp.mpr hlog

private lemma walk_to_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hsym : A.transpose = A) (S : ℝ)
    (hS : S = ∑ i, ∑ j, A i j) (hSne : S ≠ 0) (k : ℕ) :
    (∑ i, ((∑ j, A i j)/S) * ((A^k).mulVec 1) i) = (∑ i, ∑ j, (A^(k+1)) i j)/S := by
  have hdiv : (∑ i, ((∑ j, A i j)/S) * ((A^k).mulVec 1) i)
      = (∑ i, (∑ j, A i j) * ((A^k).mulVec 1) i)/S := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hdiv]
  congr 1
  have hd_eq : A.mulVec 1 = fun i => ∑ j, A i j := by
    ext i; simp [Matrix.mulVec, dotProduct_one]
  have h1 : (∑ i, (∑ j, A i j) * ((A^k).mulVec 1) i)
      = (A.mulVec 1) ⬝ᵥ ((A^k).mulVec 1) := by
    rw [hd_eq]; rfl
  have h2 : (A.mulVec 1) ⬝ᵥ ((A^k).mulVec 1)
      = ((A^k).transpose.mulVec (A.mulVec 1)) ⬝ᵥ 1 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  rw [h1, h2]
  have htr : (A^k).transpose = A^k := by rw [Matrix.transpose_pow, hsym]
  rw [htr, Matrix.mulVec_mulVec, ← pow_succ]
  simp only [dotProduct_one, Matrix.mulVec, Pi.one_apply, mul_one]




open Finset

private lemma contraction_A {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hsym : A.transpose = A)
    (hnn : ∀ i j, 0 ≤ A i j) (S : ℝ) (hS : S = ∑ i, ∑ j, A i j) (hSpos : 0 < S)
    (h : Fin n → ℝ) (hh : ∀ i, 0 ≤ h i) :
    (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S)) * (∏ i, h i ^ ((∑ j, A i j)/S))
      ≤ ∏ i, (A.mulVec h) i ^ ((∑ j, A i j)/S) := by
  have hs : ∀ i j, A i j = A j i := by
    intro i j
    have h1 := congrFun (congrFun hsym j) i
    simpa [Matrix.transpose_apply] using h1
  have hd : ∀ i, 0 ≤ ∑ j, A i j := fun i => Finset.sum_nonneg (fun j _ => hnn i j)
  have hπ0 : ∀ i, 0 ≤ (∑ j, A i j)/S := fun i => div_nonneg (hd i) (le_of_lt hSpos)
  have hAi0 : ∀ i, (∑ j, A i j) = 0 → ∀ j, A i j = 0 := by
    intro i hz j
    have h2 : A i j ≤ ∑ j', A i j' := Finset.single_le_sum (fun j' _ => hnn i j') (Finset.mem_univ j)
    rw [hz] at h2
    exact le_antisymm h2 (hnn i j)
  have key : ∀ i, (∑ j, A i j) * (∏ j, h j ^ (A i j/(∑ j, A i j))) ≤ (A.mulVec h) i := by
    intro i
    rcases eq_or_lt_of_le (hd i) with hd0 | hd0
    · have hAi := hAi0 i hd0.symm
      have hL : (∑ j, A i j) * (∏ j, h j ^ (A i j/(∑ j, A i j))) = 0 := by
        rw [← hd0, zero_mul]
      have hR : (A.mulVec h) i = 0 := by
        simp only [Matrix.mulVec, dotProduct, hAi, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
      rw [hL, hR]
    · have hAM : (∏ j, h j ^ (A i j/(∑ j, A i j))) ≤ ∑ j, (A i j/(∑ j, A i j)) * h j :=
        Real.geom_mean_le_arith_mean_weighted Finset.univ (fun j => A i j/(∑ j, A i j)) h
          (fun j _ => div_nonneg (hnn i j) (le_of_lt hd0))
          (by rw [← Finset.sum_div]; exact div_self (ne_of_gt hd0)) (fun j _ => hh j)
      calc (∑ j, A i j) * (∏ j, h j ^ (A i j/(∑ j, A i j)))
          ≤ (∑ j, A i j) * (∑ j, (A i j/(∑ j, A i j)) * h j) :=
              le_of_sub_nonneg (by rw [← mul_sub]; exact mul_nonneg (le_of_lt hd0) (sub_nonneg.mpr hAM))
        _ = (A.mulVec h) i := by
              rw [Finset.mul_sum]
              simp only [Matrix.mulVec, dotProduct]
              apply Finset.sum_congr rfl; intro j _
              rw [← mul_assoc, mul_comm (∑ j', A i j') (A i j / (∑ j', A i j')),
                  div_mul_cancel₀ (A i j) (ne_of_gt hd0)]
  have step1 : ∏ i, ((∑ j, A i j) * (∏ j, h j ^ (A i j/(∑ j, A i j)))) ^ ((∑ j, A i j)/S)
      ≤ ∏ i, (A.mulVec h) i ^ ((∑ j, A i j)/S) := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Real.rpow_nonneg (mul_nonneg (hd i) (Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (hh j) _))) _
    · intro i _
      exact Real.rpow_le_rpow
        (mul_nonneg (hd i) (Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (hh j) _))) (key i) (hπ0 i)
  have hterm : ∀ i j, (A i j/(∑ j', A i j')) * ((∑ j', A i j')/S) = A i j/S := by
    intro i j
    rcases eq_or_lt_of_le (hd i) with hz | hz
    · have hAi := hAi0 i hz.symm
      rw [hAi j, ← hz]; simp
    · field_simp
  have hsum_eq : ∀ j, (∑ i, (A i j/(∑ j', A i j')) * ((∑ j', A i j')/S)) = (∑ j', A j j')/S := by
    intro j
    rw [Finset.sum_congr rfl (fun i _ => hterm i j), ← Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl; intro i _; rw [hs i j]
  have hA : ∏ i, ((∑ j, A i j) * (∏ j, h j ^ (A i j/(∑ j, A i j)))) ^ ((∑ j, A i j)/S)
      = (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S))
        * (∏ i, (∏ j, h j ^ (A i j/(∑ j, A i j))) ^ ((∑ j, A i j)/S)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro i _
    exact Real.mul_rpow (hd i) (Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (hh j) _))
  have hB : ∏ i, (∏ j, h j ^ (A i j/(∑ j, A i j))) ^ ((∑ j, A i j)/S)
      = ∏ j, h j ^ (∑ i, (A i j/(∑ j', A i j')) * ((∑ j', A i j')/S)) := by
    have e : ∏ i, (∏ j, h j ^ (A i j/(∑ j, A i j))) ^ ((∑ j, A i j)/S)
        = ∏ i, ∏ j, h j ^ ((A i j/(∑ j, A i j)) * ((∑ j, A i j)/S)) := by
      apply Finset.prod_congr rfl; intro i _
      rw [← Real.finsetProd_rpow _ _ (fun j _ => Real.rpow_nonneg (hh j) _)]
      apply Finset.prod_congr rfl; intro j _
      rw [← Real.rpow_mul (hh j)]
    rw [e, Finset.prod_comm]
    apply Finset.prod_congr rfl; intro j _
    rw [Real.rpow_sum_of_nonneg (hh j)
      (fun i _ => mul_nonneg (div_nonneg (hnn i j) (hd i)) (div_nonneg (hd i) (le_of_lt hSpos)))]
  have hC : ∏ j, h j ^ (∑ i, (A i j/(∑ j', A i j')) * ((∑ j', A i j')/S))
      = ∏ i, h i ^ ((∑ j, A i j)/S) := by
    apply Finset.prod_congr rfl; intro j _
    rw [hsum_eq j]
  calc (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S)) * (∏ i, h i ^ ((∑ j, A i j)/S))
      = (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S))
        * ∏ j, h j ^ (∑ i, (A i j/(∑ j', A i j')) * ((∑ j', A i j')/S)) := by rw [hC]
    _ = (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S))
        * (∏ i, (∏ j, h j ^ (A i j/(∑ j, A i j))) ^ ((∑ j, A i j)/S)) := by rw [hB]
    _ = ∏ i, ((∑ j, A i j) * (∏ j, h j ^ (A i j/(∑ j, A i j)))) ^ ((∑ j, A i j)/S) := hA.symm
    _ ≤ ∏ i, (A.mulVec h) i ^ ((∑ j, A i j)/S) := step1


private lemma main_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hsym : A.transpose = A)
    (hnn : ∀ i j, 0 ≤ A i j) (S : ℝ) (hS : S = ∑ i, ∑ j, A i j) (hSpos : 0 < S) (k : ℕ) :
    ∀ h : Fin n → ℝ, (∀ i, 0 ≤ h i) →
      (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S))^k * (∏ i, h i ^ ((∑ j, A i j)/S))
        ≤ ∑ i, ((∑ j, A i j)/S) * ((A^k).mulVec h) i := by
  intro h
  induction k generalizing h with
  | zero =>
      intro hh
      rw [pow_zero, one_mul, pow_zero, Matrix.one_mulVec]
      exact Real.geom_mean_le_arith_mean_weighted Finset.univ (fun i => (∑ j, A i j)/S) h
        (fun i _ => div_nonneg (Finset.sum_nonneg (fun j _ => hnn i j)) (le_of_lt hSpos))
        (by rw [← Finset.sum_div, ← hS, div_self (ne_of_gt hSpos)]) (fun i _ => hh i)
  | succ k ih =>
      intro hh
      have hmat : (A^(k+1)).mulVec h = (A^k).mulVec (A.mulVec h) := by
        rw [pow_succ, ← Matrix.mulVec_mulVec]
      rw [hmat, pow_succ]
      have hAh : ∀ i, 0 ≤ (A.mulVec h) i := fun i => by
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_nonneg (fun j _ => mul_nonneg (hnn i j) (hh j))
      have ih' := ih (A.mulVec h) hAh
      have hc := contraction_A A hsym hnn S hS hSpos h hh
      have hG0 : 0 ≤ (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S))^k :=
        pow_nonneg (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => hnn i j)) _)) k
      calc (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S))^k * (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S))
              * (∏ i, h i ^ ((∑ j, A i j)/S))
          = (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S))^k
              * ((∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S)) * (∏ i, h i ^ ((∑ j, A i j)/S))) := by ring
        _ ≤ (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S))^k
              * (∏ i, (A.mulVec h) i ^ ((∑ j, A i j)/S)) :=
              le_of_sub_nonneg (by rw [← mul_sub]; exact mul_nonneg hG0 (sub_nonneg.mpr hc))
        _ ≤ ∑ i, ((∑ j, A i j)/S) * ((A^k).mulVec (A.mulVec h)) i := ih'

/-- **Mulholland–Smith (1959) / Blakley–Roy (1965)**: Sidorenko's property for paths. For a symmetric matrix `A` with nonnegative entries, the total weight `1ᵀAᵐ 1` of walks of length `m` is at least `(1ᵀA1)^m / n^{m-1}`. -/
theorem br_path {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℝ}
    (hsym : A.transpose = A) (hnn : ∀ i j, 0 ≤ A i j) (m : ℕ) :
    (∑ i, ∑ j, (A ^ m) i j) ≥ ((∑ i, ∑ j, A i j)) ^ m / (n : ℝ) ^ (m - 1) := by
  set S := ∑ i, ∑ j, A i j with hSdef
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hL : (∑ i, ∑ j, (A ^ 0) i j) = (n : ℝ) := by
      rw [pow_zero]
      simp [Matrix.one_apply]
    have hR : S ^ 0 / (n : ℝ) ^ (0 - 1) = 1 := by
      rw [pow_zero, show (0:ℕ) - 1 = 0 from rfl, pow_zero, div_one]
    rw [hL, hR]
    exact_mod_cast hn
  · have hSnn : 0 ≤ S := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j))
    rcases eq_or_lt_of_le hSnn with hS0 | hSpos
    · have hA0 : A = 0 := by
        ext i j
        rw [Matrix.zero_apply]
        have h1 : A i j ≤ S := by
          rw [hSdef]
          calc A i j ≤ ∑ j, A i j := Finset.single_le_sum (fun j _ => hnn i j) (Finset.mem_univ j)
            _ ≤ ∑ i, ∑ j, A i j := Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hnn i j)) (Finset.mem_univ i)
        rw [← hS0] at h1
        exact le_antisymm h1 (hnn i j)
      subst hA0
      have hL : (∑ i, ∑ j, ((0 : Matrix (Fin n) (Fin n) ℝ) ^ m) i j) = 0 := by
        rw [zero_pow (by omega)]; simp
      have hR : ((∑ i, ∑ j, (0 : Matrix (Fin n) (Fin n) ℝ) i j)) ^ m / (n : ℝ) ^ (m - 1) = 0 := by
        rw [show (∑ i, ∑ j, (0 : Matrix (Fin n) (Fin n) ℝ) i j) = 0 from by simp,
          zero_pow (by omega), zero_div]
      rw [hL, hR]
    · have h1 := main_step A hsym hnn S hSdef.symm hSpos (m - 1) (1 : Fin n → ℝ)
        (fun i => by rw [Pi.one_apply]; exact zero_le_one)
      rw [walk_to_pow A hsym S hSdef.symm (ne_of_gt hSpos) (m-1)] at h1
      simp only [Pi.one_apply, Real.one_rpow, Finset.prod_const_one, mul_one] at h1
      rw [show m - 1 + 1 = m from Nat.sub_add_cancel hmpos] at h1
      have h2 := arith_le_geom_deg hn (fun i => ∑ j, A i j) (fun i => Finset.sum_nonneg (fun j _ => hnn i j))
        (hSdef.symm ▸ hSpos)
      have h2pow : (S/(n:ℝ))^(m-1) ≤ (∏ i, (∑ j, A i j) ^ ((∑ j, A i j)/S))^(m-1) :=
        pow_le_pow_left₀ (div_nonneg hSnn (Nat.cast_nonneg n)) h2 (m-1)
      have h3 : (S/(n:ℝ))^(m-1) ≤ (∑ i, ∑ j, (A^m) i j)/S := le_trans h2pow h1
      have h4 : S * (S/(n:ℝ))^(m-1) ≤ ∑ i, ∑ j, (A^m) i j := by
        have := (le_div_iff₀ hSpos).mp h3
        rwa [mul_comm] at this
      have h5 : S * (S/(n:ℝ))^(m-1) = S^m/(n:ℝ)^(m-1) := by
        rw [div_pow, ← mul_div_assoc, show S * S^(m-1) = S^m from by
          rw [← pow_succ', Nat.sub_add_cancel hmpos]]
      rw [h5] at h4
      exact h4

end Work.BMF
