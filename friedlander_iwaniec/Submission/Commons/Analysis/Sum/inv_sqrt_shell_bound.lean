import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Star

open scoped BigOperators

namespace Commons.Analysis.Sum

/-! ### Auxiliary lemmas -/

/-- `(X^(1/4))^2 = √X` for `X ≥ 0`. -/
private lemma rpow_quarter_sq {X : ℝ} (hX : 0 ≤ X) : (X ^ (1/4:ℝ))^2 = Real.sqrt X := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX, Real.sqrt_eq_rpow]
  norm_num

/-- `(X^(1/4))^4 = X` for `X ≥ 0`. -/
private lemma rpow_quarter_pow_four {X : ℝ} (hX : 0 ≤ X) : (X ^ (1/4:ℝ))^4 = X := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
  norm_num

/-- `(X^4)^(1/4) = X` for `X ≥ 0`. -/
private lemma pow_four_rpow_quarter {X : ℝ} (hX : 0 ≤ X) : (X ^ 4) ^ (1/4:ℝ) = X := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
  norm_num

/-- The fourth power of the iterated integer square root is at most `x`. -/
private lemma natSqrt_sqrt_pow_four_le (x : ℕ) : (Nat.sqrt (Nat.sqrt x)) ^ 4 ≤ x := by
  have h1 : (Nat.sqrt (Nat.sqrt x)) ^ 2 ≤ Nat.sqrt x := Nat.sqrt_le' _
  have h2 : (Nat.sqrt x) ^ 2 ≤ x := Nat.sqrt_le' _
  calc (Nat.sqrt (Nat.sqrt x)) ^ 4 = ((Nat.sqrt (Nat.sqrt x)) ^ 2) ^ 2 := by ring
    _ ≤ (Nat.sqrt x) ^ 2 := by nlinarith [h1]
    _ ≤ x := h2

/-- The iterated integer square root of `x` is at most the real fourth root of `x`. -/
private lemma natSqrt_sqrt_le_rpow_quarter (x : ℕ) :
    ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) ≤ (x : ℝ) ^ (1/4:ℝ) := by
  have h4 : (Nat.sqrt (Nat.sqrt x)) ^ 4 ≤ x := natSqrt_sqrt_pow_four_le x
  have hMnn : (0:ℝ) ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) := by positivity
  have hXnn : (0:ℝ) ≤ (x:ℝ) := by positivity
  have hcast : (((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ))^4 ≤ (x:ℝ) := by
    have h := Nat.cast_le (α := ℝ).mpr h4
    push_cast at h
    exact h
  calc ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ)
      = ((((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ))^4)^(1/4:ℝ) := (pow_four_rpow_quarter hMnn).symm
    _ ≤ (x:ℝ) ^ (1/4:ℝ) := Real.rpow_le_rpow (by positivity) hcast (by norm_num)

/-- For `0 ≤ c ≤ L`, the difference `L^4 - c^4` dominates `(L-c)·L^3`. -/
private lemma sub_pow_four_ge (L c : ℝ) (hL : 0 ≤ L) (hc : 0 ≤ c) (hcL : c ≤ L) :
    (L - c) * L ^ 3 ≤ L ^ 4 - c ^ 4 := by
  have key : L ^ 4 - c ^ 4 - (L - c) * L ^ 3 = c * (L - c) * (L^2 + L*c + c^2) := by ring
  have hnn : 0 ≤ c * (L - c) * (L^2 + L*c + c^2) := by
    have h1 : 0 ≤ L - c := by linarith
    have h2 : 0 ≤ L^2 + L*c + c^2 := by nlinarith [mul_nonneg hL hc, sq_nonneg L, sq_nonneg c]
    positivity
  linarith [key, hnn]

/-- `1/√(x+1) ≤ 2(√(x+1) - √x)` for `x ≥ 0`. -/
private lemma inv_sqrt_le_two_sub (x : ℝ) (hx : 0 ≤ x) :
    (Real.sqrt (x+1))⁻¹ ≤ 2 * (Real.sqrt (x+1) - Real.sqrt x) := by
  have ha2 : (Real.sqrt (x+1))^2 = x+1 := Real.sq_sqrt (by linarith)
  have hb2 : (Real.sqrt x)^2 = x := Real.sq_sqrt hx
  have ha0 : 0 < Real.sqrt (x+1) := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hba : Real.sqrt x ≤ Real.sqrt (x+1) := Real.sqrt_le_sqrt (by linarith)
  have hden : 0 < Real.sqrt (x+1) + Real.sqrt x := by linarith
  have hdiff : Real.sqrt (x+1) - Real.sqrt x = 1 / (Real.sqrt (x+1) + Real.sqrt x) := by
    rw [eq_div_iff hden.ne']
    nlinarith [ha2, hb2]
  have hmain : (1:ℝ) / Real.sqrt (x+1) ≤ 2 / (Real.sqrt (x+1) + Real.sqrt x) := by
    rw [div_le_div_iff₀ ha0 hden]
    linarith [hba]
  rw [hdiff]
  have h2 : 2 * (1 / (Real.sqrt (x+1) + Real.sqrt x)) = 2 / (Real.sqrt (x+1) + Real.sqrt x) := by ring
  rw [h2]
  simpa [one_div] using hmain

/-- Sum bound: `∑_{k<n} 1/√(k+1) ≤ 2√n`. -/
private lemma sum_range_inv_sqrt_succ_le (n : ℕ) :
    (∑ k ∈ Finset.range n, (Real.sqrt ((k : ℝ) + 1))⁻¹) ≤ 2 * Real.sqrt (n : ℝ) := by
  have hpt : ∀ k : ℕ,
      (Real.sqrt ((k:ℝ)+1))⁻¹ ≤ 2 * (Real.sqrt ((k:ℝ)+1) - Real.sqrt (k:ℝ)) := by
    intro k
    simpa using inv_sqrt_le_two_sub (k:ℝ) (by positivity)
  have hsub : (∑ k ∈ Finset.range n, (Real.sqrt ((k : ℝ) + 1))⁻¹)
      ≤ 2 * ∑ k ∈ Finset.range n, (Real.sqrt ((k:ℝ)+1) - Real.sqrt (k:ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hpt k)
  have htel : ∑ k ∈ Finset.range n, (Real.sqrt ((k:ℝ)+1) - Real.sqrt (k:ℝ))
      = Real.sqrt (n:ℝ) := by
    have h := Finset.sum_range_sub (fun k => Real.sqrt (k:ℝ)) n
    simpa using h
  linarith [hsub, htel]


/-- Reindexing: `∑_{c=1}^{M} g c = ∑_{k<M} g (M-k)`. -/
private lemma sum_Icc_eq_sum_range_sub (g : ℕ → ℝ) (M : ℕ) :
    ∑ c ∈ Finset.Icc 1 M, g c = ∑ k ∈ Finset.range M, g (M - k) := by
  have h := Finset.sum_Ico_reflect (fun j : ℕ => g (M - j)) 1 (m := M + 1) (n := M) (by omega)
  have hicc : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := by
    ext j; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have hz : M + 1 - (M + 1) = 0 := by omega
  have hz2 : M + 1 - 1 = M := by omega
  rw [hicc, hz, hz2, Nat.Ico_zero_eq_range] at h
  have hL : ∑ j ∈ Finset.Icc 1 M, g (M - (M - j)) = ∑ j ∈ Finset.Icc 1 M, g j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [show M - (M - j) = j by omega]
  rw [hL] at h
  exact h

/-- The shifted reciprocal-square-root sum is at most `3`. -/
private lemma sum_range_inv_sqrt_one_add_mul_le (L : ℝ) (hL : 0 < L) (M : ℕ)
    (hMle : (M:ℝ) ≤ L) (hM1 : 1 ≤ M) :
    ∑ k ∈ Finset.range M, (Real.sqrt (1 + (k:ℝ)*L))⁻¹ ≤ 3 := by
  have hpt : ∀ k : ℕ,
      (Real.sqrt (1 + ((k:ℝ)+1)*L))⁻¹ ≤ (Real.sqrt L)⁻¹ * (Real.sqrt ((k:ℝ)+1))⁻¹ := by
    intro k
    have hpos : (0:ℝ) < ((k:ℝ)+1)*L := mul_pos (by positivity) hL
    have hle : ((k:ℝ)+1)*L ≤ 1 + ((k:ℝ)+1)*L := by linarith
    have hs : Real.sqrt (((k:ℝ)+1)*L) ≤ Real.sqrt (1 + ((k:ℝ)+1)*L) := Real.sqrt_le_sqrt hle
    have h1 : (Real.sqrt (1 + ((k:ℝ)+1)*L))⁻¹ ≤ (Real.sqrt (((k:ℝ)+1)*L))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos) hs
    have hsq : Real.sqrt (((k:ℝ)+1)*L) = Real.sqrt ((k:ℝ)+1) * Real.sqrt L := by
      rw [Real.sqrt_mul (by positivity) L]
    rw [hsq, mul_inv] at h1
    calc (Real.sqrt (1 + ((k:ℝ)+1)*L))⁻¹
        ≤ (Real.sqrt ((k:ℝ)+1))⁻¹ * (Real.sqrt L)⁻¹ := h1
      _ = (Real.sqrt L)⁻¹ * (Real.sqrt ((k:ℝ)+1))⁻¹ := by ring
  have hsplit : ∑ k ∈ Finset.range M, (Real.sqrt (1 + (k:ℝ)*L))⁻¹
      = ∑ k ∈ Finset.range (M-1), (Real.sqrt (1 + ((k:ℝ)+1)*L))⁻¹
        + (Real.sqrt (1 + (0:ℝ)*L))⁻¹ := by
    rw [← Nat.sub_add_cancel hM1, Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl; intro k _
      rw [Nat.cast_add, Nat.cast_one]
    · norm_num
  have h0 : (Real.sqrt (1 + (0:ℝ)*L))⁻¹ = 1 := by norm_num
  rw [hsplit, h0]
  have hbound : ∑ k ∈ Finset.range (M-1), (Real.sqrt (1 + ((k:ℝ)+1)*L))⁻¹
      ≤ (Real.sqrt L)⁻¹ * (2 * Real.sqrt ((M-1:ℕ):ℝ)) := by
    calc ∑ k ∈ Finset.range (M-1), (Real.sqrt (1 + ((k:ℝ)+1)*L))⁻¹
        ≤ ∑ k ∈ Finset.range (M-1), (Real.sqrt L)⁻¹ * (Real.sqrt ((k:ℝ)+1))⁻¹ :=
          Finset.sum_le_sum (fun k _ => hpt k)
      _ = (Real.sqrt L)⁻¹ * ∑ k ∈ Finset.range (M-1), (Real.sqrt ((k:ℝ)+1))⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ (Real.sqrt L)⁻¹ * (2 * Real.sqrt ((M-1:ℕ):ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa using sum_range_inv_sqrt_succ_le (M-1)
  have hstep2 : (Real.sqrt L)⁻¹ * (2 * Real.sqrt ((M-1:ℕ):ℝ)) ≤ 2 := by
    have hsqL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
    have hML : Real.sqrt ((M-1:ℕ):ℝ) ≤ Real.sqrt L := by
      apply Real.sqrt_le_sqrt
      have : ((M-1:ℕ):ℝ) ≤ (M:ℝ) := by exact_mod_cast Nat.sub_le M 1
      linarith
    calc (Real.sqrt L)⁻¹ * (2 * Real.sqrt ((M-1:ℕ):ℝ))
        ≤ (Real.sqrt L)⁻¹ * (2 * Real.sqrt L) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 2 := by
          rw [show (Real.sqrt L)⁻¹ * (2 * Real.sqrt L) = 2 * ((Real.sqrt L)⁻¹ * Real.sqrt L) by ring]
          rw [inv_mul_cancel₀ hsqL.ne']; ring
  linarith [hbound, hstep2]

theorem inv_sqrt_shell_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℕ, 1 ≤ x → x ≤ y ^ 2 →
      (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
          (((x : ℝ) + (y : ℝ) - (c : ℝ) ^ 4)) ^ (-(1 / 2 : ℝ)))
        ≤ C * (x : ℝ) ^ (-(1 / 4 : ℝ)) := by
  refine ⟨3, by norm_num, ?_⟩
  intro x y hx hy
  have hXpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hX0 : (0:ℝ) ≤ (x:ℝ) := le_of_lt hXpos
  set L : ℝ := (x:ℝ)^(1/4:ℝ) with hL
  have hLpos : 0 < L := by rw [hL]; exact Real.rpow_pos_of_pos hXpos _
  have hL0 : 0 ≤ L := le_of_lt hLpos
  have hL2 : L^2 = Real.sqrt (x:ℝ) := by rw [hL]; exact rpow_quarter_sq hX0
  have hL4 : L^4 = (x:ℝ) := by rw [hL]; exact rpow_quarter_pow_four hX0
  set M : ℕ := Nat.sqrt (Nat.sqrt x) with hM
  have hYge : L^2 ≤ (y:ℝ) := by
    rw [hL2]
    have hcast : (x:ℝ) ≤ (y:ℝ)^2 := by exact_mod_cast hy
    calc Real.sqrt (x:ℝ) ≤ Real.sqrt ((y:ℝ)^2) := Real.sqrt_le_sqrt hcast
      _ = (y:ℝ) := Real.sqrt_sq (by positivity)
  have hL2ge1 : (1:ℝ) ≤ L^2 := by
    rw [hL2]
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (x:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hx)
  have hYpos : 0 < (y:ℝ) := by linarith [hYge, hL2ge1]
  have hMle : (M:ℝ) ≤ L := by
    rw [hM, hL]; exact natSqrt_sqrt_le_rpow_quarter x
  have hM4 : ((M:ℝ))^4 ≤ (x:ℝ) := by
    rw [hM]
    have h := Nat.cast_le (α := ℝ).mpr (natSqrt_sqrt_pow_four_le x)
    push_cast at h
    exact h
  have hM1 : 1 ≤ M := by
    rw [hM]
    have hsx : 1 ≤ Nat.sqrt x := by
      calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
        _ ≤ Nat.sqrt x := Nat.sqrt_le_sqrt hx
    calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
      _ ≤ Nat.sqrt (Nat.sqrt x) := Nat.sqrt_le_sqrt hsx
  have hterm : ∀ c ∈ Finset.Icc 1 M,
      (((x:ℝ) + (y:ℝ) - (c:ℝ)^4))^(-(1/2:ℝ))
        ≤ (1/L) * (Real.sqrt (1 + (L - (c:ℝ))*L))⁻¹ := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    obtain ⟨hc1, hcM⟩ := hc
    have hc0 : (0:ℝ) ≤ (c:ℝ) := by positivity
    have hcLe : (c:ℝ) ≤ L := by
      have : (c:ℝ) ≤ (M:ℝ) := by exact_mod_cast hcM
      linarith [hMle]
    have hc4le : (c:ℝ)^4 ≤ (x:ℝ) := by
      calc (c:ℝ)^4 ≤ ((M:ℝ))^4 :=
            pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcM) 4
        _ ≤ (x:ℝ) := hM4
    have hZpos : 0 < (x:ℝ) + (y:ℝ) - (c:ℝ)^4 := by linarith [hc4le, hYpos]
    have hkey : L^2 * (1 + (L - (c:ℝ))*L) ≤ (x:ℝ) + (y:ℝ) - (c:ℝ)^4 := by
      have h1 : (L - (c:ℝ))*L^3 ≤ L^4 - (c:ℝ)^4 := sub_pow_four_ge L (c:ℝ) hL0 hc0 hcLe
      rw [hL4] at h1
      have h2 : (L - (c:ℝ))*L^3 + L^2 ≤ (x:ℝ) + (y:ℝ) - (c:ℝ)^4 := by linarith [h1, hYge]
      calc L^2 * (1 + (L - (c:ℝ))*L) = (L - (c:ℝ))*L^3 + L^2 := by ring
        _ ≤ (x:ℝ) + (y:ℝ) - (c:ℝ)^4 := h2
    have hZpow : ((x:ℝ)+(y:ℝ)-(c:ℝ)^4)^(-(1/2:ℝ))
        = (Real.sqrt ((x:ℝ)+(y:ℝ)-(c:ℝ)^4))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hZpos) (1/2), ← Real.sqrt_eq_rpow]
    rw [hZpow]
    have hWpos : 0 < L^2 * (1 + (L - (c:ℝ))*L) := by
      have hW1 : 0 < 1 + (L - (c:ℝ))*L := by nlinarith [hcLe, hLpos]
      positivity
    have hsW : Real.sqrt (L^2 * (1 + (L - (c:ℝ))*L))
        = L * Real.sqrt (1 + (L - (c:ℝ))*L) := by
      rw [Real.sqrt_mul (by positivity) _, Real.sqrt_sq hL0]
    have hle_sqrt : Real.sqrt (L^2 * (1 + (L - (c:ℝ))*L))
        ≤ Real.sqrt ((x:ℝ)+(y:ℝ)-(c:ℝ)^4) := Real.sqrt_le_sqrt hkey
    have hsqZ : 0 < Real.sqrt ((x:ℝ)+(y:ℝ)-(c:ℝ)^4) := Real.sqrt_pos.mpr hZpos
    calc (Real.sqrt ((x:ℝ)+(y:ℝ)-(c:ℝ)^4))⁻¹
        ≤ (Real.sqrt (L^2 * (1 + (L - (c:ℝ))*L)))⁻¹ := by
          rw [← one_div, ← one_div]
          exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hWpos) hle_sqrt
      _ = (L * Real.sqrt (1 + (L - (c:ℝ))*L))⁻¹ := by rw [hsW]
      _ = (1/L) * (Real.sqrt (1 + (L - (c:ℝ))*L))⁻¹ := by rw [mul_inv]; ring
  have hsum1 : ∑ c ∈ Finset.Icc 1 M, (Real.sqrt (1 + (L - (c:ℝ))*L))⁻¹
      ≤ ∑ k ∈ Finset.range M, (Real.sqrt (1 + (k:ℝ)*L))⁻¹ := by
    rw [sum_Icc_eq_sum_range_sub (fun c => (Real.sqrt (1 + (L - (c:ℝ))*L))⁻¹) M]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range] at hk
    have hkM : k ≤ M := le_of_lt hk
    have hcast : ((M - k : ℕ):ℝ) = (M:ℝ) - (k:ℝ) := by rw [Nat.cast_sub hkM]
    have harg : L - ((M - k : ℕ):ℝ) = L - (M:ℝ) + (k:ℝ) := by rw [hcast]; ring
    have hge : (k:ℝ)*L ≤ (L - ((M - k : ℕ):ℝ))*L := by
      rw [harg]
      apply mul_le_mul_of_nonneg_right _ hL0
      linarith [hMle]
    have hpos1 : 0 < 1 + (k:ℝ)*L := by
      have : 0 ≤ (k:ℝ)*L := mul_nonneg (by positivity) hL0
      linarith
    have hsle : Real.sqrt (1 + (k:ℝ)*L) ≤ Real.sqrt (1 + (L - ((M - k : ℕ):ℝ))*L) :=
      Real.sqrt_le_sqrt (by linarith)
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos1) hsle
  have hsum2 : ∑ k ∈ Finset.range M, (Real.sqrt (1 + (k:ℝ)*L))⁻¹ ≤ 3 :=
    sum_range_inv_sqrt_one_add_mul_le L hLpos M hMle hM1
  calc ∑ c ∈ Finset.Icc 1 M, ((x:ℝ)+(y:ℝ)-(c:ℝ)^4)^(-(1/2:ℝ))
      ≤ ∑ c ∈ Finset.Icc 1 M, (1/L) * (Real.sqrt (1 + (L - (c:ℝ))*L))⁻¹ :=
          Finset.sum_le_sum hterm
    _ = (1/L) * ∑ c ∈ Finset.Icc 1 M, (Real.sqrt (1 + (L - (c:ℝ))*L))⁻¹ := by
          rw [Finset.mul_sum]
    _ ≤ (1/L) * ∑ k ∈ Finset.range M, (Real.sqrt (1 + (k:ℝ)*L))⁻¹ := by
          apply mul_le_mul_of_nonneg_left hsum1 (by positivity)
    _ ≤ (1/L) * 3 := by
          apply mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = 3 * (x:ℝ)^(-(1/4:ℝ)) := by
          rw [Real.rpow_neg hX0 (1/4), ← hL, one_div]; ring


end Commons.Analysis.Sum
