import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Star.Real

set_option maxHeartbeats 4000000

namespace Commons.Analysis.Sigma2

open scoped BigOperators

/-- Elementary quadratic lower bound: for `X > 0` and reals `p, q, r`,
`(X/(X+1)) p^2 - 2X (q^2 + r^2) ≤ (p - q - r)^2`.  The difference equals
`(1/(X+1)) (p - (X+1)(q+r))^2 + X (q-r)^2`. -/
theorem sq_lower_bound (p q r X : ℝ) (hX : 0 < X) :
    (X / (X + 1)) * p ^ 2 - 2 * X * (q ^ 2 + r ^ 2) ≤ (p - q - r) ^ 2 := by
  have hX1 : 0 < X + 1 := by linarith
  have key : ((p - q - r) ^ 2 - ((X / (X + 1)) * p ^ 2 - 2 * X * (q ^ 2 + r ^ 2))) * (X + 1)
      = (p - (X + 1) * (q + r)) ^ 2 + X * (X + 1) * (q - r) ^ 2 := by
    field_simp
    ring
  have hnn : 0 ≤ ((p - q - r) ^ 2 - ((X / (X + 1)) * p ^ 2 - 2 * X * (q ^ 2 + r ^ 2))) * (X + 1) := by
    rw [key]
    have := mul_nonneg hX.le hX1.le
    nlinarith [sq_nonneg (p - (X + 1) * (q + r)), sq_nonneg (q - r)]
  have h2 : 0 ≤ (p - q - r) ^ 2 - ((X / (X + 1)) * p ^ 2 - 2 * X * (q ^ 2 + r ^ 2)) :=
    (mul_nonneg_iff_of_pos_right hX1).mp hnn
  linarith

open scoped BigOperators in
theorem regular_case_contradiction {S rho b α β Γ γ : ℝ} {lam xc u D1b : Fin 4 → ℝ}
    (hb : 0 < b) (hbγ : 1 / γ ≤ b) (hrho : 0 < rho) (hrho9 : rho < 9) (hS : 0 < S)
    (hΓ : 4 ≤ Γ) (hγ : 0 < γ) (hγ4000 : 4000 ≤ 1 / γ)
    (hα : α = γ ^ 4 / Γ) (hβ : β = γ ^ 6 / Γ ^ 2)
    (hxc : ∀ i : Fin 4, |xc i| ≤ 3) (hu : ∀ i : Fin 4, |u i| ≤ Γ)
    (hfs3 : (∑ i : Fin 4, (S - lam i)) = 3 * S)
    (hfsnn : ∀ i : Fin 4, 0 ≤ S - lam i)
    (hklow : ∀ i : Fin 4, i ≠ 0 → (1 - 1 / Real.sqrt 2) * S ≤ S - lam i)
    (hf0 : S / 16 ≤ (S - lam 0) * (lam 0) ^ 2)
    (hk : ∃ k : Fin 4, 1 ≤ (k : ℕ) ∧ 1 / 4 ≤ (xc k) ^ 2)
    (hmax1 : ∀ i : Fin 4, D1b i / b = 4 * xc i / rho - α * xc i * lam i - β * u i * lam i)
    (hmaxP : -12 * S / rho - 8 * (∑ i : Fin 4, (S - lam i) * (xc i) ^ 2) / rho ^ 2 + 2 * α
        + β * (∑ i : Fin 4, (S - lam i) * (lam i) ^ 2)
        + (1 / 36) * ((1 / b) * (∑ i : Fin 4, (S - lam i) * (D1b i) ^ 2)) ≤ 0) :
    False := by
  classical
  have hΓpos : 0 < Γ := by linarith
  have hαpos : 0 < α := by rw [hα]; positivity
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hγpos : 0 < γ := hγ
  have hγle : γ ≤ 1 / 4000 := by
    have h4 : (4000 : ℝ) * γ ≤ 1 := (le_div_iff₀ hγ).mp hγ4000
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4000)]
    linarith
  have hb4000 : 4000 ≤ b := le_trans hγ4000 hbγ
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc0pos : 0 < 1 - 1 / Real.sqrt 2 := by
    have : 1 / Real.sqrt 2 < 1 := by
      rw [div_lt_one hsqrt2pos]; nlinarith [hsq2, hsqrt2pos]
    linarith
  have hc0_gt : (27 : ℝ) / 100 < 1 - 1 / Real.sqrt 2 := by
    have : 1 / Real.sqrt 2 < 73 / 100 := by
      rw [div_lt_iff₀ hsqrt2pos]; nlinarith [hsq2, hsqrt2pos]
    linarith
  set T2 : ℝ := ∑ i : Fin 4, (S - lam i) * (xc i) ^ 2 with hT2
  set T3 : ℝ := ∑ i : Fin 4, (S - lam i) * (lam i) ^ 2 with hT3
  set W : ℝ := ∑ i : Fin 4, (S - lam i) * (D1b i) ^ 2 with hW
  set S1 : ℝ := 9 * α ^ 2 + Γ ^ 2 * β ^ 2 with hS1
  have hS1pos : 0 < S1 := by rw [hS1]; positivity
  set X : ℝ := 18 * β / (b * S1) with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  set A : ℝ := (4 * b * X) / (9 * (X + 1)) with hA
  set Q : ℝ := T2 / rho ^ 2 with hQ
  set V0 : ℝ := (16 * X / (X + 1)) * T2 / rho ^ 2 - 2 * X * S1 * T3 with hV0
  have hmaxP' : -12 * S / rho - 8 * Q + 2 * α + β * T3 + (1 / 36) * ((1 / b) * W) ≤ 0 := by
    have h := hmaxP
    have e2 : -12 * S / rho - 8 * T2 / rho ^ 2 + 2 * α + β * T3 + (1 / 36) * ((1 / b) * W)
        = -12 * S / rho - 8 * (T2 / rho ^ 2) + 2 * α + β * T3 + (1 / 36) * ((1 / b) * W) := by ring
    rw [e2] at h
    rw [hQ]
    exact h
  have hXbS1 : X * (b * S1) = 18 * β := by rw [hX]; field_simp
  have hXbS1' : X * b * S1 = 18 * β := by rw [mul_assoc]; exact hXbS1
  have hD : ∀ i : Fin 4, D1b i = b * (4 * xc i / rho - α * xc i * lam i - β * u i * lam i) := by
    intro i
    rw [← hmax1 i, mul_div_cancel₀ _ hb.ne']
  have hpoint : ∀ i : Fin 4,
      (S - lam i) * b ^ 2 * ((X / (X + 1)) * (4 * xc i / rho) ^ 2
        - 2 * X * ((α * xc i * lam i) ^ 2 + (β * u i * lam i) ^ 2))
      ≤ (S - lam i) * (D1b i) ^ 2 := by
    intro i
    rw [hD i]
    have hP := sq_lower_bound (4 * xc i / rho) (α * xc i * lam i) (β * u i * lam i) X hXpos
    have hcoef : 0 ≤ (S - lam i) * b ^ 2 := mul_nonneg (hfsnn i) (sq_nonneg b)
    have h1 := mul_le_mul_of_nonneg_left hP hcoef
    nlinarith [h1]
  have hsum : (∑ i : Fin 4, (S - lam i) * b ^ 2 * ((X / (X + 1)) * (4 * xc i / rho) ^ 2
        - 2 * X * ((α * xc i * lam i) ^ 2 + (β * u i * lam i) ^ 2))) ≤ W :=
    Finset.sum_le_sum (fun i _ => hpoint i)
  have hZ1 : (∑ i : Fin 4, (S - lam i) * b ^ 2 * ((X / (X + 1)) * (4 * xc i / rho) ^ 2))
      = b ^ 2 * ((16 * X / (X + 1)) * T2 / rho ^ 2) := by
    rw [hT2]
    rw [show b ^ 2 * ((16 * X / (X + 1)) * (∑ i : Fin 4, (S - lam i) * (xc i) ^ 2) / rho ^ 2)
        = ∑ i : Fin 4, b ^ 2 * (16 * X / (X + 1)) * ((S - lam i) * (xc i) ^ 2) / rho ^ 2 by
      rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hZ2 : (∑ i : Fin 4, (S - lam i) * b ^ 2 * (2 * X * ((α * xc i * lam i) ^ 2 + (β * u i * lam i) ^ 2)))
      ≤ b ^ 2 * 2 * X * S1 * T3 := by
    have hb1 : ∀ i : Fin 4, (S - lam i) * b ^ 2 * (2 * X * ((α * xc i * lam i) ^ 2 + (β * u i * lam i) ^ 2))
        ≤ (S - lam i) * b ^ 2 * (2 * X * S1 * (lam i) ^ 2) := by
      intro i
      have hxc2 : (xc i) ^ 2 ≤ 9 := by
        have := abs_le.mp (hxc i); nlinarith [this.1, this.2]
      have hu2 : (u i) ^ 2 ≤ Γ ^ 2 := by
        have := abs_le.mp (hu i); nlinarith [this.1, this.2, hΓpos]
      have hkey2 : (α * xc i * lam i) ^ 2 + (β * u i * lam i) ^ 2 ≤ S1 * (lam i) ^ 2 := by
        rw [hS1]
        nlinarith [hxc2, hu2, sq_nonneg (α * lam i), sq_nonneg (β * lam i), sq_nonneg (lam i)]
      have hcoef : 0 ≤ (S - lam i) * b ^ 2 * (2 * X) :=
        mul_nonneg (mul_nonneg (hfsnn i) (sq_nonneg b)) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hkey2 hcoef]
    have hsum2 : (∑ i : Fin 4, (S - lam i) * b ^ 2 * (2 * X * ((α * xc i * lam i) ^ 2 + (β * u i * lam i) ^ 2)))
        ≤ (∑ i : Fin 4, (S - lam i) * b ^ 2 * (2 * X * S1 * (lam i) ^ 2)) :=
      Finset.sum_le_sum (fun i _ => hb1 i)
    have hZ2eq : (∑ i : Fin 4, (S - lam i) * b ^ 2 * (2 * X * S1 * (lam i) ^ 2))
        = b ^ 2 * 2 * X * S1 * T3 := by
      rw [hT3]
      rw [show b ^ 2 * 2 * X * S1 * (∑ i : Fin 4, (S - lam i) * (lam i) ^ 2)
          = ∑ i : Fin 4, b ^ 2 * 2 * X * S1 * ((S - lam i) * (lam i) ^ 2) by
        rw [Finset.mul_sum]]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hZ2eq] at hsum2
    exact hsum2
  have hZeq : (∑ i : Fin 4, (S - lam i) * b ^ 2 * ((X / (X + 1)) * (4 * xc i / rho) ^ 2
        - 2 * X * ((α * xc i * lam i) ^ 2 + (β * u i * lam i) ^ 2)))
      = (∑ i : Fin 4, (S - lam i) * b ^ 2 * ((X / (X + 1)) * (4 * xc i / rho) ^ 2))
        - (∑ i : Fin 4, (S - lam i) * b ^ 2 * (2 * X * ((α * xc i * lam i) ^ 2 + (β * u i * lam i) ^ 2))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hWlb : b ^ 2 * V0 ≤ W := by
    have hZlb : b ^ 2 * V0
        ≤ (∑ i : Fin 4, (S - lam i) * b ^ 2 * ((X / (X + 1)) * (4 * xc i / rho) ^ 2
          - 2 * X * ((α * xc i * lam i) ^ 2 + (β * u i * lam i) ^ 2))) := by
      rw [hV0, hZeq, hZ1]
      nlinarith [hZ2]
    exact hZlb.trans hsum
  have hbound : A * Q - β * T3 ≤ (1 / 36) * ((1 / b) * W) := by
    rw [hQ, hA]
    have hnn : (0 : ℝ) ≤ (1 / 36) * (1 / b) := by positivity
    have hstep : (1 / 36) * ((1 / b) * (b ^ 2 * V0)) ≤ (1 / 36) * ((1 / b) * W) := by
      have := mul_le_mul_of_nonneg_left hWlb hnn
      nlinarith [this]
    have hsimp : (1 / 36) * ((1 / b) * (b ^ 2 * V0))
        = (4 * b * X / (9 * (X + 1))) * (T2 / rho ^ 2) - β * T3 := by
      have hbXS1 : b * X * S1 = 18 * β := by rw [mul_comm b X, mul_assoc]; exact hXbS1
      rw [hV0]
      have h1 : (1 / 36) * ((1 / b) * (b ^ 2 * ((16 * X / (X + 1)) * T2 / rho ^ 2 - 2 * X * S1 * T3)))
          = (b / 36) * ((16 * X / (X + 1)) * T2 / rho ^ 2 - 2 * X * S1 * T3) := by
        field_simp
      rw [h1]
      have hfin : (b / 36) * ((16 * X / (X + 1)) * T2 / rho ^ 2 - 2 * X * S1 * T3)
          = (4 * b * X / (9 * (X + 1))) * (T2 / rho ^ 2) - β * T3 := by
        have hβeq : β = b * X * S1 / 18 := by
          rw [eq_div_iff (by norm_num : (18 : ℝ) ≠ 0)]
          linarith [hbXS1]
        rw [hβeq]
        field_simp
        ring
      rw [hfin]
    linarith [hstep, hsimp]
  have hkey : -12 * S / rho + 2 * α + (A - 8) * Q ≤ 0 := by nlinarith [hmaxP', hbound]
  have hA_big : 1620 ≤ A := by
    rw [hA]
    have hAeq : (4 * b * X) / (9 * (X + 1)) = 8 * b * β / (18 * β + b * S1) := by
      have h9 : (9 : ℝ) * (X + 1) ≠ 0 := by positivity
      have h18 : 18 * β + b * S1 ≠ 0 := by positivity
      rw [div_eq_div_iff h9 h18]
      nlinarith [hXbS1]
    have hA8 : 8 * b * β / (18 * β + b * S1) = 8 * b / (18 + b * (9 * γ ^ 2 + γ ^ 6)) := by
      have e : 18 * β + b * S1 = 18 * β + b * (9 * α ^ 2 + Γ ^ 2 * β ^ 2) := by rw [hS1]
      rw [e, hα, hβ]
      field_simp
      try ring
    rw [hAeq, hA8]
    have hden : 0 < 18 + b * (9 * γ ^ 2 + γ ^ 6) := by positivity
    rw [le_div_iff₀ hden]
    have hγ2 : 9 * γ ^ 2 + γ ^ 6 ≤ 1 / 1000000 := by
      have hb1 : γ ^ 2 ≤ (1 / 4000 : ℝ) ^ 2 := pow_le_pow_left₀ hγpos.le hγle 2
      have hb2 : γ ^ 6 ≤ (1 / 4000 : ℝ) ^ 6 := pow_le_pow_left₀ hγpos.le hγle 6
      nlinarith [hb1, hb2]
    nlinarith [hb4000, hγ2]
  have hT2lb : (1 - 1 / Real.sqrt 2) * S / 4 ≤ T2 := by
    rw [hT2]
    obtain ⟨k, hk1, hk2⟩ := hk
    have hk0 : k ≠ 0 := by intro h; rw [h] at hk1; simp at hk1
    have hFk : (1 - 1 / Real.sqrt 2) * S ≤ S - lam k := hklow k hk0
    have hc0nn : 0 ≤ 1 - 1 / Real.sqrt 2 := le_of_lt hc0pos
    have hterm : (1 - 1 / Real.sqrt 2) * S * (1 / 4) ≤ (S - lam k) * (xc k) ^ 2 :=
      mul_le_mul hFk hk2 (by norm_num) (le_trans (mul_nonneg hc0nn hS.le) hFk)
    have hsingle : (S - lam k) * (xc k) ^ 2 ≤ ∑ i, (S - lam i) * (xc i) ^ 2 :=
      Finset.single_le_sum (fun i _ => mul_nonneg (hfsnn i) (sq_nonneg (xc i))) (Finset.mem_univ k)
    linarith
  have hQlb : (1 - 1 / Real.sqrt 2) * S / (4 * rho ^ 2) ≤ Q := by
    rw [hQ]
    rw [show (1 - 1 / Real.sqrt 2) * S / (4 * rho ^ 2) = ((1 - 1 / Real.sqrt 2) * S / 4) / rho ^ 2 by ring]
    exact div_le_div_of_nonneg_right hT2lb (by positivity)
  have hQpos : 0 < Q :=
    lt_of_lt_of_le (div_pos (mul_pos hc0pos hS) (by positivity : (0 : ℝ) < 4 * rho ^ 2)) hQlb
  have hcontra : 0 < -12 * S / rho + 2 * α + (A - 8) * Q := by
    have hA8' : (1612 : ℝ) ≤ A - 8 := by linarith [hA_big]
    have h1 : (1612 : ℝ) * Q ≤ (A - 8) * Q :=
      mul_le_mul_of_nonneg_right hA8' hQpos.le
    have h2 : 1612 * ((1 - 1 / Real.sqrt 2) * S / (4 * rho ^ 2)) ≤ 1612 * Q :=
      mul_le_mul_of_nonneg_left hQlb (by norm_num)
    have h3 : 0 < -12 * S / rho + 2 * α + 1612 * ((1 - 1 / Real.sqrt 2) * S / (4 * rho ^ 2)) := by
      have hineq : 12 * S / rho < 1612 * ((1 - 1 / Real.sqrt 2) * S / (4 * rho ^ 2)) := by
        have : True := trivial
        have h12 : 12 * rho < 1612 * (1 - 1 / Real.sqrt 2) / 4 := by nlinarith [hrho9, hc0_gt]
        have hSp : 0 < S / rho ^ 2 := div_pos hS (by positivity)
        have hthis := mul_lt_mul_of_pos_right h12 hSp
        have e1 : 12 * rho * (S / rho ^ 2) = 12 * S / rho := by field_simp
        have e2 : (1612 * (1 - 1 / Real.sqrt 2) / 4) * (S / rho ^ 2)
            = 1612 * ((1 - 1 / Real.sqrt 2) * S / (4 * rho ^ 2)) := by ring
        rw [e1, e2] at hthis
        exact hthis
      have hmain : 0 < -(12 * S / rho) + 1612 * ((1 - 1 / Real.sqrt 2) * S / (4 * rho ^ 2)) := by
        linarith [hineq]
      have hneg : (-12 : ℝ) * S / rho = -(12 * S / rho) := by ring
      rw [hneg]
      linarith [hmain, hαpos]
    linarith [h1, h2, h3]
  linarith [hkey, hcontra]

end Commons.Analysis.Sigma2