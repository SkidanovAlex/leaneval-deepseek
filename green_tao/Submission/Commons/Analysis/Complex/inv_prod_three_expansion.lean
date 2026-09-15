import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Submission.Commons.Analysis.Complex.inv_one_sub_approx
import Submission.Commons.Analysis.Complex.norm_prod_one_add_sub_one_sub_sum_le

open scoped BigOperators

namespace Commons.Analysis.Complex

set_option maxHeartbeats 4000000 in
/-- Auxiliary form of `inv_prod_three_expansion` for arbitrary complex sequences `a,b,c`
satisfying the norm bounds. -/
lemma inv_prod_three_expansion_aux {m : ℕ} (a b c : Fin m → ℂ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hA1 : A ≤ 1) (hC1 : C ≤ 1)
    (hm : (m : ℝ) * (2 * A + C) ≤ 1 / 2)
    (ha : ∀ j, ‖a j‖ ≤ A) (hb : ∀ j, ‖b j‖ ≤ A) (hc : ∀ j, ‖c j‖ ≤ C) :
    ∃ S : ℂ, ‖S‖ ≤ 10000 * ((m : ℝ) ^ 2 + m) * (A ^ 2 + A * C + C ^ 2)
      ∧ ∏ j, ((1 - a j)⁻¹ * (1 - b j)⁻¹ * (1 - c j))
        = 1 + ∑ j, (a j + b j - c j) + S := by
  rcases eq_or_ne m 0 with h0 | hm0
  · subst h0
    exact ⟨0, by simp, by simp⟩
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
    have hm0' : (0 : ℝ) ≤ (m : ℝ) := by linarith
    have h2AC : 2 * A + C ≤ 1 / 2 := by nlinarith [hm, hm1, hA, hC]
    have hA14 : A ≤ 1 / 4 := by nlinarith [h2AC, hC]
    have hC12 : C ≤ 1 / 2 := by nlinarith [h2AC, hA]
    have hA12 : A ≤ 1 / 2 := by linarith
    have hmA : (m : ℝ) * A ≤ 1 / 4 := by nlinarith [hm, hm0', hA, hC]
    have hmC : (m : ℝ) * C ≤ 1 / 2 := by nlinarith [hm, hm0', hA, hC]
    -- the second order remainder of each individual `(1 - a)⁻¹`
    let ε : Fin m → ℂ := fun j => (1 - a j)⁻¹ - (1 + a j)
    let δ : Fin m → ℂ := fun j => (1 - b j)⁻¹ - (1 + b j)
    have hε4 : ∀ j, ‖ε j‖ ≤ 4 * A ^ 2 := by
      intro j
      have h1 := (inv_one_sub_approx (show ‖a j‖ ≤ 1 / 2 by linarith [ha j, hA12])).2
      have h2 : ‖a j‖ ^ 2 ≤ A ^ 2 := by nlinarith [ha j, norm_nonneg (a j)]
      change ‖(1 - a j)⁻¹ - (1 + a j)‖ ≤ 4 * A ^ 2
      linarith
    have hδ4 : ∀ j, ‖δ j‖ ≤ 4 * A ^ 2 := by
      intro j
      have h1 := (inv_one_sub_approx (show ‖b j‖ ≤ 1 / 2 by linarith [hb j, hA12])).2
      have h2 : ‖b j‖ ^ 2 ≤ A ^ 2 := by nlinarith [hb j, norm_nonneg (b j)]
      change ‖(1 - b j)⁻¹ - (1 + b j)‖ ≤ 4 * A ^ 2
      linarith
    -- bounds of the relevant sums
    have hsumA : ∑ j, ‖a j + ε j‖ ≤ (m : ℝ) * (A + 4 * A ^ 2) := by
      calc ∑ j, ‖a j + ε j‖ ≤ ∑ j, (A + 4 * A ^ 2) :=
            Finset.sum_le_sum (fun j _ => by
              have h := norm_add_le (a j) (ε j)
              have h4 := hε4 j
              have h5 := ha j
              linarith)
        _ = (m : ℝ) * (A + 4 * A ^ 2) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring
    have hsumB : ∑ j, ‖b j + δ j‖ ≤ (m : ℝ) * (A + 4 * A ^ 2) := by
      calc ∑ j, ‖b j + δ j‖ ≤ ∑ j, (A + 4 * A ^ 2) :=
            Finset.sum_le_sum (fun j _ => by
              have h := norm_add_le (b j) (δ j)
              have h4 := hδ4 j
              have h5 := hb j
              linarith)
        _ = (m : ℝ) * (A + 4 * A ^ 2) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring
    have hAq_le : (m : ℝ) * (A + 4 * A ^ 2) ≤ 1 / 2 := by
      nlinarith [hmA, hA14, hA, hm0']
    have hsumA1 : ∑ j, ‖a j + ε j‖ ≤ 1 := by linarith [hsumA, hAq_le]
    have hsumB1 : ∑ j, ‖b j + δ j‖ ≤ 1 := by linarith [hsumB, hAq_le]
    have hsumE : ∑ j, ‖ε j‖ ≤ (m : ℝ) * (4 * A ^ 2) := by
      calc ∑ j, ‖ε j‖ ≤ ∑ j, (4 * A ^ 2) := Finset.sum_le_sum (fun j _ => hε4 j)
        _ = (m : ℝ) * (4 * A ^ 2) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring
    have hsumD : ∑ j, ‖δ j‖ ≤ (m : ℝ) * (4 * A ^ 2) := by
      calc ∑ j, ‖δ j‖ ≤ ∑ j, (4 * A ^ 2) := Finset.sum_le_sum (fun j _ => hδ4 j)
        _ = (m : ℝ) * (4 * A ^ 2) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring
    have hsumC : ∑ j, ‖c j‖ ≤ (m : ℝ) * C := by
      calc ∑ j, ‖c j‖ ≤ ∑ j, C := Finset.sum_le_sum (fun j _ => hc j)
        _ = (m : ℝ) * C := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring
    have hsumC1 : ∑ j, ‖c j‖ ≤ 1 := by linarith [hsumC, hmC]
    have hsumA0 : ∑ j, ‖a j‖ ≤ (m : ℝ) * A := by
      calc ∑ j, ‖a j‖ ≤ ∑ j, A := Finset.sum_le_sum (fun j _ => ha j)
        _ = (m : ℝ) * A := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring
    have hsumB0 : ∑ j, ‖b j‖ ≤ (m : ℝ) * A := by
      calc ∑ j, ‖b j‖ ≤ ∑ j, A := Finset.sum_le_sum (fun j _ => hb j)
        _ = (m : ℝ) * A := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring
    -- the three products
    set Pa : ℂ := ∏ j, (1 - a j)⁻¹ with hPa_def
    set Pb : ℂ := ∏ j, (1 - b j)⁻¹ with hPb_def
    set Pc : ℂ := ∏ j, (1 - c j) with hPc_def
    have hPa_eq : Pa = ∏ j, (1 + (a j + ε j)) := by
      rw [hPa_def]
      apply Finset.prod_congr rfl
      intro j _
      show (1 - a j)⁻¹ = 1 + (a j + ε j)
      simp only [ε]
      ring
    have hPb_eq : Pb = ∏ j, (1 + (b j + δ j)) := by
      rw [hPb_def]
      apply Finset.prod_congr rfl
      intro j _
      show (1 - b j)⁻¹ = 1 + (b j + δ j)
      simp only [δ]
      ring
    have hPc_eq : Pc = ∏ j, (1 + (-(c j))) := by
      rw [hPc_def]
      apply Finset.prod_congr rfl
      intro j _
      ring
    have hPa_le : ‖Pa - 1 - ∑ j, (a j + ε j)‖ ≤ 2 * (∑ j, ‖a j + ε j‖) ^ 2 := by
      rw [hPa_eq]
      exact norm_prod_one_add_sub_one_sub_sum_le Finset.univ (fun j => a j + ε j) hsumA1
    have hPb_le : ‖Pb - 1 - ∑ j, (b j + δ j)‖ ≤ 2 * (∑ j, ‖b j + δ j‖) ^ 2 := by
      rw [hPb_eq]
      exact norm_prod_one_add_sub_one_sub_sum_le Finset.univ (fun j => b j + δ j) hsumB1
    have hPc_le : ‖Pc - 1 - ∑ j, (-(c j))‖ ≤ 2 * (∑ j, ‖-(c j)‖) ^ 2 := by
      rw [hPc_eq]
      exact norm_prod_one_add_sub_one_sub_sum_le Finset.univ (fun j => -(c j)) (by simpa using hsumC1)
    set α : ℂ := ∑ j, a j with hα_def
    set β : ℂ := ∑ j, b j with hβ_def
    set γ : ℂ := ∑ j, c j with hγ_def
    have hsumU : ∑ j, (a j + ε j) = α + ∑ j, ε j := by
      rw [Finset.sum_add_distrib, hα_def]
    have hsumV : ∑ j, (b j + δ j) = β + ∑ j, δ j := by
      rw [Finset.sum_add_distrib, hβ_def]
    have hsumW : ∑ j, (-(c j)) = -γ := by
      rw [Finset.sum_neg_distrib, hγ_def]
    set Ea : ℂ := Pa - 1 - α with hEa_def
    set Eb : ℂ := Pb - 1 - β with hEb_def
    set Ec : ℂ := Pc - 1 + γ with hEc_def
    have hEa_b : ‖Ea‖ ≤ 2 * ((m : ℝ) * (A + 4 * A ^ 2)) ^ 2 + (m : ℝ) * (4 * A ^ 2) := by
      have hdec : Ea = (Pa - 1 - ∑ j, (a j + ε j)) + ∑ j, ε j := by
        rw [hEa_def, hsumU]; ring
      have hsq : (∑ j, ‖a j + ε j‖) ^ 2 ≤ ((m : ℝ) * (A + 4 * A ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsumA 2
      rw [hdec]
      calc ‖(Pa - 1 - ∑ j, (a j + ε j)) + ∑ j, ε j‖
          ≤ ‖Pa - 1 - ∑ j, (a j + ε j)‖ + ‖∑ j, ε j‖ := norm_add_le _ _
        _ ≤ 2 * (∑ j, ‖a j + ε j‖) ^ 2 + ∑ j, ‖ε j‖ := by
              linarith [hPa_le, norm_sum_le Finset.univ ε]
        _ ≤ 2 * ((m : ℝ) * (A + 4 * A ^ 2)) ^ 2 + (m : ℝ) * (4 * A ^ 2) := by
              linarith [hsq, hsumE]
    have hEb_b : ‖Eb‖ ≤ 2 * ((m : ℝ) * (A + 4 * A ^ 2)) ^ 2 + (m : ℝ) * (4 * A ^ 2) := by
      have hdec : Eb = (Pb - 1 - ∑ j, (b j + δ j)) + ∑ j, δ j := by
        rw [hEb_def, hsumV]; ring
      have hsq : (∑ j, ‖b j + δ j‖) ^ 2 ≤ ((m : ℝ) * (A + 4 * A ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsumB 2
      rw [hdec]
      calc ‖(Pb - 1 - ∑ j, (b j + δ j)) + ∑ j, δ j‖
          ≤ ‖Pb - 1 - ∑ j, (b j + δ j)‖ + ‖∑ j, δ j‖ := norm_add_le _ _
        _ ≤ 2 * (∑ j, ‖b j + δ j‖) ^ 2 + ∑ j, ‖δ j‖ := by
              linarith [hPb_le, norm_sum_le Finset.univ δ]
        _ ≤ 2 * ((m : ℝ) * (A + 4 * A ^ 2)) ^ 2 + (m : ℝ) * (4 * A ^ 2) := by
              linarith [hsq, hsumD]
    have hEc_b : ‖Ec‖ ≤ 2 * ((m : ℝ) * C) ^ 2 := by
      have hdec : Ec = Pc - 1 - ∑ j, (-(c j)) := by
        rw [hEc_def, hsumW]; ring
      have hsq : (∑ j, ‖-(c j)‖) ^ 2 ≤ ((m : ℝ) * C) ^ 2 := by
        have h1 : (∑ j, ‖-(c j)‖) = ∑ j, ‖c j‖ := by simp
        rw [h1]
        exact pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsumC 2
      rw [hdec]
      linarith [hPc_le, hsq]
    -- simplified bounds
    have hAq : A + 4 * A ^ 2 ≤ 2 * A := by nlinarith [hA14, hA]
    have hAq0 : (0:ℝ) ≤ A + 4 * A ^ 2 := by positivity
    have hsqA : ((m : ℝ) * (A + 4 * A ^ 2)) ^ 2 ≤ ((m : ℝ) * (2 * A)) ^ 2 := by
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hAq0 hAq 2) (sq_nonneg (m : ℝ))
    have hEq2 : (2:ℝ) * ((m : ℝ) * (2 * A)) ^ 2 + (m : ℝ) * (4 * A ^ 2)
        = 8 * (m : ℝ) ^ 2 * A ^ 2 + 4 * (m : ℝ) * A ^ 2 := by ring
    have hEa2 : ‖Ea‖ ≤ 8 * (m : ℝ) ^ 2 * A ^ 2 + 4 * (m : ℝ) * A ^ 2 := by
      linarith [hEa_b, hsqA, hEq2]
    have hEb2 : ‖Eb‖ ≤ 8 * (m : ℝ) ^ 2 * A ^ 2 + 4 * (m : ℝ) * A ^ 2 := by
      linarith [hEb_b, hsqA, hEq2]
    have hEc2 : ‖Ec‖ ≤ 2 * (m : ℝ) ^ 2 * C ^ 2 := by
      have hEq : (2:ℝ) * ((m : ℝ) * C) ^ 2 = 2 * (m : ℝ) ^ 2 * C ^ 2 := by ring
      linarith [hEc_b, hEq]
    have hα_b : ‖α‖ ≤ (m : ℝ) * A := by
      rw [hα_def]; exact (norm_sum_le Finset.univ a).trans hsumA0
    have hβ_b : ‖β‖ ≤ (m : ℝ) * A := by
      rw [hβ_def]; exact (norm_sum_le Finset.univ b).trans hsumB0
    have hγ_b : ‖γ‖ ≤ (m : ℝ) * C := by
      rw [hγ_def]; exact (norm_sum_le Finset.univ c).trans hsumC
    set X : ℂ := α + Ea with hX_def
    set Y : ℂ := β + Eb with hY_def
    set Z : ℂ := -γ + Ec with hZ_def
    have h4mA : (0:ℝ) ≤ 4 * (m : ℝ) * A := by positivity
    have h2mC : (0:ℝ) ≤ 2 * (m : ℝ) * C := by positivity
    have hmA0 : (0:ℝ) ≤ (m : ℝ) * A := mul_nonneg hm0' hA
    have hmC0 : (0:ℝ) ≤ (m : ℝ) * C := mul_nonneg hm0' hC
    have h8mA : 8 * (m : ℝ) ^ 2 * A ^ 2 ≤ 2 * ((m : ℝ) * A) := by
      nlinarith [hmA, hmA0]
    have h4mA2 : 4 * (m : ℝ) * A ^ 2 ≤ (m : ℝ) * A := by
      nlinarith [hA14, hA, hm0']
    have hX_b : ‖X‖ ≤ 4 * (m : ℝ) * A := by
      rw [hX_def]
      have h := norm_add_le α Ea
      nlinarith [h, hα_b, hEa2, h8mA, h4mA2]
    have hY_b : ‖Y‖ ≤ 4 * (m : ℝ) * A := by
      rw [hY_def]
      have h := norm_add_le β Eb
      nlinarith [h, hβ_b, hEb2, h8mA, h4mA2]
    have hZ_b : ‖Z‖ ≤ 2 * (m : ℝ) * C := by
      rw [hZ_def]
      have h := norm_add_le (-γ) Ec
      have hneg : ‖-γ‖ = ‖γ‖ := norm_neg γ
      have h2mC2 : 2 * (m : ℝ) ^ 2 * C ^ 2 ≤ (m : ℝ) * C := by
        nlinarith [hmC, hmC0]
      nlinarith [h, hneg, hγ_b, hEc2, h2mC2]
    have hXY : ‖X‖ * ‖Y‖ ≤ 16 * (m : ℝ) ^ 2 * A ^ 2 := by
      have h := mul_le_mul hX_b hY_b (norm_nonneg Y) h4mA
      nlinarith [h]
    have hXZ : ‖X‖ * ‖Z‖ ≤ 8 * (m : ℝ) ^ 2 * A * C := by
      have h := mul_le_mul hX_b hZ_b (norm_nonneg Z) h4mA
      nlinarith [h]
    have hYZ : ‖Y‖ * ‖Z‖ ≤ 8 * (m : ℝ) ^ 2 * A * C := by
      have h := mul_le_mul hY_b hZ_b (norm_nonneg Z) h4mA
      nlinarith [h]
    have hXYZ : ‖X‖ * ‖Y‖ * ‖Z‖ ≤ 8 * (m : ℝ) ^ 2 * A * C := by
      have h1 : ‖X‖ * ‖Y‖ ≤ (4 * (m : ℝ) * A) * (4 * (m : ℝ) * A) :=
        mul_le_mul hX_b hY_b (norm_nonneg Y) h4mA
      have h2 : ‖X‖ * ‖Y‖ * ‖Z‖ ≤ ((4 * (m : ℝ) * A) * (4 * (m : ℝ) * A)) * (2 * (m : ℝ) * C) :=
        mul_le_mul h1 hZ_b (norm_nonneg Z) (mul_nonneg h4mA h4mA)
      have hpos : (0:ℝ) ≤ 8 * (m : ℝ) ^ 2 * A * C := by positivity
      nlinarith [h2, hmA, hm0', hA, hC, hpos]
    refine ⟨Ea + Eb + Ec + X * Y + X * Z + Y * Z + X * Y * Z, ?_, ?_⟩
    · have hsum : ‖Ea + Eb + Ec + X*Y + X*Z + Y*Z + X*Y*Z‖
          ≤ ‖Ea‖ + ‖Eb‖ + ‖Ec‖ + ‖X‖*‖Y‖ + ‖X‖*‖Z‖ + ‖Y‖*‖Z‖ + ‖X‖*‖Y‖*‖Z‖ := by
        have h1 := norm_add_le (Ea + Eb + Ec + X*Y + X*Z + Y*Z) (X*Y*Z)
        have h2 := norm_add_le (Ea + Eb + Ec + X*Y + X*Z) (Y*Z)
        have h3 := norm_add_le (Ea + Eb + Ec + X*Y) (X*Z)
        have h4 := norm_add_le (Ea + Eb + Ec) (X*Y)
        have h5 := norm_add_le (Ea + Eb) Ec
        have h6 := norm_add_le Ea Eb
        have h7 := norm_mul X Y
        have h8 := norm_mul X Z
        have h9 := norm_mul Y Z
        have h10 := norm_mul (X*Y) Z
        nlinarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
      have hR0 : (0:ℝ) ≤ A ^ 2 + A * C + C ^ 2 := by positivity
      have hfin : ‖Ea‖ + ‖Eb‖ + ‖Ec‖ + ‖X‖*‖Y‖ + ‖X‖*‖Z‖ + ‖Y‖*‖Z‖ + ‖X‖*‖Y‖*‖Z‖
          ≤ 10000 * ((m : ℝ) ^ 2 + m) * (A ^ 2 + A * C + C ^ 2) := by
        nlinarith [hEa2, hEb2, hEc2, hXY, hXZ, hYZ, hXYZ, hm0', hA, hC, hR0,
          sq_nonneg (m : ℝ), sq_nonneg A, sq_nonneg C, mul_nonneg hA hC]
      linarith [hsum, hfin]
    · have hLHS : ∏ j, ((1 - a j)⁻¹ * (1 - b j)⁻¹ * (1 - c j)) = Pa * Pb * Pc := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← hPa_def, ← hPb_def, ← hPc_def]
      have hRHS : ∑ j, (a j + b j - c j) = α + β - γ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← hα_def, ← hβ_def, ← hγ_def]
      rw [hLHS, hRHS, hX_def, hY_def, hZ_def, hEa_def, hEb_def, hEc_def]
      ring

/-- Second-order expansion of a product of the form `∏_j (1-a_j)⁻¹(1-b_j)⁻¹(1-c_j)`, where the
`a_j, b_j, c_j` are small complex numbers (`‖a_j‖,‖b_j‖ ≤ A`, `‖c_j‖ ≤ C`).

For `A, C ≥ 0`, `A ≤ 1`, `C ≤ 1`, `m·(2A + C) ≤ 1/2`, there is `S` with
`∏_j (1-a_j)⁻¹(1-b_j)⁻¹(1-c_j) = 1 + ∑_j (a_j + b_j - c_j) + S` and
`‖S‖ ≤ 10000·(m² + m)·(A² + AC + C²)`.

Proof sketch (the ingredients are the present commons lemmas):
* `Commons.Analysis.Complex.inv_one_sub_approx` gives, when `‖a‖ ≤ 1/2`,
  `(1-a)⁻¹ = 1 + a + ε` with `‖ε‖ ≤ 4‖a‖²`;
* hence each factor is `(1+a+ε₁)(1+b+ε₂)(1-c) = 1 + (a+b-c) + η` with
  `η = ab - ac - bc - abc + (ε₁+ε₂)(1-c) + aε₂ + ε₁b + ε₁ε₂`, so `‖η‖ ≤ 45(A² + AC)` using
  `A, C ≤ 1` (`‖ab‖ ≤ A²`, `‖ac‖,‖bc‖ ≤ AC`, `‖abc‖ ≤ A²`, `‖ε‖(1+‖c‖) ≤ 8A²`, `‖a‖‖ε‖ ≤ 4A³ ≤ 4A²`,
  `‖ε₁‖‖ε₂‖ ≤ 16A⁴ ≤ 16A²`);
* then `∏_j (1 + (a_j+b_j-c_j) + η_j) = 1 + ∑_j(a_j+b_j-c_j) + ∑_j η_j + ρ` with
  `‖ρ‖ ≤ (∑_j ‖a_j+b_j-c_j+η_j‖)²` by
  `Commons.Analysis.Complex.norm_prod_one_add_sub_one_sub_sum_le` (its hypothesis
  `∑_j ‖···‖ ≤ 1` follows from `m(2A+C) ≤ 1/2` and `A,C ≤ 1`);
* finally `(∑_j ‖a_j+b_j-c_j+η_j‖)² ≤ (m(2A+C+45(A²+AC)))² ≤ m²(2A+C)²(1+45A)²
  ≤ 5000 m²(A² + AC + C²)` and `∑_j ‖η_j‖ ≤ 45m(A²+AC)`.

`m = 0` is allowed (then everything is `1` and `S = 0`). -/
theorem inv_prod_three_expansion {m : ℕ} (z z' : Fin m → ℂ) {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hA1 : A ≤ 1) (hC1 : C ≤ 1)
    (hm : (m : ℝ) * (2 * A + C) ≤ 1 / 2)
    {p : ℕ} (ha : ∀ j, ‖(p : ℂ) ^ (-(1 + z j))‖ ≤ A)
    (hb : ∀ j, ‖(p : ℂ) ^ (-(1 + z' j))‖ ≤ A)
    (hc : ∀ j, ‖(p : ℂ) ^ (-(1 + z j + z' j))‖ ≤ C) :
    ∃ S : ℂ, ‖S‖ ≤ 10000 * ((m : ℝ) ^ 2 + m) * (A ^ 2 + A * C + C ^ 2)
      ∧ (∏ j, ((1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j)))
            * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹))⁻¹
        = 1 + ∑ j, ((p : ℂ) ^ (-(1 + z j)) + (p : ℂ) ^ (-(1 + z' j))
            - (p : ℂ) ^ (-(1 + z j + z' j))) + S := by
  obtain ⟨S, hS, hSeq⟩ := inv_prod_three_expansion_aux
      (fun j => (p : ℂ) ^ (-(1 + z j))) (fun j => (p : ℂ) ^ (-(1 + z' j)))
      (fun j => (p : ℂ) ^ (-(1 + z j + z' j))) hA hC hA1 hC1 hm ha hb hc
  refine ⟨S, hS, ?_⟩
  have hL : (∏ j, ((1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j)))
        * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹))⁻¹
      = ∏ j, ((1 - (p : ℂ) ^ (-(1 + z j)))⁻¹ * (1 - (p : ℂ) ^ (-(1 + z' j)))⁻¹
        * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))) := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [mul_inv, mul_inv, inv_inv]
  rw [hL, hSeq]

end Commons.Analysis.Complex