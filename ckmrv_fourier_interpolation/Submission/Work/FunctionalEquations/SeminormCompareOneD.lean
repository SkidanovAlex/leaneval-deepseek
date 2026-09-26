import Submission.Work.FunctionalEquations.SeminormCompareAux

open scoped ContDiff BigOperators
open Polynomial

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.FunctionalEquations

theorem oneD_bound_gen (Q b : ℕ) (hb : b ≤ Q) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
      (g : ℝ → V), ContDiff ℝ (Q : ℕ∞ω) g → ∀ (R M N : ℝ),
      0 < R → 0 ≤ M → 0 ≤ N →
      (∀ t ∈ Set.Icc (0:ℝ) R, ‖g t‖ ≤ M) →
      (∀ t ∈ Set.Icc (0:ℝ) R, ‖iteratedDeriv Q g t‖ ≤ N) →
      ‖iteratedDeriv b g 0‖ ≤ c * (M / R ^ b + R ^ (Q - b) * N) := by
  classical
  let αf : ℕ → Fin Q → ℝ := fun b' => Classical.choose (exists_extraction_coeffs Q b')
  have hαf : ∀ b' : ℕ, ∀ i : Fin Q,
      ∑ j : Fin Q, αf b' j * (j : ℝ) ^ (i : ℕ) = if (i : ℕ) = b' then 1 else 0 :=
    fun b' => Classical.choose_spec (exists_extraction_coeffs Q b')
  let cfun : ℕ → ℝ := fun b' =>
    max 1 (2 * ((Nat.factorial b' : ℝ) * (∑ j : Fin Q, |αf b' j|) * (2 * (Q:ℝ))^b'))
  have hcfun_nonneg : ∀ b' : ℕ, 0 ≤ cfun b' := fun b' =>
    le_trans zero_le_one (le_max_left _ _)
  refine ⟨∑ b' ∈ Finset.range (Q + 1), cfun b',
    Finset.sum_nonneg fun b' _ => hcfun_nonneg b', ?_⟩
  intro V _ _ g hg R M N hR hM hN hgM hgN
  have hcle : cfun b ≤ ∑ b' ∈ Finset.range (Q + 1), cfun b' :=
    Finset.single_le_sum (fun b' _ => hcfun_nonneg b') (Finset.mem_range.mpr (by omega))
  have hc1 : (1 : ℝ) ≤ ∑ b' ∈ Finset.range (Q + 1), cfun b' :=
    le_trans (le_max_left 1 _) hcle
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    have hx : ‖iteratedDeriv 0 g 0‖ ≤ M := by
      simpa using hgM 0 (Set.left_mem_Icc.mpr hR.le)
    rw [pow_zero, Nat.sub_zero]
    calc ‖iteratedDeriv 0 g 0‖ ≤ M := hx
      _ ≤ (∑ b' ∈ Finset.range (Q + 1), cfun b') * (M / 1 + R ^ Q * N) := by
          have h0 : (0:ℝ) ≤ R ^ Q * N := mul_nonneg (pow_nonneg hR.le _) hN
          calc M ≤ 1 * (M + R ^ Q * N) := by linarith
            _ ≤ (∑ b' ∈ Finset.range (Q + 1), cfun b') * (M + R ^ Q * N) :=
                mul_le_mul_of_nonneg_right hc1 (by linarith)
            _ = (∑ b' ∈ Finset.range (Q + 1), cfun b') * (M / 1 + R ^ Q * N) := by ring
  · rcases lt_or_eq_of_le hb with hblt | hbeq
    · -- main case: 0 < b < Q
      have hbQ1 : 1 ≤ Q := by omega
      have hQposn : 0 < Q := by omega
      have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQposn
      let S : ℝ := ∑ j : Fin Q, |αf b j|
      have hSnn : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
      set h : ℝ := R / (2 * (Q:ℝ)) with hh
      have hhpos : 0 < h := by rw [hh]; positivity
      set tj : Fin Q → ℝ := fun j => (j : ℝ) * h with htjE
      have htj_mem : ∀ j : Fin Q, tj j ∈ Set.Icc (0:ℝ) R := by
        intro j
        constructor
        · rw [htjE]; exact mul_nonneg (Nat.cast_nonneg _) hhpos.le
        · rw [htjE]
          have hle : (j : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (le_of_lt j.isLt)
          calc (j:ℝ) * h ≤ (Q:ℝ) * h := mul_le_mul_of_nonneg_right hle hhpos.le
            _ = (Q:ℝ) * (R / (2*(Q:ℝ))) := by rw [hh]
            _ = R / 2 := by field_simp
            _ ≤ R := by linarith
      let v : Fin Q → V := fun k => iteratedDeriv (k : ℕ) g 0
      set Rem : Fin Q → V := fun j => g (tj j) - ∑ k : Fin Q,
        ((Nat.factorial (k:ℕ) : ℝ)⁻¹ * (tj j)^(k:ℕ)) • v k with hRemE
      have hRem : ∀ j : Fin Q, ‖Rem j‖ ≤ N * R^Q / ((Q-1).factorial : ℝ) := by
        intro j
        have hbase := taylor_remainder_bound_V (V := V) (g := g) (Q := Q)
          hbQ1 hg (x₀ := 0) (t := tj j) (N := N) (htj_mem j).1 hN
          (fun s hs => hgN s (Set.Icc_subset_Icc_right (htj_mem j).2 hs))
        have hsum : (∑ k ∈ Finset.range Q,
              ((Nat.factorial k : ℝ)⁻¹ * (tj j - 0) ^ k) • iteratedDeriv k g 0)
            = ∑ k : Fin Q, ((Nat.factorial (k:ℕ) : ℝ)⁻¹ * (tj j) ^ (k:ℕ)) • v k := by
          rw [← Fin.sum_univ_eq_sum_range
            (f := fun k => ((Nat.factorial k : ℝ)⁻¹ * (tj j - 0) ^ k) • iteratedDeriv k g 0) Q]
          simp only [v, sub_zero]
        rw [hsum, sub_zero] at hbase
        have hfpos : 0 < ((Q-1).factorial : ℝ) := by positivity
        have hpow : (tj j)^Q ≤ R^Q :=
          pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hhpos.le) (htj_mem j).2 Q
        rw [hRemE]
        calc ‖g (tj j) - ∑ k : Fin Q, ((Nat.factorial (k:ℕ) : ℝ)⁻¹ * (tj j)^(k:ℕ)) • v k‖
            ≤ N * (tj j)^Q / ((Q-1).factorial : ℝ) := hbase
          _ ≤ N * R^Q / ((Q-1).factorial : ℝ) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hN) hfpos.le
      set C : Fin Q → ℝ := fun k =>
        (Nat.factorial (k:ℕ) : ℝ)⁻¹ * h^(k:ℕ) * (∑ j : Fin Q, αf b j * (j:ℝ)^(k:ℕ)) with hCE
      have hCeq : ∀ k : Fin Q, (∑ j : Fin Q,
            αf b j * ((Nat.factorial (k:ℕ) : ℝ)⁻¹ * (tj j)^(k:ℕ))) = C k := by
        intro k
        simp only [hCE]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [htjE]
        rw [mul_pow]
        ring
      have hC0 : ∀ k : Fin Q, k ≠ ⟨b, hblt⟩ → C k = 0 := by
        intro k hk
        simp only [hCE]
        have hne : (k:ℕ) ≠ b := fun hc => hk (Fin.ext hc)
        rw [hαf b k, if_neg hne, mul_zero]
      have hC1 : C ⟨b, hblt⟩ = (Nat.factorial b : ℝ)⁻¹ * h^b := by
        simp only [hCE]
        rw [hαf b ⟨b, hblt⟩, if_pos rfl, mul_one]
      have key : (∑ j : Fin Q, αf b j • g (tj j))
          = ((Nat.factorial b : ℝ)⁻¹ * h^b) • v ⟨b, hblt⟩ + ∑ j : Fin Q, αf b j • Rem j := by
        have step1 : (∑ j : Fin Q, αf b j • g (tj j))
            = ∑ j : Fin Q, αf b j • ((∑ k : Fin Q,
                ((Nat.factorial (k:ℕ) : ℝ)⁻¹ * (tj j)^(k:ℕ)) • v k) + Rem j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          rw [hRemE]
          exact (add_sub_cancel _ _).symm
        have step2 : (∑ j : Fin Q, αf b j • ((∑ k : Fin Q,
              ((Nat.factorial (k:ℕ) : ℝ)⁻¹ * (tj j)^(k:ℕ)) • v k) + Rem j))
            = (∑ j : Fin Q, ∑ k : Fin Q,
                (αf b j * ((Nat.factorial (k:ℕ) : ℝ)⁻¹ * (tj j)^(k:ℕ))) • v k)
              + ∑ j : Fin Q, αf b j • Rem j := by
          simp only [smul_add]
          rw [Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [smul_smul]
        have step3 : (∑ j : Fin Q, ∑ k : Fin Q,
                (αf b j * ((Nat.factorial (k:ℕ) : ℝ)⁻¹ * (tj j)^(k:ℕ))) • v k)
            = ((Nat.factorial b : ℝ)⁻¹ * h^b) • v ⟨b, hblt⟩ := by
          rw [Finset.sum_comm]
          rw [show (∑ k : Fin Q, ∑ j : Fin Q,
                (αf b j * ((Nat.factorial (k:ℕ) : ℝ)⁻¹ * (tj j)^(k:ℕ))) • v k)
              = ∑ k : Fin Q, C k • v k from by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Finset.sum_smul, hCeq k]]
          rw [Finset.sum_eq_single ⟨b, hblt⟩]
          · rw [hC1]
          · intro k _ hk
            rw [hC0 k hk, zero_smul]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
        rw [step1, step2, step3]
      have hnorm : ((Nat.factorial b : ℝ)⁻¹ * h^b) * ‖v ⟨b, hblt⟩‖
          ≤ S * (M + N * R^Q / ((Q-1).factorial : ℝ)) := by
        have h1 : ‖((Nat.factorial b : ℝ)⁻¹ * h^b) • v ⟨b, hblt⟩‖
            = ((Nat.factorial b : ℝ)⁻¹ * h^b) * ‖v ⟨b, hblt⟩‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        have hkey' : ((Nat.factorial b : ℝ)⁻¹ * h^b) • v ⟨b, hblt⟩
            = (∑ j : Fin Q, αf b j • g (tj j)) - ∑ j : Fin Q, αf b j • Rem j := by
          rw [key]; abel
        rw [← h1, hkey']
        have hA : ‖∑ j : Fin Q, αf b j • g (tj j)‖ ≤ S * M := by
          calc ‖∑ j : Fin Q, αf b j • g (tj j)‖ ≤ ∑ j : Fin Q, ‖αf b j • g (tj j)‖ := norm_sum_le _ _
            _ = ∑ j : Fin Q, |αf b j| * ‖g (tj j)‖ := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [norm_smul, Real.norm_eq_abs]
            _ ≤ ∑ j : Fin Q, |αf b j| * M := Finset.sum_le_sum fun j _ =>
                mul_le_mul_of_nonneg_left (hgM (tj j) (htj_mem j)) (abs_nonneg _)
            _ = S * M := by rw [← Finset.sum_mul]
        have hB : ‖∑ j : Fin Q, αf b j • Rem j‖ ≤ S * (N * R^Q / ((Q-1).factorial : ℝ)) := by
          calc ‖∑ j : Fin Q, αf b j • Rem j‖ ≤ ∑ j : Fin Q, ‖αf b j • Rem j‖ := norm_sum_le _ _
            _ = ∑ j : Fin Q, |αf b j| * ‖Rem j‖ := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [norm_smul, Real.norm_eq_abs]
            _ ≤ ∑ j : Fin Q, |αf b j| * (N * R^Q / ((Q-1).factorial : ℝ)) :=
                Finset.sum_le_sum fun j _ =>
                  mul_le_mul_of_nonneg_left (hRem j) (abs_nonneg _)
            _ = S * (N * R^Q / ((Q-1).factorial : ℝ)) := by rw [← Finset.sum_mul]
        calc ‖(∑ j : Fin Q, αf b j • g (tj j)) - ∑ j : Fin Q, αf b j • Rem j‖
            ≤ ‖∑ j : Fin Q, αf b j • g (tj j)‖ + ‖∑ j : Fin Q, αf b j • Rem j‖ := norm_sub_le _ _
          _ ≤ S * M + S * (N * R^Q / ((Q-1).factorial : ℝ)) := add_le_add hA hB
          _ = S * (M + N * R^Q / ((Q-1).factorial : ℝ)) := by ring
      have hApos : 0 < (Nat.factorial b : ℝ)⁻¹ * h^b := by positivity
      have hAinv : ((Nat.factorial b : ℝ)⁻¹ * h^b)⁻¹ =
          (Nat.factorial b : ℝ) * (2 * (Q:ℝ))^b / R^b := by
        rw [mul_inv, hh, div_pow, inv_div, inv_inv]
        ring
      have hstep : ‖v ⟨b, hblt⟩‖ ≤
          ((Nat.factorial b : ℝ)⁻¹ * h^b)⁻¹ * (S * (M + N * R^Q / ((Q-1).factorial : ℝ))) := by
        calc ‖v ⟨b, hblt⟩‖
            = ((Nat.factorial b : ℝ)⁻¹ * h^b)⁻¹ *
                (((Nat.factorial b : ℝ)⁻¹ * h^b) * ‖v ⟨b, hblt⟩‖) := by
                rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hApos), one_mul]
          _ ≤ ((Nat.factorial b : ℝ)⁻¹ * h^b)⁻¹ *
                (S * (M + N * R^Q / ((Q-1).factorial : ℝ))) :=
                mul_le_mul_of_nonneg_left hnorm (by positivity)
      have hfact_ge : (1:ℝ) ≤ ((Q-1).factorial : ℝ) := by
        have h1 : 1 ≤ (Q-1).factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
        exact_mod_cast h1
      have hle1 : N * R^Q / ((Q-1).factorial : ℝ) ≤ N * R^Q := by
        rw [div_le_iff₀ (by positivity)]
        have h0 : (0:ℝ) ≤ N * R^Q := mul_nonneg hN (pow_nonneg hR.le _)
        nlinarith [hfact_ge, h0]
      have hsplit : M / R^b + R^(Q-b) * N = (M + R^Q * N) / R^b := by
        have h1 : R ^ (Q - b) = R^Q / R^b := by
          rw [pow_sub₀ R hR.ne' hb, div_eq_mul_inv]
        rw [add_div, h1]
        ring
      have hbase_nonneg : (0:ℝ) ≤ (Nat.factorial b : ℝ) * (∑ j : Fin Q, |αf b j|)
          * (2 * (Q:ℝ))^b := by
        have h1 : (0:ℝ) ≤ (∑ j : Fin Q, |αf b j|) :=
          Finset.sum_nonneg fun j _ => abs_nonneg _
        positivity
      have hcv : (Nat.factorial b : ℝ) * S * (2 * (Q:ℝ))^b ≤ cfun b := by
        have h2 : (Nat.factorial b : ℝ) * (∑ j : Fin Q, |αf b j|) * (2 * (Q:ℝ))^b
            ≤ 2 * ((Nat.factorial b : ℝ) * (∑ j : Fin Q, |αf b j|) * (2 * (Q:ℝ))^b) := by
          linarith [hbase_nonneg]
        exact le_trans h2 (le_max_right _ _)
      calc ‖iteratedDeriv b g 0‖
          = ‖v ⟨b, hblt⟩‖ := rfl
        _ ≤ (Nat.factorial b : ℝ) * (2 * (Q:ℝ))^b / R^b *
              (S * (M + N * R^Q / ((Q-1).factorial : ℝ))) := by
            rw [hAinv] at hstep
            exact hstep
        _ ≤ (Nat.factorial b : ℝ) * (2 * (Q:ℝ))^b / R^b * (S * (M + N * R^Q)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left (by linarith [hle1]) hSnn
        _ = (Nat.factorial b : ℝ) * S * (2 * (Q:ℝ))^b * (M + R^Q * N) / R^b := by ring
        _ ≤ cfun b * (M + R^Q * N) / R^b := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hcv (by positivity)
        _ = cfun b * (M / R^b + R^(Q-b) * N) := by rw [hsplit]; ring
        _ ≤ (∑ b' ∈ Finset.range (Q + 1), cfun b') * (M / R^b + R^(Q-b) * N) :=
            mul_le_mul_of_nonneg_right hcle (by positivity)
    · -- b = Q
      rw [hbeq]
      have hx : ‖iteratedDeriv Q g 0‖ ≤ N := hgN 0 (Set.left_mem_Icc.mpr hR.le)
      rw [Nat.sub_self, pow_zero]
      calc ‖iteratedDeriv Q g 0‖ ≤ N := hx
        _ ≤ (∑ b' ∈ Finset.range (Q + 1), cfun b') * (M / R ^ Q + 1 * N) := by
            have h0 : (0:ℝ) ≤ M / R^Q := div_nonneg hM (pow_nonneg hR.le _)
            calc N ≤ 1 * (M / R ^ Q + 1 * N) := by linarith
              _ ≤ (∑ b' ∈ Finset.range (Q + 1), cfun b') * (M / R ^ Q + 1 * N) :=
                  mul_le_mul_of_nonneg_right hc1 (by linarith)

end Work.FunctionalEquations
