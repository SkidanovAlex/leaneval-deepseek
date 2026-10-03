import Mathlib
import Submission.Work.Peluse.Prop36SW.lstatePeelFin
import Submission.Work.Peluse.UControl.bandCore

namespace Work.Peluse.Prop36SW

theorem peelStrengthLower (Dc K t' Q sh : ℕ) (C₀ c : ℝ) (hC₀ : 0 < C₀) (hc : 0 < c) :
    ∃ cc₂ : ℝ, 0 < cc₂ ∧
      ∀ (N : ℕ) (γ : ℝ), 1 ≤ N → 0 < γ → γ ≤ 1 →
        cc₂ * γ ^ (K * (K + 1) * 2 ^ Q)
          ≤ min ((((Work.Peluse.symIcc N).card : ℝ) /
                  ((Work.Peluse.symIcc
                    (Work.Peluse.Prop36SW.peelN N Dc t' (γ ^ K / C₀))).card : ℝ)) ^
                  (1 / (2 : ℝ) ^ sh) *
                  (c * (γ * (γ ^ K / C₀)) ^ K) ^ (2 ^ Q)) 1 := by
  -- The peel strength bound of the §5 round: the peeled strength
  -- `min (ratio · (c(γγ')^K)^{2^Q}) 1` dominates `cc₂ · γ^{K(K+1)2^Q}`.
  -- The only non-trivial input is that the ambient ratio
  -- `|symIcc N| / |symIcc (peelN N Dc t' γ')|` is bounded below uniformly in `N, γ`.
  set M₀ : ℕ := ⌈(Dc : ℝ) / C₀⌉₊ with hM₀
  set R₀ : ℝ := 1 / (1 + (t' : ℝ) * (M₀ : ℝ)) with hR₀
  have hR₀pos : 0 < R₀ := by rw [hR₀]; positivity
  have hbasepos : 0 < c / C₀ ^ K := by positivity
  refine ⟨min (R₀ * (c / C₀ ^ K) ^ (2 ^ Q)) 1, ?_, ?_⟩
  · exact lt_min (mul_pos hR₀pos (pow_pos hbasepos _)) one_pos
  · intro N γ hN hγ0 hγ1
    set γ' : ℝ := γ ^ K / C₀ with hγ'
    set m : ℕ := ⌈γ' * (Dc : ℝ)⌉₊ with hm
    set pN : ℕ := Work.Peluse.Prop36SW.peelN N Dc t' γ' with hpN
    have hcardNat : ∀ n : ℕ, (Work.Peluse.symIcc n).card = 2 * n + 1 :=
      Work.Peluse.UControl.card_symIcc
    have hγKpos : 0 < γ ^ K := pow_pos hγ0 K
    have hγKle1 : γ ^ K ≤ 1 := pow_le_one₀ hγ0.le hγ1
    -- the ceiling `m = ⌈γ^K Dc / C₀⌉₊` is at most `M₀ = ⌈Dc / C₀⌉₊`
    have hmle : m ≤ M₀ := by
      rw [hm, hM₀]
      apply Nat.ceil_le_ceil
      have h : γ' * (Dc : ℝ) = (γ ^ K) * ((Dc : ℝ) / C₀) := by rw [hγ']; ring
      rw [h]
      have h2 : (0:ℝ) ≤ (Dc : ℝ) / C₀ := by positivity
      calc (γ ^ K) * ((Dc : ℝ) / C₀) ≤ 1 * ((Dc : ℝ) / C₀) :=
            mul_le_mul_of_nonneg_right hγKle1 h2
        _ = (Dc : ℝ) / C₀ := one_mul _
    have hpNdef : pN = N * (1 + t' * m) := by
      rw [hpN, Work.Peluse.Prop36SW.peelN, hm]
    have hNle : N ≤ pN := by
      rw [hpNdef]
      calc N = N * 1 := (mul_one N).symm
        _ ≤ N * (1 + t' * m) := Nat.mul_le_mul_left N (by omega)
    have hpNle : pN ≤ N * (1 + t' * M₀) := by
      rw [hpNdef]
      refine Nat.mul_le_mul_left N ?_
      exact Nat.add_le_add_left (Nat.mul_le_mul_left t' hmle) 1
    have hcardN : ((Work.Peluse.symIcc N).card : ℝ) = 2 * (N : ℝ) + 1 := by
      rw [hcardNat]; push_cast; ring
    have hcardP : ((Work.Peluse.symIcc pN).card : ℝ) = 2 * (pN : ℝ) + 1 := by
      rw [hcardNat]; push_cast; ring
    have hcardNpos : 0 < ((Work.Peluse.symIcc N).card : ℝ) := by rw [hcardN]; positivity
    have hcardPpos : 0 < ((Work.Peluse.symIcc pN).card : ℝ) := by rw [hcardP]; positivity
    -- the ambient ratio is at most `1`
    have hRle1 : ((Work.Peluse.symIcc N).card : ℝ) /
        ((Work.Peluse.symIcc pN).card : ℝ) ≤ 1 := by
      rw [hcardN, hcardP, div_le_one (by positivity)]
      have : (N:ℝ) ≤ (pN:ℝ) := by exact_mod_cast hNle
      linarith
    -- and at least `R₀`
    have hRge : R₀ ≤ ((Work.Peluse.symIcc N).card : ℝ) /
        ((Work.Peluse.symIcc pN).card : ℝ) := by
      rw [hcardN, hcardP, hR₀]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (pN : ℝ) + 1)]
      have hden : 0 < 1 + (t' : ℝ) * (M₀ : ℝ) := by positivity
      have hpNleR : (pN : ℝ) ≤ (N : ℝ) * (1 + (t' : ℝ) * (M₀ : ℝ)) := by
        have h := hpNle
        have h' : (pN : ℝ) ≤ ((N * (1 + t' * M₀) : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at h'
        linarith
      have h2 : 2 * (pN : ℝ) + 1 ≤ (2 * (N : ℝ) + 1) * (1 + (t' : ℝ) * (M₀ : ℝ)) := by
        nlinarith [hpNleR, hden]
      calc (1 / (1 + (t' : ℝ) * (M₀ : ℝ))) * (2 * (pN : ℝ) + 1)
          ≤ (1 / (1 + (t' : ℝ) * (M₀ : ℝ))) *
              ((2 * (N : ℝ) + 1) * (1 + (t' : ℝ) * (M₀ : ℝ))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 * (N : ℝ) + 1 := by field_simp
    -- the exponent `1 / 2^sh` is at most `1`, so the ratio power is at least the ratio
    have hF1 : R₀ ≤ ((((Work.Peluse.symIcc N).card : ℝ) /
        ((Work.Peluse.symIcc pN).card : ℝ)) ^ (1 / (2 : ℝ) ^ sh)) := by
      have hRpos : 0 < ((Work.Peluse.symIcc N).card : ℝ) /
          ((Work.Peluse.symIcc pN).card : ℝ) := div_pos hcardNpos hcardPpos
      have hexp : (1:ℝ) / (2:ℝ) ^ sh ≤ 1 := by
        rw [div_le_one (by positivity : (0:ℝ) < (2:ℝ)^sh)]
        have := Nat.one_le_two_pow (n := sh)
        exact_mod_cast this
      have h := Real.rpow_le_rpow_of_exponent_ge hRpos hRle1 hexp
      rw [Real.rpow_one] at h
      exact le_trans hRge h
    -- the second factor is exactly `(c / C₀^K)^{2^Q} · γ^{K(K+1)2^Q}`
    have hF2 : (c * (γ * (γ ^ K / C₀)) ^ K) ^ (2 ^ Q)
        = (c / C₀ ^ K) ^ (2 ^ Q) * γ ^ (K * (K + 1) * 2 ^ Q) := by
      have hbase : c * (γ * (γ ^ K / C₀)) ^ K = (c / C₀ ^ K) * γ ^ (K * (K + 1)) := by
        have h1 : γ * (γ ^ K / C₀) = γ ^ (K + 1) / C₀ := by rw [← mul_div_assoc, ← pow_succ']
        have h2 : (γ ^ (K + 1) / C₀) ^ K = γ ^ (K * (K + 1)) / C₀ ^ K := by
          rw [div_pow, ← pow_mul]
          rw [show (K + 1) * K = K * (K + 1) by ring]
        rw [h1, h2]
        ring
      rw [hbase, mul_pow, ← pow_mul]
    have hF2nn : 0 ≤ (c * (γ * (γ ^ K / C₀)) ^ K) ^ (2 ^ Q) := by
      have h1 : 0 ≤ γ * (γ ^ K / C₀) := by positivity
      have h2 : 0 ≤ c * (γ * (γ ^ K / C₀)) ^ K := by positivity
      exact pow_nonneg h2 _
    have hγEnn : 0 ≤ γ ^ (K * (K + 1) * 2 ^ Q) := pow_nonneg hγ0.le _
    have hγE1 : γ ^ (K * (K + 1) * 2 ^ Q) ≤ 1 := pow_le_one₀ hγ0.le hγ1
    refine le_min ?_ ?_
    · calc min (R₀ * (c / C₀ ^ K) ^ (2 ^ Q)) 1 * γ ^ (K * (K + 1) * 2 ^ Q)
          ≤ R₀ * (c / C₀ ^ K) ^ (2 ^ Q) * γ ^ (K * (K + 1) * 2 ^ Q) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hγEnn
        _ = R₀ * (c * (γ * (γ ^ K / C₀)) ^ K) ^ (2 ^ Q) := by
            rw [hF2]; ring
        _ ≤ ((((Work.Peluse.symIcc N).card : ℝ) /
              ((Work.Peluse.symIcc pN).card : ℝ)) ^ (1 / (2 : ℝ) ^ sh)) *
              (c * (γ * (γ ^ K / C₀)) ^ K) ^ (2 ^ Q) :=
            mul_le_mul_of_nonneg_right hF1 hF2nn
    · calc min (R₀ * (c / C₀ ^ K) ^ (2 ^ Q)) 1 * γ ^ (K * (K + 1) * 2 ^ Q)
          ≤ 1 * γ ^ (K * (K + 1) * 2 ^ Q) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hγEnn
        _ ≤ 1 := by rw [one_mul]; exact hγE1

end Work.Peluse.Prop36SW
