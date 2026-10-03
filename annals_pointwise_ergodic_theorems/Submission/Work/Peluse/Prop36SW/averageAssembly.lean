import Mathlib

namespace Work.Peluse.Prop36SW

/-- Averaging assembly used in the proof of Proposition 3.6 (`SW` variant):

On a "core" set `A ⊆ cc` carrying at least three quarters of the mass `η·|cc|` of the
function `F` (which is bounded by `1` on `cc`), and on which `F` is controlled by the
average of `G` in the second variable, the double average of `G` dominates
`η / 2^(1 + 2 Ncard)`. -/
theorem averageAssembly {α β : Type} [DecidableEq α] [DecidableEq β]
    {cc A : Finset α} {Pb : Finset β} {F : α → ℝ} {G : α → β → ℝ} {η C : ℝ} {Ncard : ℕ}
    (hCpos : 0 < C)
    (hA : A ⊆ cc) (hF0 : ∀ a ∈ cc, 0 ≤ F a) (hF1 : ∀ a ∈ cc, F a ≤ 1) (hη1 : η ≤ 1)
    (hη : η ≤ (cc.card : ℝ)⁻¹ * ∑ a ∈ cc, F a)
    (hgood : 4 * ((cc \ A).card : ℝ) ≤ η * (cc.card : ℝ))
    (hcore : ∀ a ∈ A, F a ≤ C * ((Pb.card : ℝ)⁻¹ * ∑ b ∈ Pb, G a b))
    (hC : C * ((4 : ℝ) ^ Ncard)⁻¹ ≤ 1) :
    η / 2 ^ (1 + 2 * Ncard) ≤ (A.card : ℝ)⁻¹ * (Pb.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ Pb, G a b := by
  classical
  set u : α → ℝ := fun a => (Pb.card : ℝ)⁻¹ * ∑ b ∈ Pb, G a b with hu
  set T : ℝ := (A.card : ℝ)⁻¹ * (Pb.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ Pb, G a b with hT
  have hcoreU : ∀ a ∈ A, F a ≤ C * u a := by
    intro a ha
    have h := hcore a ha
    simp only [hu]
    exact h
  by_cases hAcard : A.card = 0
  · have hAeq : A = ∅ := Finset.card_eq_zero.mp hAcard
    have hcc0 : cc = ∅ := by
      by_contra hne
      have hccn : cc.card ≠ 0 := by simpa [Finset.card_eq_zero] using hne
      have hcardpos : 0 < (cc.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hccn)
      have hg : 4 * ((cc \ A).card : ℝ) ≤ η * (cc.card : ℝ) := hgood
      rw [hAeq, Finset.sdiff_empty] at hg
      have h4 : 4 ≤ η := (mul_le_mul_iff_of_pos_right hcardpos).mp hg
      linarith
    have hη0 : η ≤ 0 := by
      rw [hcc0] at hη
      simpa using hη
    rw [hT]
    have hz : (A.card : ℝ)⁻¹ * (Pb.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ Pb, G a b = 0 := by
      simp [hAeq]
    rw [hz]
    exact div_nonpos_of_nonpos_of_nonneg hη0 (by positivity)
  · have hAcardpos : 0 < A.card := Nat.pos_of_ne_zero hAcard
    have hmApos : 0 < (A.card : ℝ) := by exact_mod_cast hAcardpos
    have hmAinv_nn : (0 : ℝ) ≤ (A.card : ℝ)⁻¹ := by positivity
    have hCinv_nn : (0 : ℝ) ≤ 1 / C := by positivity
    have hFsum_nonneg : 0 ≤ ∑ a ∈ A, F a := by
      apply Finset.sum_nonneg
      intro a ha
      exact hF0 a (hA ha)
    have havg_nonneg : 0 ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, F a :=
      mul_nonneg hmAinv_nn hFsum_nonneg
    have hsumsplit : ∑ a ∈ A, F a = (∑ a ∈ cc, F a) - ∑ a ∈ cc \ A, F a := by
      have h := Finset.sum_sdiff hA (f := F)
      linarith
    have hbadle : ∑ a ∈ cc \ A, F a ≤ ((cc \ A).card : ℝ) := by
      calc ∑ a ∈ cc \ A, F a ≤ ∑ a ∈ cc \ A, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro a ha
            exact hF1 a (Finset.mem_sdiff.mp ha).1
          _ = ((cc \ A).card : ℝ) := by simp
    have hηM : η * (cc.card : ℝ) ≤ ∑ a ∈ cc, F a := by
      rcases Nat.eq_zero_or_pos cc.card with h0 | hpos
      · have hcc : cc = ∅ := Finset.card_eq_zero.mp h0
        rw [hcc]; simp
      · have hMpos : 0 < (cc.card : ℝ) := by exact_mod_cast hpos
        have hMne : (cc.card : ℝ) ≠ 0 := ne_of_gt hMpos
        calc η * (cc.card : ℝ)
            ≤ ((cc.card : ℝ)⁻¹ * ∑ a ∈ cc, F a) * (cc.card : ℝ) :=
              mul_le_mul_of_nonneg_right hη hMpos.le
          _ = ∑ a ∈ cc, F a := by
              rw [mul_assoc, mul_comm (∑ a ∈ cc, F a) (cc.card : ℝ), ← mul_assoc,
                  inv_mul_cancel₀ hMne, one_mul]
    have hmain : (3 / 4) * η * (cc.card : ℝ) ≤ ∑ a ∈ A, F a := by
      linarith [hsumsplit, hbadle, hηM, hgood]
    have hMA : (A.card : ℝ) ≤ (cc.card : ℝ) := by exact_mod_cast Finset.card_le_card hA
    have hone_le : (1 : ℝ) ≤ (A.card : ℝ)⁻¹ * (cc.card : ℝ) := by
      have hkey : (A.card : ℝ) * ((A.card : ℝ)⁻¹ * (cc.card : ℝ)) = (cc.card : ℝ) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hmApos), one_mul]
      exact (mul_le_mul_iff_of_pos_left hmApos).mp (by rw [hkey, mul_one]; exact hMA)
    have havg_ge : 0 ≤ η → (3 / 4) * η ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, F a := by
      intro hηnn
      have h3nn : (0 : ℝ) ≤ (3 / 4) * η := mul_nonneg (by norm_num) hηnn
      have h1 : (A.card : ℝ)⁻¹ * ((3 / 4) * η * (cc.card : ℝ))
          ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, F a :=
        mul_le_mul_of_nonneg_left hmain hmAinv_nn
      have h3 : (3 / 4) * η * 1 ≤ (3 / 4) * η * ((A.card : ℝ)⁻¹ * (cc.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hone_le h3nn
      have h2 : (3 / 4) * η ≤ (A.card : ℝ)⁻¹ * ((3 / 4) * η * (cc.card : ℝ)) := by
        calc (3 / 4) * η = (3 / 4) * η * 1 := by ring
          _ ≤ (3 / 4) * η * ((A.card : ℝ)⁻¹ * (cc.card : ℝ)) := h3
          _ = (A.card : ℝ)⁻¹ * ((3 / 4) * η * (cc.card : ℝ)) := by ring
      linarith
    have hT_lower : (1 / C) * ((A.card : ℝ)⁻¹ * ∑ a ∈ A, F a) ≤ T := by
      rw [hT]
      have hle : (∑ a ∈ A, F a) / C ≤ ∑ a ∈ A, u a := by
        rw [Finset.sum_div]
        apply Finset.sum_le_sum
        intro a ha
        have h := hcoreU a ha
        rw [div_le_iff₀ hCpos]
        linarith
      calc (1 / C) * ((A.card : ℝ)⁻¹ * ∑ a ∈ A, F a)
          = (A.card : ℝ)⁻¹ * ((∑ a ∈ A, F a) / C) := by ring
        _ ≤ (A.card : ℝ)⁻¹ * ∑ a ∈ A, u a := mul_le_mul_of_nonneg_left hle hmAinv_nn
        _ = (A.card : ℝ)⁻¹ * (Pb.card : ℝ)⁻¹ * ∑ a ∈ A, ∑ b ∈ Pb, G a b := by
              simp only [hu]
              rw [← Finset.mul_sum]
              ring
    have hT_nonneg : 0 ≤ T := by
      have h1 : 0 ≤ (1 / C) * ((A.card : ℝ)⁻¹ * ∑ a ∈ A, F a) :=
        mul_nonneg hCinv_nn havg_nonneg
      linarith [hT_lower, h1]
    by_cases hηnp : η ≤ 0
    · have hL : η / 2 ^ (1 + 2 * Ncard) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hηnp (by positivity)
      linarith [hT_nonneg, hL]
    · have hηpos : 0 < η := lt_of_not_ge hηnp
      have hηnn : 0 ≤ η := le_of_lt hηpos
      have hAg := havg_ge hηnn
      have hT2 : (1 / C) * ((3 / 4) * η) ≤ T := by
        have h1 : (1 / C) * ((3 / 4) * η) ≤ (1 / C) * ((A.card : ℝ)⁻¹ * ∑ a ∈ A, F a) :=
          mul_le_mul_of_nonneg_left hAg hCinv_nn
        linarith [hT_lower, h1]
      have h4 : C ≤ (4 : ℝ) ^ Ncard := by
        have h4pos : (0 : ℝ) < (4 : ℝ) ^ Ncard := by positivity
        have h4' := mul_le_mul_of_nonneg_right hC h4pos.le
        rw [one_mul] at h4'
        have hsimp : (C * ((4 : ℝ) ^ Ncard)⁻¹) * (4 : ℝ) ^ Ncard = C := by
          rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt h4pos), mul_one]
        rwa [hsimp] at h4'
      have hpow4 : (4 : ℝ) ^ Ncard = 2 ^ (2 * Ncard) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      have hpow2 : (2 : ℝ) ^ (1 + 2 * Ncard) = 2 * 2 ^ (2 * Ncard) := by
        rw [pow_add]; norm_num
      have hCle : C ≤ (3 / 4) * 2 ^ (1 + 2 * Ncard) := by
        have h2n : (0 : ℝ) ≤ 2 ^ (2 * Ncard) := by positivity
        calc C ≤ (4 : ℝ) ^ Ncard := h4
          _ = 2 ^ (2 * Ncard) := hpow4
          _ ≤ (3 / 4) * 2 ^ (1 + 2 * Ncard) := by rw [hpow2]; nlinarith
      have hfinal : η / 2 ^ (1 + 2 * Ncard) ≤ (1 / C) * ((3 / 4) * η) := by
        have h2pos : (0 : ℝ) < 2 ^ (1 + 2 * Ncard) := by positivity
        rw [div_le_iff₀ h2pos]
        have hkey : η * C ≤ (3 / 4) * η * 2 ^ (1 + 2 * Ncard) := by
          have := mul_le_mul_of_nonneg_left hCle hηnn
          calc η * C ≤ η * ((3 / 4) * 2 ^ (1 + 2 * Ncard)) := this
            _ = (3 / 4) * η * 2 ^ (1 + 2 * Ncard) := by ring
        have hmm : (1 / C) * ((3 / 4) * η) * 2 ^ (1 + 2 * Ncard)
            = ((3 / 4) * η * 2 ^ (1 + 2 * Ncard)) / C := by ring
        rw [hmm, le_div_iff₀ hCpos]
        linarith
      linarith [hT2, hfinal]

end Work.Peluse.Prop36SW
