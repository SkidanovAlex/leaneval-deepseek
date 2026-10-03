/-
# The period `perQ` of a pair of exact-height arithmetic frequencies

This module bounds the sum of the squares of the periods `perQ γ₁ γ₂ = lcm (addOrderOf γ₁)
(addOrderOf γ₂)` over the pairs of exact-height arithmetic frequencies at levels `l₁, l₂ ≤ L`.
Since every element of the IW denominator set `P_{≤l}` is at most `2^{C(l 2^{ρl/2} + l)}`
(`iwP_element_le_sharp`) and the levels are at most `L`, each `perQ` is at most
`2^{C·2^{ρL}}`, while the number of frequencies at level `l ≤ L` is at most `2^{2^{ρL}}`
(`iw_height_card_le`).  Hence the whole double sum is `≤ C·2^{K·2^{ρL}}`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallSymDefs
import Submission.Work.KMTPlan.A6.iwP_element_le_sharp

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

private theorem diffFreqs_subset (ρ : ℝ) (l : ℕ) : Work.KMTAreas.A7.diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
  intro γ hγ
  unfold Work.KMTAreas.A7.diffFreqs at hγ
  split_ifs at hγ with h
  · rw [h]; exact hγ
  · exact (Finset.mem_sdiff.mp hγ).1

/-- The number of exact-height frequencies at a level `l ≤ L` is at most `C·2^{2^{ρL}}`. -/
private theorem card_diffFreqs_le (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ l L : ℕ, l ≤ L →
      ((Work.KMTAreas.A7.diffFreqs ρ l).card : ℝ) ≤ C * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))) := by
  obtain ⟨C, hC, hCl⟩ := iw_height_card_le hρ
  refine ⟨C, hC, fun l L hl => ?_⟩
  have hcard : ((Work.KMTAreas.A7.diffFreqs ρ l).card : ℝ) ≤ ((iwArithFreqs ρ l).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (diffFreqs_subset ρ l)
  refine hcard.trans ((hCl l).trans ?_)
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC)
  have hexp : ρ * (l : ℝ) ≤ ρ * (L : ℝ) := by
    have h : (l : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl
    nlinarith [le_of_lt hρ]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- **The uniform bound on `perQ`.**  For a pair of exact-height arithmetic frequencies at levels
`l₁, l₂ ≤ L` the period `perQ γ₁ γ₂` is at most `2^{C·2^{ρL}}`. -/
theorem perQ_le_gain (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (l₁ l₂ L : ℕ) (γ₁ γ₂ : Analysis.IonescuWainger.Circle), l₁ ≤ L → l₂ ≤ L →
      γ₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₁ → γ₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂ →
      ((perQ γ₁ γ₂ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Cp * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
  obtain ⟨Kel, hKel, hKelb⟩ := iwP_element_le_sharp ρ hρ hρ1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hκ : 0 < ρ * Real.log 2 := by positivity
  refine ⟨2 * Kel * (1 + 4 / (ρ * Real.log 2)), by positivity, ?_⟩
  intro l₁ l₂ L γ₁ γ₂ h1 h2 hγ₁ hγ₂
  have hc : (0 : ℝ) ≤ 2 / (ρ * Real.log 2) := by positivity
  -- the level-wise growth of `1 + l·2^{ρl/2} + l`
  have key : ∀ l : ℕ, l ≤ L →
      (1 : ℝ) + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ)
        ≤ (1 + 4 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (L : ℝ)) := by
    intro l hl
    have hlL : (l : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl
    have hYL : (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ])
    have hY1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hY2pos : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hexp : (ρ * (l : ℝ) / 2) * Real.log 2 + 1 ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := by
      have h := Real.add_one_le_exp ((ρ * (l : ℝ) / 2) * Real.log 2)
      simpa [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm] using h
    have hl1 : (l : ℝ) ≤ (2 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := by
      have h : (ρ * (l : ℝ) / 2) * Real.log 2 ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := by linarith
      have hmul : (ρ * Real.log 2 / 2) * (l : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := by
        calc (ρ * Real.log 2 / 2) * (l : ℝ) = (ρ * (l : ℝ) / 2) * Real.log 2 := by ring
          _ ≤ _ := h
      calc (l : ℝ) = (2 / (ρ * Real.log 2)) * ((ρ * Real.log 2 / 2) * (l : ℝ)) := by
            rw [show (2 / (ρ * Real.log 2)) * ((ρ * Real.log 2 / 2) * (l : ℝ))
                = ((2 / (ρ * Real.log 2)) * (ρ * Real.log 2 / 2)) * (l : ℝ) from by ring,
              show (2 / (ρ * Real.log 2)) * (ρ * Real.log 2 / 2) = 1 from by
                field_simp,
              one_mul]
        _ ≤ (2 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hmul hc
    have hYl2 : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2)
        = (2 : ℝ) ^ (ρ * (l : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hB : (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) ≤ (2 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (L : ℝ)) := by
      have h1' := mul_le_mul_of_nonneg_right hl1 (le_of_lt hY2pos)
      have h2' : ((2 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2)) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2)
          = (2 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (l : ℝ)) := by
        rw [mul_assoc, hYl2]
      have h3' : (2 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (l : ℝ))
          ≤ (2 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hYL hc
      linarith
    have hcoef : (1 : ℝ) + 2 * (2 / (ρ * Real.log 2)) = 1 + 4 / (ρ * Real.log 2) := by
      field_simp
      ring
    have hmain : (1 : ℝ) + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ)
        ≤ (1 + 2 * (2 / (ρ * Real.log 2))) * (2 : ℝ) ^ (ρ * (L : ℝ)) := by
      nlinarith [hl1, hB, hY1]
    rwa [hcoef] at hmain
  -- the two level bounds
  obtain ⟨q₁, hq₁, hq₁γ⟩ := mem_iwArithFreqs.mp (diffFreqs_subset ρ l₁ hγ₁)
  obtain ⟨q₂, hq₂, hq₂γ⟩ := mem_iwArithFreqs.mp (diffFreqs_subset ρ l₂ hγ₂)
  have ho₁ : addOrderOf γ₁ ∣ q₁ := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hq₁γ
  have ho₂ : addOrderOf γ₂ ∣ q₂ := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hq₂γ
  have hq₁pos : 0 < q₁ := pos_of_mem_iwP hq₁
  have hq₂pos : 0 < q₂ := pos_of_mem_iwP hq₂
  have hle₁ : addOrderOf γ₁ ≤ q₁ := Nat.le_of_dvd hq₁pos ho₁
  have hle₂ : addOrderOf γ₂ ≤ q₂ := Nat.le_of_dvd hq₂pos ho₂
  have ho₁pos : 0 < addOrderOf γ₁ := Nat.pos_of_dvd_of_pos ho₁ hq₁pos
  have ho₂pos : 0 < addOrderOf γ₂ := Nat.pos_of_dvd_of_pos ho₂ hq₂pos
  have hper : perQ γ₁ γ₂ ≤ addOrderOf γ₁ * addOrderOf γ₂ :=
    Nat.le_of_dvd (Nat.mul_pos ho₁pos ho₂pos)
      (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))
  have hq₁b : (q₁ : ℝ) ≤ (2 : ℝ) ^ (Kel * (1 + (l₁ : ℝ) * (2 : ℝ) ^ (ρ * (l₁ : ℝ) / 2) + (l₁ : ℝ))) :=
    hKelb l₁ q₁ hq₁
  have hq₂b : (q₂ : ℝ) ≤ (2 : ℝ) ^ (Kel * (1 + (l₂ : ℝ) * (2 : ℝ) ^ (ρ * (l₂ : ℝ) / 2) + (l₂ : ℝ))) :=
    hKelb l₂ q₂ hq₂
  have hkey₁ := key l₁ h1
  have hkey₂ := key l₂ h2
  have hfin : (q₁ : ℝ) * (q₂ : ℝ)
      ≤ (2 : ℝ) ^ (Kel * ((1 + 4 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (L : ℝ))))
        * (2 : ℝ) ^ (Kel * ((1 + 4 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (L : ℝ)))) := by
    refine mul_le_mul (hq₁b.trans ?_) (hq₂b.trans ?_) (by positivity) (by positivity)
    · refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      nlinarith [hKel, hkey₁]
    · refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      nlinarith [hKel, hkey₂]
  have hcomb : (2 : ℝ) ^ (Kel * ((1 + 4 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (L : ℝ))))
        * (2 : ℝ) ^ (Kel * ((1 + 4 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (L : ℝ))))
      = (2 : ℝ) ^ (2 * Kel * (1 + 4 / (ρ * Real.log 2)) * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hperR : ((perQ γ₁ γ₂ : ℕ) : ℝ) ≤ (q₁ : ℝ) * (q₂ : ℝ) := by
    have h1' : ((perQ γ₁ γ₂ : ℕ) : ℝ) ≤ ((addOrderOf γ₁ * addOrderOf γ₂ : ℕ) : ℝ) := by
      exact_mod_cast hper
    have h2' : ((addOrderOf γ₁ * addOrderOf γ₂ : ℕ) : ℝ)
        ≤ ((q₁ * q₂ : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul hle₁ hle₂
    calc ((perQ γ₁ γ₂ : ℕ) : ℝ) ≤ ((addOrderOf γ₁ * addOrderOf γ₂ : ℕ) : ℝ) := h1'
      _ ≤ ((q₁ * q₂ : ℕ) : ℝ) := h2'
      _ = (q₁ : ℝ) * (q₂ : ℝ) := by push_cast; ring
  exact hperR.trans (hfin.trans (le_of_eq hcomb))

/-- **The sum of the squared periods.**  The sum of `perQ γ₁ γ₂²` over the pairs of exact-height
arithmetic frequencies at levels `l₁, l₂ ≤ L` is at most `C·2^{K·2^{ρL}}`. -/
theorem perQ_sum_bound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ (l₁ l₂ L : ℕ), l₁ ≤ L → l₂ ≤ L →
      (∑ γ₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, ∑ γ₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
          ((perQ γ₁ γ₂ : ℕ) : ℝ) ^ 2)
        ≤ C * (2 : ℝ) ^ (K * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
  obtain ⟨Ccd, hCcd, hcd⟩ := card_diffFreqs_le ρ hρ
  obtain ⟨Cp, hCp, hple⟩ := perQ_le_gain ρ hρ hρ1
  refine ⟨Ccd ^ 2 * (2 : ℝ) ^ (2 * Cp), 2 + 2 * Cp, ?_, ?_, ?_⟩
  · positivity
  · positivity
  intro l₁ l₂ L h1 h2
  have hG0 : (0 : ℝ) < (2 : ℝ) ^ (Cp * (2 : ℝ) ^ (ρ * (L : ℝ))) := by positivity
  have hstep1 : (∑ γ₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, ∑ γ₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
          ((perQ γ₁ γ₂ : ℕ) : ℝ) ^ 2)
      ≤ (∑ _γ₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
          ∑ _γ₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
            ((2 : ℝ) ^ (Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))) ^ 2) := by
    refine Finset.sum_le_sum (fun γ₁ hγ₁ => Finset.sum_le_sum (fun γ₂ hγ₂ => ?_))
    have h := hple l₁ l₂ L γ₁ γ₂ h1 h2 hγ₁ hγ₂
    have h0 : (0 : ℝ) ≤ ((perQ γ₁ γ₂ : ℕ) : ℝ) := by positivity
    nlinarith [h, h0, hG0]
  have hstep2 : (∑ _γ₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₁,
          ∑ _γ₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
            ((2 : ℝ) ^ (Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))) ^ 2)
      = ((Work.KMTAreas.A7.diffFreqs ρ l₁).card : ℝ)
        * ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ)
        * ((2 : ℝ) ^ (Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))) ^ 2 := by
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  refine hstep1.trans ?_
  rw [hstep2]
  have hmul : ((Work.KMTAreas.A7.diffFreqs ρ l₁).card : ℝ)
        * ((Work.KMTAreas.A7.diffFreqs ρ l₂).card : ℝ)
        * ((2 : ℝ) ^ (Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))) ^ 2
      ≤ (Ccd * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))))
        * (Ccd * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))))
        * ((2 : ℝ) ^ (Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))) ^ 2 := by
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul (hcd l₁ L h1) (hcd l₂ L h2) (by positivity) (by positivity)) (by positivity)
  refine hmul.trans ?_
  have hG2 : ((2 : ℝ) ^ (Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))) ^ 2
      = (2 : ℝ) ^ (2 * Cp * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
    rw [show ((2 : ℝ) ^ (Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))) ^ 2
        = ((2 : ℝ) ^ (Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))) ^ ((2 : ℕ) : ℝ) from
      (Real.rpow_natCast _ 2).symm]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hBsq : (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))) * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ)))
      = (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hG2]
  have hsplit : Ccd * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ)))
        * (Ccd * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))))
        * (2 : ℝ) ^ (2 * Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))
      = Ccd ^ 2 * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ))
          + 2 * Cp * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
    rw [show Ccd * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ)))
          * (Ccd * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))))
          * (2 : ℝ) ^ (2 * Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))
        = Ccd ^ 2 * (((2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ)))
            * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (L : ℝ))))
          * (2 : ℝ) ^ (2 * Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))) from by ring,
      hBsq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [hsplit]
  have h2Cp : (0 : ℝ) ≤ 2 * Cp := by positivity
  have hB0 : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by positivity
  have hexp : 2 * (2 : ℝ) ^ (ρ * (L : ℝ)) + 2 * Cp * (2 : ℝ) ^ (ρ * (L : ℝ))
      ≤ (2 + 2 * Cp) * (2 : ℝ) ^ (ρ * (L : ℝ)) + 2 * Cp := by
    nlinarith [h2Cp, hB0]
  calc Ccd ^ 2 * (2 : ℝ) ^ (2 * (2 : ℝ) ^ (ρ * (L : ℝ)) + 2 * Cp * (2 : ℝ) ^ (ρ * (L : ℝ)))
      ≤ Ccd ^ 2 * (2 : ℝ) ^ ((2 + 2 * Cp) * (2 : ℝ) ^ (ρ * (L : ℝ)) + 2 * Cp) := by
        refine mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity)
    _ = Ccd ^ 2 * (2 : ℝ) ^ (2 * Cp) * (2 : ℝ) ^ ((2 + 2 * Cp) * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        ring

end

end Work.KMTPlan.A6
