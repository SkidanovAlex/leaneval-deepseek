import Mathlib
import Submission.Work.KMTAreas.A4.existsMulPowGeNatAddOne
import Submission.Work.KMTAreas.A4.addRpowLeTwoRpowMul

namespace Work.KMTAreas.A4

/-- The real-power identity `(2 ^ ρ) ^ l = 2 ^ (ρ * l)` for a natural exponent. -/
lemma two_rpow_pow_eq (ρ : ℝ) (l : ℕ) : ((2:ℝ)^ρ)^l = (2:ℝ)^(ρ*(l:ℝ)) := by
  rw [← Real.rpow_natCast ((2:ℝ)^ρ) l, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]

/--
Core arithmetic bound: if `(l + 1) ≤ M * 2 ^ (ρ * l)` for all `l` (which holds for a suitable
`M > 0` when `ρ > 0`), then the quantity `2 ^ (-(c*l)) * ((l+1) + Cρ * 2 ^ (ρ*(l+1))) ^ (c/ρ)`
is bounded uniformly in `l` by `2 ^ (c/ρ) * (M ^ (c/ρ) + Cρ ^ (c/ρ) * 2 ^ c)`.

The estimate uses `(a + b) ^ s ≤ 2 ^ s * (a ^ s + b ^ s)` (for `a, b ≥ 0`, `s ≥ 0`) to split the
base `(l+1) + Cρ * 2 ^ (ρ*(l+1))` into its two summands, and then the two identities
`(M * 2 ^ (ρ*l)) ^ (c/ρ) = M ^ (c/ρ) * 2 ^ (c*l)` and
`2 ^ (ρ*(l+1) * (c/ρ)) = 2 ^ (c*(l+1)) = 2 ^ (c*l) * 2 ^ c`. -/
lemma goodArcIndexDecay_core {c ρ Cρ M : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hCρ : 0 < Cρ)
    (hMpos : 0 < M) (hM : ∀ l : ℕ, (l:ℝ)+1 ≤ M * (2:ℝ)^(ρ*(l:ℝ))) :
    ∀ l : ℕ, (2:ℝ)^(-(c*(l:ℝ))) * (((l:ℝ)+1) + Cρ*(2:ℝ)^(ρ*((l:ℝ)+1)))^(c/ρ)
      ≤ (2:ℝ)^(c/ρ) * (M^(c/ρ) + Cρ^(c/ρ)*(2:ℝ)^c) := by
  intro l
  have he : 0 < c/ρ := div_pos hc hρ
  set A : ℝ := (l:ℝ)+1 with hA
  set B : ℝ := Cρ*(2:ℝ)^(ρ*((l:ℝ)+1)) with hB
  have hAnonneg : 0 ≤ A := by rw [hA]; positivity
  have hBnonneg : 0 ≤ B := by rw [hB]; positivity
  have h2pos : 0 < (2:ℝ)^(-(c*(l:ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  have h2c : (2:ℝ)^(-(c*(l:ℝ))) * (2:ℝ)^(c*(l:ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    have : -(c*(l:ℝ)) + c*(l:ℝ) = 0 := by ring
    rw [this, Real.rpow_zero]
  have hsplit : (A+B)^(c/ρ) ≤ (2:ℝ)^(c/ρ) * (A^(c/ρ) + B^(c/ρ)) :=
    addRpowLeTwoRpowMul hAnonneg hBnonneg (le_of_lt he)
  have hA2 : (2:ℝ)^(-(c*(l:ℝ))) * A^(c/ρ) ≤ M^(c/ρ) := by
    have hAl : A ≤ M * (2:ℝ)^(ρ*(l:ℝ)) := by rw [hA]; exact hM l
    have h1 : A^(c/ρ) ≤ (M * (2:ℝ)^(ρ*(l:ℝ)))^(c/ρ) :=
      Real.rpow_le_rpow hAnonneg hAl (le_of_lt he)
    have h2 : (M * (2:ℝ)^(ρ*(l:ℝ)))^(c/ρ) = M^(c/ρ) * (2:ℝ)^(c*(l:ℝ)) := by
      rw [Real.mul_rpow (le_of_lt hMpos) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _),
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      field_simp
    have h3 : (2:ℝ)^(-(c*(l:ℝ))) * (M^(c/ρ) * (2:ℝ)^(c*(l:ℝ))) = M^(c/ρ) := by
      rw [show (2:ℝ)^(-(c*(l:ℝ))) * (M^(c/ρ) * (2:ℝ)^(c*(l:ℝ)))
            = M^(c/ρ) * ((2:ℝ)^(-(c*(l:ℝ))) * (2:ℝ)^(c*(l:ℝ))) by ring, h2c, mul_one]
    exact (mul_le_mul_of_nonneg_left (h1.trans (le_of_eq h2)) (le_of_lt h2pos)).trans (le_of_eq h3)
  have hB2 : (2:ℝ)^(-(c*(l:ℝ))) * B^(c/ρ) ≤ Cρ^(c/ρ) * (2:ℝ)^c := by
    have hBexp : B^(c/ρ) = Cρ^(c/ρ) * ((2:ℝ)^(c*(l:ℝ)) * (2:ℝ)^c) := by
      rw [hB, Real.mul_rpow (le_of_lt hCρ) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _),
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [show (ρ*((l:ℝ)+1))*(c/ρ) = c*(l:ℝ) + c by field_simp,
          Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    have h3 : (2:ℝ)^(-(c*(l:ℝ))) * (Cρ^(c/ρ) * ((2:ℝ)^(c*(l:ℝ)) * (2:ℝ)^c))
        = Cρ^(c/ρ) * (2:ℝ)^c := by
      rw [show (2:ℝ)^(-(c*(l:ℝ))) * (Cρ^(c/ρ) * ((2:ℝ)^(c*(l:ℝ)) * (2:ℝ)^c))
            = Cρ^(c/ρ) * ((2:ℝ)^c * ((2:ℝ)^(-(c*(l:ℝ))) * (2:ℝ)^(c*(l:ℝ)))) by ring,
          h2c, mul_one]
    rw [hBexp]
    exact le_of_eq h3
  have hfinal : (2:ℝ)^(-(c*(l:ℝ))) * (A+B)^(c/ρ)
      ≤ (2:ℝ)^(c/ρ) * (M^(c/ρ) + Cρ^(c/ρ)*(2:ℝ)^c) := by
    have h4 : (2:ℝ)^(-(c*(l:ℝ))) * (A+B)^(c/ρ)
        ≤ (2:ℝ)^(-(c*(l:ℝ))) * ((2:ℝ)^(c/ρ) * (A^(c/ρ)+B^(c/ρ))) :=
      mul_le_mul_of_nonneg_left hsplit (le_of_lt h2pos)
    have h5 : (2:ℝ)^(-(c*(l:ℝ))) * ((2:ℝ)^(c/ρ) * (A^(c/ρ)+B^(c/ρ)))
        = (2:ℝ)^(c/ρ) * ((2:ℝ)^(-(c*(l:ℝ)))*A^(c/ρ) + (2:ℝ)^(-(c*(l:ℝ)))*B^(c/ρ)) := by ring
    have h6 : (2:ℝ)^(c/ρ) * ((2:ℝ)^(-(c*(l:ℝ)))*A^(c/ρ) + (2:ℝ)^(-(c*(l:ℝ)))*B^(c/ρ))
        ≤ (2:ℝ)^(c/ρ) * (M^(c/ρ) + Cρ^(c/ρ)*(2:ℝ)^c) :=
      mul_le_mul_of_nonneg_left (add_le_add hA2 hB2) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
    exact (h4.trans (le_of_eq h5)).trans h6
  exact hfinal

/--
Decay of the "good arc index" weight: if `x ≥ 1` lies below the threshold
`(l+1) + Cρ * 2 ^ (ρ * (l+1))` attached to the index `l`, then the weight `2 ^ (-(c*l))` is
dominated by `K * x ^ (-(c/ρ))`, uniformly in `x` and `l`.
-/
theorem goodArcIndexDecay {c ρ Cρ Cg : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hCρ : 0 < Cρ) (hCg : 0 < Cg) :
    ∃ K : NNReal, 0 < K ∧ ∀ (x : ℝ) (l : ℕ), 1 ≤ x →
      x < ((l : ℝ) + 1) + Cρ * (2 : ℝ) ^ (ρ * ((l : ℝ) + 1)) →
      Cg * (2 : ℝ) ^ (-(c * (l : ℝ))) ≤ Cg * (K : ℝ) * x ^ (-(c / ρ)) := by
  have h2ρ : (1:ℝ) < (2:ℝ)^ρ := Real.one_lt_rpow (by norm_num) hρ
  obtain ⟨M, hMpos, hM0⟩ := existsMulPowGeNatAddOne h2ρ
  have hM : ∀ l : ℕ, (l:ℝ)+1 ≤ M * (2:ℝ)^(ρ*(l:ℝ)) := by
    intro l
    have h := hM0 l
    rw [two_rpow_pow_eq ρ l] at h
    exact h
  set Kreal : ℝ := (2:ℝ)^(c/ρ) * (M^(c/ρ) + Cρ^(c/ρ)*(2:ℝ)^c) with hKreal
  have hKpos : 0 < Kreal := by
    rw [hKreal]
    have h1 : 0 < (2:ℝ)^(c/ρ) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : 0 < M^(c/ρ) := Real.rpow_pos_of_pos hMpos _
    have h3 : 0 < Cρ^(c/ρ) := Real.rpow_pos_of_pos hCρ _
    have h4 : 0 < (2:ℝ)^c := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine ⟨⟨Kreal, le_of_lt hKpos⟩, ?_, ?_⟩
  · exact_mod_cast hKpos
  · intro x l hx hxl
    change Cg * (2:ℝ)^(-(c*(l:ℝ))) ≤ Cg * Kreal * x^(-(c/ρ))
    have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
    have hxnonneg : 0 ≤ x := le_of_lt hxpos
    have he : 0 < c/ρ := div_pos hc hρ
    have hxe : x^(c/ρ) < (((l:ℝ)+1) + Cρ*(2:ℝ)^(ρ*((l:ℝ)+1)))^(c/ρ) :=
      Real.rpow_lt_rpow hxnonneg hxl he
    have hmul : (2:ℝ)^(-(c*(l:ℝ))) * x^(c/ρ)
        < (2:ℝ)^(-(c*(l:ℝ))) * (((l:ℝ)+1) + Cρ*(2:ℝ)^(ρ*((l:ℝ)+1)))^(c/ρ) :=
      mul_lt_mul_of_pos_left hxe (Real.rpow_pos_of_pos (by norm_num) _)
    have hcore := goodArcIndexDecay_core hc hρ hCρ hMpos hM l
    have hKbound : (2:ℝ)^(-(c*(l:ℝ))) * x^(c/ρ) ≤ Kreal := by
      rw [hKreal]
      exact (le_of_lt hmul).trans hcore
    have hxe_inv : x^(c/ρ) * x^(-(c/ρ)) = 1 := by
      rw [← Real.rpow_add hxpos, add_neg_cancel, Real.rpow_zero]
    have hstep : (2:ℝ)^(-(c*(l:ℝ))) ≤ Kreal * x^(-(c/ρ)) := by
      have h1 : (2:ℝ)^(-(c*(l:ℝ))) = (2:ℝ)^(-(c*(l:ℝ))) * (x^(c/ρ) * x^(-(c/ρ))) := by
        rw [hxe_inv, mul_one]
      have h2 : (2:ℝ)^(-(c*(l:ℝ))) * (x^(c/ρ) * x^(-(c/ρ)))
          = ((2:ℝ)^(-(c*(l:ℝ))) * x^(c/ρ)) * x^(-(c/ρ)) := by ring
      exact h1.le.trans (h2.le.trans (mul_le_mul_of_nonneg_right hKbound (Real.rpow_nonneg hxnonneg _)))
    have h3 : Cg * (2:ℝ)^(-(c*(l:ℝ))) ≤ Cg * (Kreal * x^(-(c/ρ))) :=
      mul_le_mul_of_nonneg_left hstep (le_of_lt hCg)
    have h4 : Cg * (Kreal * x^(-(c/ρ))) = Cg * Kreal * x^(-(c/ρ)) := by ring
    exact h3.trans (le_of_eq h4)

end Work.KMTAreas.A4
