import Mathlib
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.summable_int_inv_one_add_abs_pow

namespace Work.GM.Affine

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

/-- **Elementary lattice inequality.**  For every real `u` and every integer `ℓ`,
`1 + |⌊u⌋ - ℓ| ≤ 2 (1 + |u - ℓ|)`. -/
lemma one_add_abs_floor_sub_le (u : ℝ) (ℓ : ℤ) :
    1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)| ≤ 2 * (1 + |u - (ℓ : ℝ)|) := by
  have hmu : |((⌊u⌋ : ℤ) : ℝ) - u| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor
    · have := Int.floor_le u; linarith
    · have := (Int.lt_floor_add_one u).le; linarith
  have htri := abs_sub_le (((⌊u⌋ : ℤ) : ℝ)) u ((ℓ : ℝ))
  have hnn : (0 : ℝ) ≤ |u - (ℓ : ℝ)| := abs_nonneg _
  linarith

/-- **Lattice comparison.**  For all `u, ℓ`,
`1/(1+|u-ℓ|)^4 ≤ 16 · 1/(1+|⌊u⌋-ℓ|)^4`. -/
lemma inv_pow_four_le_shift (u : ℝ) (ℓ : ℤ) :
    (1 : ℝ) / (1 + |u - (ℓ : ℝ)|) ^ 4
      ≤ 16 * (1 / (1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) ^ 4) := by
  have hkey := one_add_abs_floor_sub_le u ℓ
  have h4 : ((1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) / 2) ^ 4
      ≤ (1 + |u - (ℓ : ℝ)|) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hpos : 0 < ((1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) / 2) ^ 4 := by positivity
  have hone : (1 : ℝ) / (1 + |u - (ℓ : ℝ)|) ^ 4
      ≤ 1 / ((1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) / 2) ^ 4 :=
    one_div_le_one_div_of_le hpos h4
  have h16 : 1 / ((1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) / 2) ^ 4
      = 16 * (1 / (1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) ^ 4) := by
    rw [div_pow, one_div_div]; ring
  linarith [hone, h16.le, h16.ge]

/-- **The decay bound, squared and compared with the floor-centred lattice.** -/
lemma normSq_psi1hat_le {K C M₃ u : ℝ}
    (hdec : ∀ y : ℝ, ‖psi1hat K y‖ ≤ C / (1 + |y|) ^ 2) (hM₃ : 1 ≤ M₃) (ℓ : ℤ) :
    ‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2
      ≤ 16 * C ^ 2 * (1 / (1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) ^ 4) := by
  have hM₃nn : 0 ≤ M₃ := le_trans zero_le_one hM₃
  set y : ℝ := M₃ * (u - (ℓ : ℝ)) with hy
  have hsq : ‖psi1hat K y‖ ^ 2 ≤ C ^ 2 / (1 + |y|) ^ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (hdec y) 2
    have heq : (C / (1 + |y|) ^ 2) ^ 2 = C ^ 2 / (1 + |y|) ^ 4 := by
      rw [div_pow, ← pow_mul, show (2 : ℕ) * 2 = 4 from rfl]
    rwa [heq] at h
  have habs : |u - (ℓ : ℝ)| ≤ |y| := by
    rw [hy, abs_mul, abs_of_nonneg hM₃nn]
    nlinarith [abs_nonneg (u - (ℓ : ℝ))]
  have hstep : C ^ 2 / (1 + |y|) ^ 4 ≤ C ^ 2 / (1 + |u - (ℓ : ℝ)|) ^ 4 := by
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hstep2 := inv_pow_four_le_shift u ℓ
  have hfin : C ^ 2 / (1 + |u - (ℓ : ℝ)|) ^ 4
      ≤ 16 * C ^ 2 * (1 / (1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) ^ 4) := by
    rw [show C ^ 2 / (1 + |u - (ℓ : ℝ)|) ^ 4
          = C ^ 2 * ((1 : ℝ) / (1 + |u - (ℓ : ℝ)|) ^ 4) by ring,
        show 16 * C ^ 2 * (1 / (1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) ^ 4)
          = C ^ 2 * (16 * (1 / (1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) ^ 4)) by ring]
    exact mul_le_mul_of_nonneg_left hstep2 (sq_nonneg C)
  linarith [hsq, hstep, hfin]

/-- **The pointwise `ℝ≥0∞` bound** for the terms of the far lattice weight. -/
lemma far_weight_term_le {K C M₃ u : ℝ}
    (hdec : ∀ y : ℝ, ‖psi1hat K y‖ ≤ C / (1 + |y|) ^ 2) (hM₃ : 1 ≤ M₃) (ℓ : ℤ) :
    (if 2 / M₃ < |u - (ℓ : ℝ)| then
        ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0)
      ≤ ENNReal.ofReal
          (16 * C ^ 2 * (1 / (1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) ^ 4)) := by
  by_cases h : 2 / M₃ < |u - (ℓ : ℝ)|
  · rw [if_pos h]
    exact ENNReal.ofReal_le_ofReal (normSq_psi1hat_le hdec hM₃ ℓ)
  · rw [if_neg h]
    exact bot_le

/-- **Uniform bound on the far lattice weight.**

For `K > 0` there is `Cw > 0` such that for every `M₃ ≥ 1` and every `u : ℝ`,
`Σ'_ℓ [2/M₃ < |u - ℓ|] · ‖ψ̂₁(M₃(u-ℓ))‖² ≤ Cw` (as an `ℝ≥0∞`-valued sum, so no summability
is needed to state it).

Route: `psi1hat_decay K hK 2` gives `‖ψ̂₁ y‖² ≤ C² (1+|y|)^{-4}`.  With `m := ⌊u⌋` one has
`1 + |m - ℓ| ≤ 4(1 + |u - ℓ|)`, and `1 + |u-ℓ| ≤ 1 + M₃|u-ℓ|` since `M₃ ≥ 1`, so the sum is at
most `256 C² Σ'_ℓ (1+|m-ℓ|)^{-4} ≤ 256 C² Σ'_k (1+|k|)^{-4}`
(`ENNReal.tsum_comp_le_tsum_of_injective` with `ℓ ↦ m - ℓ`, which is injective), and the last
sum is finite and positive because `∑_{k:ℤ} (1+|k|)^{-4}` is summable
(`Summable.of_nat_of_neg` from the `ℕ`-case, e.g. `Real.summable_one_div_nat_rpow`). -/
theorem far_weight_uniform_bound {K : ℝ} (hK : 0 < K) :
    ∃ Cw : ℝ, 0 < Cw ∧ ∀ M₃ : ℝ, 1 ≤ M₃ → ∀ u : ℝ,
      (∑' ℓ : ℤ, (if 2 / M₃ < |u - (ℓ : ℝ)| then
        ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0))
        ≤ ENNReal.ofReal Cw := by
  obtain ⟨C, hCpos, hdec⟩ := psi1hat_decay K hK 2
  set S : ℝ := ∑' k : ℤ, (1 : ℝ) / (1 + |((k : ℤ) : ℝ)|) ^ 4 with hSdef
  have hSsum : Summable (fun k : ℤ => (1 : ℝ) / (1 + |((k : ℤ) : ℝ)|) ^ 4) :=
    summable_int_inv_one_add_abs_pow 4 (by norm_num)
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact tsum_nonneg (fun k => by positivity)
  refine ⟨16 * C ^ 2 * S + 1, by nlinarith [hCpos, hSnn, sq_nonneg C], fun M₃ hM₃ u => ?_⟩
  have hstep1 : (∑' ℓ : ℤ, (if 2 / M₃ < |u - (ℓ : ℝ)| then
        ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0))
      ≤ ∑' ℓ : ℤ, ENNReal.ofReal
          (16 * C ^ 2 * (1 / (1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) ^ 4)) :=
    ENNReal.tsum_le_tsum (fun ℓ => far_weight_term_le hdec hM₃ ℓ)
  have hinj : Function.Injective (fun ℓ : ℤ => ⌊u⌋ - ℓ) :=
    fun a b hab => sub_right_inj.mp hab
  have hcomp : (∑' ℓ : ℤ, ENNReal.ofReal
        (16 * C ^ 2 * (1 / (1 + |((⌊u⌋ - ℓ : ℤ) : ℝ)|) ^ 4)))
      ≤ ∑' k : ℤ, ENNReal.ofReal
        (16 * C ^ 2 * (1 / (1 + |((k : ℤ) : ℝ)|) ^ 4)) :=
    ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun k : ℤ => ENNReal.ofReal (16 * C ^ 2 * (1 / (1 + |((k : ℤ) : ℝ)|) ^ 4)))
  have hcomp' : (∑' ℓ : ℤ, ENNReal.ofReal
        (16 * C ^ 2 * (1 / (1 + |((⌊u⌋ : ℤ) : ℝ) - (ℓ : ℝ)|) ^ 4)))
      ≤ ∑' k : ℤ, ENNReal.ofReal
        (16 * C ^ 2 * (1 / (1 + |((k : ℤ) : ℝ)|) ^ 4)) := by
    simpa only [Int.cast_sub] using hcomp
  have hvalue : (∑' k : ℤ, ENNReal.ofReal
        (16 * C ^ 2 * (1 / (1 + |((k : ℤ) : ℝ)|) ^ 4)))
      = ENNReal.ofReal (16 * C ^ 2) * ENNReal.ofReal S := by
    have h1 : ∀ k : ℤ, ENNReal.ofReal (16 * C ^ 2 * (1 / (1 + |((k : ℤ) : ℝ)|) ^ 4))
        = ENNReal.ofReal (16 * C ^ 2)
          * ENNReal.ofReal (1 / (1 + |((k : ℤ) : ℝ)|) ^ 4) :=
      fun k => ENNReal.ofReal_mul (by positivity)
    rw [tsum_congr h1, ENNReal.tsum_mul_left]
    congr 1
    rw [hSdef, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hSsum]
  have hfin : ENNReal.ofReal (16 * C ^ 2) * ENNReal.ofReal S
      ≤ ENNReal.ofReal (16 * C ^ 2 * S + 1) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 16 * C ^ 2)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc (∑' ℓ : ℤ, (if 2 / M₃ < |u - (ℓ : ℝ)| then
        ENNReal.ofReal (‖psi1hat K (M₃ * (u - (ℓ : ℝ)))‖ ^ 2) else 0))
      ≤ _ := hstep1
    _ ≤ _ := hcomp'
    _ = ENNReal.ofReal (16 * C ^ 2) * ENNReal.ofReal S := hvalue
    _ ≤ ENNReal.ofReal (16 * C ^ 2 * S + 1) := hfin

end

end Work.GM.Affine
