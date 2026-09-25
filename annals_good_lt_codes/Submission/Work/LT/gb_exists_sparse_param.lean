import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_card_weight
import Submission.Work.LT.gb_alpha_core
import Submission.Work.LT.gb_D0_large

namespace Work.LT

/-- For every `β > 0` there is `α > 0` (depending on `β`) such that for all sufficiently large `D` the number of vectors in `𝔽₂^D` of weight at most `α D` is at most `2^{β D}`.  This is the elementary entropy/Gilbert bound; a proof from `#{v : wt v ≤ αD} ≤ (αD+1) * (e/α)^{αD}` is fine. -/
theorem gb_exists_sparse_param (β : ℝ) (hβ : 0 < β) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
      ((Finset.univ.filter (fun v : Fin D → ZMod 2 => (hammingNorm v : ℝ) ≤ α * D)).card : ℝ) ≤
        (2 : ℝ) ^ (β * D) := by
  -- Choose `α ∈ (0, 1/2]` with `(2e/α)^α ≤ 2^{β/2}` (`α = 2^{-N}` for large `N`).
  obtain ⟨α, hαpos, hαhalf, hαcore⟩ := gb_alpha_core β hβ
  -- For large `D`, `α D + 1 ≤ 2^{β D / 2}`, `α D ≥ 2` and `D ≥ 1`.
  obtain ⟨D0, hD0⟩ := gb_D0_large (β / 2) α (by positivity) hαpos
  refine ⟨α, hαpos, by linarith, D0, fun D hD => ?_⟩
  obtain ⟨hpre, hαD, hD1⟩ := hD0 D hD
  -- `w = ⌊α D⌋` is the largest weight that can occur.
  have hαDpos : 0 < α * (D:ℝ) := by linarith
  have hαDnn : 0 ≤ α * (D:ℝ) := le_of_lt hαDpos
  set w : ℕ := ⌊α * (D:ℝ)⌋₊ with hwdef
  have hwle : (w:ℝ) ≤ α * (D:ℝ) := Nat.floor_le hαDnn
  have hwlt : α * (D:ℝ) < (w:ℝ) + 1 := Nat.lt_floor_add_one _
  have hwhalf : α * (D:ℝ) / 2 ≤ (w:ℝ) := by linarith
  have hw1 : 1 < w := by exact_mod_cast (by linarith : (1:ℝ) < (w:ℝ))
  have hwpos : 0 < w := by omega
  -- `2 w ≤ D`, so the binomial-coefficient bound applies.
  have hw2D : 2 * w ≤ D := by
    have h3 : 2 * α ≤ 1 := by linarith
    have hDnn : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
    have h1 : (2:ℝ) * w ≤ (D:ℝ) := by nlinarith [hwle, h3, hDnn]
    exact_mod_cast h1
  -- Rewrite the weight threshold `(q : ℝ) ≤ α D` as `q ≤ ⌊α D⌋`.
  have hfilt : (Finset.univ.filter (fun v : Fin D → ZMod 2 => (hammingNorm v : ℝ) ≤ α * (D:ℝ)))
      = Finset.univ.filter (fun v : Fin D → ZMod 2 => hammingNorm v ≤ w) := by
    apply Finset.filter_congr
    intro v _
    rw [hwdef]
    exact (Nat.le_floor_iff hαDnn).symm
  rw [hfilt]
  -- `#{v : wt v ≤ w} ≤ (w+1) (D e / w)^w`.
  have hw2D' : 2 * w ≤ Fintype.card (Fin D) := by simpa using hw2D
  have hcw := gb_card_weight (ι := Fin D) w hwpos hw2D'
  simp only [Fintype.card_fin] at hcw
  -- `2e/α ≥ 1` and `D e / w ≤ 2e/α`.
  have hx1 : 1 ≤ 2 * Real.exp 1 / α := by
    rw [le_div_iff₀ hαpos]
    have he : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith
  have hbase : (D:ℝ) * Real.exp 1 / w ≤ 2 * Real.exp 1 / α := by
    have hwDpos : (0:ℝ) < w := by exact_mod_cast hwpos
    rw [div_le_div_iff₀ hwDpos hαpos]
    have h' := mul_le_mul_of_nonneg_left hwhalf (by positivity : (0:ℝ) ≤ 2 * Real.exp 1)
    nlinarith [h']
  -- The chain of estimates.
  calc ((Finset.univ.filter (fun v : Fin D → ZMod 2 => hammingNorm v ≤ w)).card : ℝ)
      ≤ (w + 1) * ((D:ℝ) * Real.exp 1 / w) ^ w := hcw
    _ ≤ (α * (D:ℝ) + 1) * ((D:ℝ) * Real.exp 1 / w) ^ w := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ ≤ (α * (D:ℝ) + 1) * (2 * Real.exp 1 / α) ^ (α * (D:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ((D:ℝ) * Real.exp 1 / w) ^ w
            = ((D:ℝ) * Real.exp 1 / w) ^ (w:ℝ) := (Real.rpow_natCast _ w).symm
          _ ≤ (2 * Real.exp 1 / α) ^ (w:ℝ) :=
              Real.rpow_le_rpow (by positivity) hbase (Nat.cast_nonneg w)
          _ ≤ (2 * Real.exp 1 / α) ^ (α * (D:ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hx1 hwle
    _ ≤ (α * (D:ℝ) + 1) * (((2 * Real.exp 1 / α) ^ α) ^ D) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Real.rpow_mul (by positivity : (0:ℝ) ≤ 2 * Real.exp 1 / α) α (D:ℝ),
            Real.rpow_natCast]
    _ ≤ (α * (D:ℝ) + 1) * (((2:ℝ) ^ (β / 2)) ^ D) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hαcore D
    _ ≤ (α * (D:ℝ) + 1) * ((2:ℝ) ^ ((β / 2) * (D:ℝ))) := by
        rw [← Real.rpow_natCast ((2:ℝ) ^ (β / 2)) D,
            ← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num) (β/2) (D:ℝ)]
    _ ≤ (2:ℝ) ^ ((β / 2) * (D:ℝ)) * (2:ℝ) ^ ((β / 2) * (D:ℝ)) :=
        mul_le_mul_of_nonneg_right hpre (by positivity)
    _ = (2:ℝ) ^ (β * (D:ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring

end Work.LT
