import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_count_weight_vec
import Submission.Work.LT.gb_small_gamma
import Submission.Work.LT.gb_real_core

namespace Work.LT

/-- For every `c > 0` there is `γ > 0` such that for all sufficiently large `D` the number of `D × D` matrices over `𝔽₂` of Hamming weight at most `γ D²` is at most `2^{c D²}`.  Again an elementary counting bound suffices (take `γ` enormously small compared with `c` so that `γ log₂(e/γ) < c`). -/
theorem gb_exists_weight_param (c : ℝ) (hc : 0 < c) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ D0 : ℕ, ∀ D : ℕ, D0 ≤ D →
      ((Finset.univ.filter
          (fun x : Fin D × Fin D → ZMod 2 => (hammingNorm x : ℝ) ≤ γ * D ^ 2)).card : ℝ) ≤
        (2 : ℝ) ^ (c * D ^ 2) := by
  -- Choose `γ` small enough that `(2e/γ)^γ ≤ 2^{c/2}` and `γ ≤ 2^{c/2} - 1`.
  obtain ⟨γ, hγpos, hγ4, hγδ, hbase⟩ := gb_small_gamma c hc
  -- Choose `D0` so that `γ * D² ≥ 2` for all `D ≥ D0`.
  obtain ⟨D0, hD0⟩ := exists_nat_ge (max (2 / γ) 1)
  have hD0pos : (1:ℝ) ≤ (D0:ℝ) := le_trans (le_max_right _ _) hD0
  have hD0g : 2 / γ ≤ (D0:ℝ) := le_trans (le_max_left _ _) hD0
  refine ⟨γ, hγpos, D0, ?_⟩
  intro D hD
  have hDD : (D0:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hD1 : (1:ℝ) ≤ (D:ℝ) := le_trans hD0pos hDD
  have hDg : 2 / γ ≤ (D:ℝ) := le_trans hD0g hDD
  have hDsq : 2 / γ ≤ (D:ℝ)^2 := by nlinarith [hD1, hDg]
  have hbig : 2 ≤ γ * (D:ℝ)^2 := by
    rw [div_le_iff₀ hγpos] at hDsq
    linarith [hDsq]
  -- `W` is the natural number of ones allowed.
  let W : ℕ := ⌊γ * (D:ℝ)^2⌋₊
  have hgr : 0 ≤ γ * (D:ℝ)^2 := by positivity
  have hWle : (W:ℝ) ≤ γ * (D:ℝ)^2 := Nat.floor_le hgr
  have hWgt : γ * (D:ℝ)^2 < (W:ℝ) + 1 := Nat.lt_floor_add_one _
  have hWge : γ * (D:ℝ)^2 / 2 ≤ (W:ℝ) := by linarith
  have hWpos : 0 < W := by
    have h1 : (1:ℝ) < (W:ℝ) := by linarith
    have h2 : 1 < W := by exact_mod_cast h1
    omega
  have hWposR : (0:ℝ) < (W:ℝ) := by exact_mod_cast hWpos
  -- The counting lemma applies since `2W ≤ D²`.
  have hWhalf : 2 * W ≤ Fintype.card (Fin D × Fin D) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    have h3 : ((D*D : ℕ) : ℝ) = (D:ℝ)^2 := by push_cast; ring
    have h1 : (2*W : ℝ) ≤ 2 * (γ * (D:ℝ)^2) := by linarith [hWle]
    have h2 : 2 * (γ * (D:ℝ)^2) ≤ ((D*D:ℕ):ℝ) := by rw [h3]; nlinarith [hγ4, sq_nonneg (D:ℝ)]
    have : (2*W : ℝ) ≤ ((D*D:ℕ):ℝ) := by linarith
    exact_mod_cast this
  -- Rewrite the weight condition using the floor.
  have hfilt : (Finset.univ.filter (fun x : Fin D × Fin D → ZMod 2 =>
        (hammingNorm x : ℝ) ≤ γ * (D:ℝ)^2))
      = (Finset.univ.filter (fun x : Fin D × Fin D → ZMod 2 => hammingNorm x ≤ W)) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · intro hx
      have h1 : hammingNorm x ≤ W := Nat.le_floor hx
      exact_mod_cast h1
    · intro hx
      have h1 : (hammingNorm x : ℝ) ≤ (W:ℝ) := by exact_mod_cast hx
      have h2 : (W:ℝ) ≤ γ * (D:ℝ)^2 := Nat.floor_le hgr
      linarith
  have hcount := gb_count_weight_vec (ι := Fin D × Fin D) W hWpos hWhalf
  rw [Fintype.card_prod, Fintype.card_fin] at hcount
  have hcast : ((D*D : ℕ) : ℝ) = (D:ℝ)^2 := by push_cast; ring
  rw [hcast] at hcount
  rw [hfilt]
  -- Bound `D² e / W ≤ 2e/γ`.
  have hDW : (D:ℝ)^2 / (W:ℝ) ≤ 2 / γ := by
    rw [div_le_div_iff₀ hWposR hγpos]
    linarith [hWge]
  have hA : (D:ℝ)^2 * Real.exp 1 / (W:ℝ) ≤ 2 * Real.exp 1 / γ := by
    have := mul_le_mul_of_nonneg_right hDW (le_of_lt (Real.exp_pos 1))
    rwa [div_mul_eq_mul_div, div_mul_eq_mul_div] at this
  have hpowW : ((D:ℝ)^2 * Real.exp 1 / (W:ℝ)) ^ W ≤ (2 * Real.exp 1 / γ) ^ W :=
    pow_le_pow_left₀ (by positivity) hA W
  have hstep1 : ((W:ℝ) + 1) * ((D:ℝ)^2 * Real.exp 1 / (W:ℝ)) ^ W
      ≤ ((W:ℝ) + 1) * (2 * Real.exp 1 / γ) ^ W :=
    mul_le_mul_of_nonneg_left hpowW (by positivity)
  -- Pass from the natural exponent `W` to the real exponent `γ D²`.
  have hbase1 : (1:ℝ) ≤ 2 * Real.exp 1 / γ := by
    rw [le_div_iff₀ hγpos]
    have he : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (x := 1) (by norm_num)
    nlinarith [hγ4, he]
  have hWh : ((W:ℝ) + 1) ≤ γ * (D:ℝ)^2 + 1 := by linarith
  have hpowγ : (2 * Real.exp 1 / γ) ^ W ≤ (2 * Real.exp 1 / γ) ^ (γ * (D:ℝ)^2) := by
    calc (2 * Real.exp 1 / γ) ^ W
        = (2 * Real.exp 1 / γ) ^ ((W:ℝ)) := (Real.rpow_natCast _ W).symm
      _ ≤ (2 * Real.exp 1 / γ) ^ (γ * (D:ℝ)^2) :=
            Real.rpow_le_rpow_of_exponent_le hbase1 hWle
  have hstep2 : ((W:ℝ) + 1) * (2 * Real.exp 1 / γ) ^ W
      ≤ (γ * (D:ℝ)^2 + 1) * (2 * Real.exp 1 / γ) ^ (γ * (D:ℝ)^2) :=
    mul_le_mul hWh hpowγ (by positivity) (by positivity)
  -- Final real-analytic bound.
  have hstep3 := gb_real_core c γ hc hγpos hγδ hbase D
  linarith [hcount, hstep1, hstep2, hstep3]

end Work.LT
