import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Monotonicity of the CA exponent parameter `μ(p,·)` (Nicolas (4.11))

For a prime power parameter `ε > 0` and integer `p ≥ 2`,

  μ(p,ε) := log((p^{1+ε} − 1) / (p^{1+ε} − p)) / log p ,   a(p,ε) = ⌊μ(p,ε)⌋₊ .

`caExp_mono_of_le` records that `p ↦ μ(p,ε)` is *decreasing* in `ε`: the quotient
`(p^{1+ε}−1)/(p^{1+ε}−p) = 1 + (p−1)/(p^{1+ε}−p)` decreases as `ε` increases (the
denominator `p^{1+ε}−p` grows), hence so does its (floor of) log-ratio.
-/

namespace Commons.NumberTheory.Robin

/-- `p^{1+ε} − p > 0` for `p ≥ 2`, `ε > 0`. -/
private lemma rpow_sub_one_pos (p : ℕ) (ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) :
    0 < ((p : ℝ) ^ (1 + ε)) - (p : ℝ) := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpε : 1 < (p : ℝ) ^ ε := by
    rw [Real.one_lt_rpow_iff (le_of_lt hp0r)]
    exact Or.inl ⟨hp1r, hε⟩
  have hp1ε : (p : ℝ) ^ (1 + ε) = (p : ℝ) * (p : ℝ) ^ ε := by
    rw [Real.rpow_add hp0r, Real.rpow_one]
  rw [hp1ε]
  have hmul : (p : ℝ) < (p : ℝ) * (p : ℝ) ^ ε := by
    calc
      (p : ℝ) = (p : ℝ) * 1 := by ring
      _ < (p : ℝ) * (p : ℝ) ^ ε := mul_lt_mul_of_pos_left hpε hp0r
  linarith

/-- `(p^{1+ε}−1)/(p^{1+ε}−p) = 1 + (p−1)/(p^{1+ε}−p)` for `p ≥ 2`, `ε > 0`. -/
private lemma caQuot_eq_one_add (p : ℕ) (ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) :
    (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) =
      1 + ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) := by
  have hd : ((p : ℝ) ^ (1 + ε)) - (p : ℝ) ≠ 0 := ne_of_gt (rpow_sub_one_pos p ε hp hε)
  have hnum : ((p : ℝ) ^ (1 + ε) - 1) = (((p : ℝ) ^ (1 + ε)) - (p : ℝ)) + ((p : ℝ) - 1) := by
    ring
  rw [hnum, add_div, div_self hd]

/-- `p^{1+δ} − p` is increasing in the exponent `δ` (for `p ≥ 2`). -/
private lemma rpow_sub_p_mono (p : ℕ) (δ δ' : ℝ) (hp : 2 ≤ p) (hδle : δ ≤ δ') :
    ((p : ℝ) ^ (1 + δ)) - (p : ℝ) ≤ ((p : ℝ) ^ (1 + δ')) - (p : ℝ) := by
  have hp1le : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hle' : 1 + δ ≤ 1 + δ' := by linarith
  have h := Real.rpow_le_rpow_of_exponent_le hp1le hle'
  linarith

/-- The quotient `(p^{1+δ}−1)/(p^{1+δ}−p)` is *decreasing* in `δ`
(for `p ≥ 2`, positive exponents). -/
private lemma caQuot_antitone (p : ℕ) (δ δ' : ℝ) (hp : 2 ≤ p) (hδ : 0 < δ) (hδ' : 0 < δ')
    (hδle : δ ≤ δ') :
    (((p : ℝ) ^ (1 + δ') - 1) / (((p : ℝ) ^ (1 + δ')) - (p : ℝ))) ≤
      (((p : ℝ) ^ (1 + δ) - 1) / (((p : ℝ) ^ (1 + δ)) - (p : ℝ))) := by
  have hDpos : 0 < ((p : ℝ) ^ (1 + δ)) - (p : ℝ) := rpow_sub_one_pos p δ hp hδ
  have hDpos' : 0 < ((p : ℝ) ^ (1 + δ')) - (p : ℝ) := rpow_sub_one_pos p δ' hp hδ'
  have hDle : ((p : ℝ) ^ (1 + δ)) - (p : ℝ) ≤ ((p : ℝ) ^ (1 + δ')) - (p : ℝ) :=
    rpow_sub_p_mono p δ δ' hp hδle
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1pos : 0 < (p : ℝ) - 1 := by linarith
  have hq : ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + δ')) - (p : ℝ)) ≤
      ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + δ)) - (p : ℝ)) :=
    div_le_div_of_nonneg_left (le_of_lt hp1pos) hDpos hDle
  calc
    (((p : ℝ) ^ (1 + δ') - 1) / (((p : ℝ) ^ (1 + δ')) - (p : ℝ)))
        = 1 + ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + δ')) - (p : ℝ)) := caQuot_eq_one_add p δ' hp hδ'
    _ ≤ 1 + ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + δ)) - (p : ℝ)) := by
        linarith
    _ = (((p : ℝ) ^ (1 + δ) - 1) / (((p : ℝ) ^ (1 + δ)) - (p : ℝ))) :=
        (caQuot_eq_one_add p δ hp hδ).symm

/-- `μ(p,ε') ≤ μ(p,ε)` whenever `0 < ε ≤ ε'` (`p ≥ 2`), hence also for the
natural-part floors `⌊μ⌋₊` (Nicolas (4.11)). -/
theorem caExp_mono_of_le (p : ℕ) (ε ε' : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hε' : 0 < ε')
    (hle : ε ≤ ε') :
    Nat.floor (Real.log (((p : ℝ) ^ (1 + ε') - 1) / (((p : ℝ) ^ (1 + ε')) - (p : ℝ))) / Real.log (p : ℝ))
      ≤ Nat.floor (Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ)) := by
  have hQ : (((p : ℝ) ^ (1 + ε') - 1) / (((p : ℝ) ^ (1 + ε')) - (p : ℝ))) ≤
      (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) :=
    caQuot_antitone p ε ε' hp hε hε' hle
  have hQpos' : 0 < (((p : ℝ) ^ (1 + ε') - 1) / (((p : ℝ) ^ (1 + ε')) - (p : ℝ))) := by
    rw [caQuot_eq_one_add p ε' hp hε']
    have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp1pos : 0 < (p : ℝ) - 1 := by linarith
    have hDpos' : 0 < ((p : ℝ) ^ (1 + ε')) - (p : ℝ) := rpow_sub_one_pos p ε' hp hε'
    have hppos : 0 < ((p : ℝ) - 1) / (((p : ℝ) ^ (1 + ε')) - (p : ℝ)) := div_pos hp1pos hDpos'
    linarith
  have hlogp : 0 < Real.log (p : ℝ) := by
    have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    exact Real.log_pos hp1r
  have hlog : Real.log (((p : ℝ) ^ (1 + ε') - 1) / (((p : ℝ) ^ (1 + ε')) - (p : ℝ))) ≤
      Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) :=
    Real.log_le_log hQpos' hQ
  have hmu : Real.log (((p : ℝ) ^ (1 + ε') - 1) / (((p : ℝ) ^ (1 + ε')) - (p : ℝ))) / Real.log (p : ℝ) ≤
      Real.log (((p : ℝ) ^ (1 + ε) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ) :=
    div_le_div_of_nonneg_right hlog (le_of_lt hlogp)
  exact Nat.floor_mono hmu

end Commons.NumberTheory.Robin