import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDEstimates.dmin_facts
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.Sig2.ellXY_pair_le
import Submission.Work.HP.ceil_logb_bounds

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates.Sigma2_44_I_lo_aux

open Work.HP

/-- **Pure-arithmetic core of the shell data.**

For reals `x, y ≥ 1`, `D ≥ 1` and `Δ ≥ 1` with `x * y * D ≤ Δ`, writing
`m₁ = ⌈log₂ x⌉`, `m₂ = ⌈log₂ y⌉`:

* `x ≤ 2^{m₁}` and `y ≤ 2^{m₂}` (the ceiling of the binary logarithm is an upper dyadic shell);
* `D ≤ 4 Δ / 2^{m₁ + m₂}` (the product of the two shell radii overshoots `x y` by at most `4`);
* `2^{m₁ + m₂} ≤ 4 Δ` (the shell index is admissible);
* `m₁ + m₂ ≤ ⌊log₂ (4 Δ)⌋` (the shell index is within the dyadic range of `4 Δ`). -/
lemma shell_data_core {x y D Δ : ℝ} (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hD1 : 1 ≤ D)
    (hprod : x * y * D ≤ Δ) (hΔ1 : 1 ≤ Δ) :
    x ≤ (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ ∧
    y ≤ (2 : ℝ) ^ ⌈Real.logb 2 y⌉₊ ∧
    D ≤ 4 * Δ / (2 : ℝ) ^ (⌈Real.logb 2 x⌉₊ + ⌈Real.logb 2 y⌉₊) ∧
    (2 : ℝ) ^ (⌈Real.logb 2 x⌉₊ + ⌈Real.logb 2 y⌉₊) ≤ 4 * Δ ∧
    ⌈Real.logb 2 x⌉₊ + ⌈Real.logb 2 y⌉₊ ≤ ⌊Real.logb 2 (4 * Δ)⌋₊ := by
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
  have hypos : 0 < y := lt_of_lt_of_le one_pos hy1
  have hΔpos : 0 < Δ := lt_of_lt_of_le one_pos hΔ1
  have hxypos : 0 < x * y := mul_pos hxpos hypos
  obtain ⟨hxle, hx2⟩ := Work.HP.ceil_logb_bounds hx1
  obtain ⟨hyle, hy2⟩ := Work.HP.ceil_logb_bounds hy1
  have hMpos : 0 < (2 : ℝ) ^ (⌈Real.logb 2 x⌉₊ + ⌈Real.logb 2 y⌉₊) := by positivity
  -- the product of the two dyadic radii overshoots `x * y` by at most `4`
  have hM : (2 : ℝ) ^ (⌈Real.logb 2 x⌉₊ + ⌈Real.logb 2 y⌉₊) ≤ 4 * (x * y) := by
    rw [pow_add]
    calc (2 : ℝ) ^ ⌈Real.logb 2 x⌉₊ * (2 : ℝ) ^ ⌈Real.logb 2 y⌉₊
        ≤ (2 * x) * (2 * y) := mul_le_mul hx2 hy2 (by positivity) (by positivity)
      _ = 4 * (x * y) := by ring
  -- `x * y ≤ Δ`
  have hxyΔ : x * y ≤ Δ := by
    have h := mul_le_mul_of_nonneg_left hD1 (le_of_lt hxypos)
    nlinarith [hprod, h]
  have hM4Δ : (2 : ℝ) ^ (⌈Real.logb 2 x⌉₊ + ⌈Real.logb 2 y⌉₊) ≤ 4 * Δ := by
    nlinarith [hM, hxyΔ]
  have hDdiv : D ≤ Δ / (x * y) := by
    rw [le_div_iff₀ hxypos]
    nlinarith [hprod]
  have hstep : Δ / (x * y) ≤ 4 * Δ / (2 : ℝ) ^ (⌈Real.logb 2 x⌉₊ + ⌈Real.logb 2 y⌉₊) := by
    rw [le_div_iff₀ hMpos, div_mul_eq_mul_div, div_le_iff₀ hxypos]
    nlinarith [hM, hΔpos]
  refine ⟨hxle, hyle, hDdiv.trans hstep, hM4Δ, ?_⟩
  apply Nat.le_floor
  have h4Δpos : 0 < 4 * Δ := by linarith
  have hlog := (Real.logb_le_logb (show (1 : ℝ) < 2 by norm_num) hMpos h4Δpos).mpr hM4Δ
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
  simpa using hlog

theorem CountXYD3_shell_data :
    ∀ (B Δ : ℝ), 1 ≤ B → 1 ≤ Δ → ∀ p : (Fin 5 → ℤ) × (Fin 5 → ℤ),
      p ∈ Work.HP.Omega 4 4 B →
      Work.HP.eNorm p.1 * Work.HP.eNorm p.2 *
          Work.HP.dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ →
      Work.HP.eNorm p.1 ≤ (2:ℝ) ^ ⌈Real.logb 2 (Work.HP.eNorm p.1)⌉₊ ∧
      Work.HP.eNorm p.2 ≤ (2:ℝ) ^ ⌈Real.logb 2 (Work.HP.eNorm p.2)⌉₊ ∧
      Work.HP.dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))
        ≤ 4 * Δ / (2:ℝ) ^ (⌈Real.logb 2 (Work.HP.eNorm p.1)⌉₊ + ⌈Real.logb 2 (Work.HP.eNorm p.2)⌉₊) ∧
      (2:ℝ) ^ (⌈Real.logb 2 (Work.HP.eNorm p.1)⌉₊ + ⌈Real.logb 2 (Work.HP.eNorm p.2)⌉₊) ≤ 4 * Δ ∧
      ⌈Real.logb 2 (Work.HP.eNorm p.1)⌉₊ + ⌈Real.logb 2 (Work.HP.eNorm p.2)⌉₊
        ≤ ⌊Real.logb 2 (4 * Δ)⌋₊ := by
  intro B Δ _hB hΔ p hp hprod
  obtain ⟨hX1, hX2, hne1, hne2⟩ := hp
  have hprim1 : Work.HP.IsPrim p.1 := hX1.1
  have hprim2 : Work.HP.IsPrim p.2 := hX2.1
  have hli : LinearIndependent ℤ ![p.1, p.2] :=
    Work.HP.Sig2.li_of_mem_Omega 4 4 B p ⟨hX1, hX2, hne1, hne2⟩
  obtain ⟨_, _, hdmin_one, _⟩ := Work.HP.MDEstimates.dmin_facts 4 (by norm_num)
  have hD1 : 1 ≤ Work.HP.dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) := hdmin_one p.1 p.2 hli
  have hx1 : 1 ≤ Work.HP.eNorm p.1 :=
    Work.HP.one_le_eNorm_of_ne_zero (Work.HP.isPrim_ne_zero hprim1)
  have hy1 : 1 ≤ Work.HP.eNorm p.2 :=
    Work.HP.one_le_eNorm_of_ne_zero (Work.HP.isPrim_ne_zero hprim2)
  exact shell_data_core hx1 hy1 hD1 hprod hΔ

end Work.HP.MDEstimates.Sigma2_44_I_lo_aux
