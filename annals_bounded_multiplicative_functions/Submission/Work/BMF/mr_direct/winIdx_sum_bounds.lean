import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.goodSet_E1_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Sum bounds for the integer windows `winIdx K X j`

The four elementary estimates on `∑_{m ∈ W} 1/m²` used by the Buchstab/Ramaré
decomposition of `remPoly`:

* `∑_{m ∈ ℕ ∩ [A,B]} 1/m² ≤ 2/A` for `A > 0` (harmonic telescoping);
* `∑_{m ∈ winIdx K X j} 1/m² ≤ 2 e^{(j+1)/K}/X` for `X ≥ 1`;
* `∑_{m ∈ winIdx K X j} 1/m² ≤ 2` for `X ≥ 1` (uniform in `K`, `j`);
* the window is empty (hence the sum vanishes) as soon as `log (2X) < j/K`.

The first three are the lemmas `natIcc_inv_sq_sum_le`, `winIdx_inv_sq_le` and
`winIdx_inv_sq_le_two` of `Submission.Work.BMF.mr_direct.goodSet_E1_bound`; the last one
is proved here from the definition of `winIdx` as `ℕ ∩ [X e^{-(j+1)/K}, 2X e^{-j/K}]`.
-/

namespace Work.BMF.mr_direct

/-- If `log (2X) < j/K` (and `X ≥ 1`) then the upper end `2X e^{-j/K}` of the window
`winIdx K X j` is `< 1`, while its lower end is positive, so the window is empty. -/
lemma winIdx_eq_empty_of_log_lt {X K : ℝ} {j : ℕ} (hX : 1 ≤ X)
    (h : Real.log (2 * X) < (j : ℝ) / K) : Work.BMF.mrDirect.winIdx K X j = ∅ := by
  have hXpos : 0 < X := by linarith
  have h2Xpos : 0 < 2 * X := by linarith
  -- `2X < e^{j/K}`, i.e. `2X e^{-j/K} < 1`
  have hexp : 2 * X < Real.exp ((j : ℝ) / K) := (Real.log_lt_iff_lt_exp h2Xpos).mp h
  have hup : 2 * X * Real.exp (-(j : ℝ) / K) < 1 := by
    have hpos : 0 < Real.exp ((j : ℝ) / K) := Real.exp_pos _
    rw [show -(j : ℝ) / K = -((j : ℝ) / K) by ring, Real.exp_neg, ← div_eq_mul_inv,
      div_lt_one hpos]
    exact hexp
  have hfloor : ⌊2 * X * Real.exp (-(j : ℝ) / K)⌋₊ = 0 := Nat.floor_eq_zero.mpr hup
  have hceil : 1 ≤ ⌈X * Real.exp (-((j : ℝ) + 1) / K)⌉₊ :=
    Nat.ceil_pos.mpr (mul_pos hXpos (Real.exp_pos _))
  rw [Work.BMF.mrDirect.winIdx, Work.BMF.natIcc, hfloor]
  exact Finset.Icc_eq_empty_iff.mpr
    (not_le.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hceil))

theorem winIdx_sum_bounds :
    (∀ (A B : ℝ), 0 < A →
        (∑ m ∈ Work.BMF.natIcc A B, (1 : ℝ) / (m : ℝ) ^ 2) ≤ 2 / A) ∧
    (∀ (X K : ℝ) (j : ℕ), 1 ≤ X →
        (∑ m ∈ Work.BMF.mrDirect.winIdx K X j, (1 : ℝ) / (m : ℝ) ^ 2)
          ≤ 2 * Real.exp (((j : ℝ) + 1) / K) / X) ∧
    (∀ (X K : ℝ) (j : ℕ), 1 ≤ X →
        (∑ m ∈ Work.BMF.mrDirect.winIdx K X j, (1 : ℝ) / (m : ℝ) ^ 2) ≤ 2) ∧
    (∀ (X K : ℝ) (j : ℕ), 1 ≤ X → Real.log (2 * X) < (j : ℝ) / K →
        (∑ m ∈ Work.BMF.mrDirect.winIdx K X j, (1 : ℝ) / (m : ℝ) ^ 2) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B hA
    exact natIcc_inv_sq_sum_le A B hA
  · intro X K j hX
    exact winIdx_inv_sq_le X K j hX
  · intro X K j hX
    exact winIdx_inv_sq_le_two X K j (by linarith)
  · intro X K j hX hlog
    rw [winIdx_eq_empty_of_log_lt hX hlog, Finset.sum_empty]


end Work.BMF.mr_direct
