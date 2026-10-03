import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S40

namespace Work.FIChain

open Finset
open Submission.ASP

/-- **The lower bound `Ã(x) ≫ x^{3/4}`.**

Three already-proved ingredients are combined:

* `Submission.exists_const_mul_rpow_le_Aseq` (the paper's `(3.18)` asymptotic `A(x) = 4κx^{3/4}
  + O(√x)`, `κ = ∫₀¹√(1-u⁴) ≥ 0.872`): there are `cA > 0`, `XA` with
  `cA·x^{3/4} ≤ Aseq x` for all `x ≥ XA`;
* `Submission.ASP.FI_Aseq_le_const_mul_Atil` (the lower half of `(9.12)`,
  `Ã(x) ≫ A(x)`): `Acount FIa x ≤ (2/G)·Ã(x)` for `x ≥ XG`, where `G = Gprod FIg > 0`;
* `Submission.ASP.FI_Acount_eq`: `Acount FIa x = Aseq x − 1`, and
  `Submission.ASP.one_le_Acount_atil`: `Ã(x) ≥ 1`.

The two last facts let the `−1` be absorbed into the constant: from `Aseq x − 1 ≤ (2/G)·Ã(x)`
and `1 ≤ Ã(x)` we get `Aseq x ≤ (2/G + 1)·Ã(x)`, whence `cA/(2/G + 1)·x^{3/4} ≤ Ã(x)`. -/
theorem AcountAtilC_ge_const_mul_rpow :
    ∃ c : ℝ, 0 < c ∧ ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      c * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ Work.FIChain.AcountAtilC x := by
  obtain ⟨cA, hcA, XA, hAc⟩ := Submission.exists_const_mul_rpow_le_Aseq
  obtain ⟨XG, hG⟩ := Submission.ASP.FI_Aseq_le_const_mul_Atil
  have hGp : (0 : ℝ) < Submission.ASP.Gprod Submission.ASP.FIg := Submission.ASP.Gprod_FIg_pos
  refine ⟨cA / (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1), by positivity,
    max XA (max XG 1), fun x hx => ?_⟩
  change cA / (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) * (x : ℝ) ^ ((3 : ℝ) / 4)
      ≤ Acount (atil FIa) (x : ℝ)
  have hxXA : XA ≤ x := le_trans (le_max_left _ _) hx
  have hxXG : XG ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  -- the lower bound for `A(x)`
  have hA1 : cA * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Submission.Aseq x : ℝ) := hAc x hxXA
  -- `Ã(x) ≥ 1` (this absorbs the `−1` of `Acount FIa x = Aseq x − 1`)
  have hAt1 : (1 : ℝ) ≤ Acount (atil FIa) (x : ℝ) := one_le_Acount_atil x hx1
  have hG' : Acount FIa (x : ℝ)
      ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg) * Acount (atil FIa) (x : ℝ) := hG x hxXG
  rw [Submission.ASP.FI_Acount_eq x] at hG'
  -- hence `Aseq x ≤ (2/G + 1)·Ã(x)`
  have hAseq_le : (Submission.Aseq x : ℝ)
      ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) * Acount (atil FIa) (x : ℝ) := by
    nlinarith [hG', hAt1]
  have hmain : cA * (x : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) * Acount (atil FIa) (x : ℝ) :=
    le_trans hA1 hAseq_le
  have hKpos : (0 : ℝ) < 2 / Submission.ASP.Gprod Submission.ASP.FIg + 1 := by positivity
  have hfin : cA / (2 / Submission.ASP.Gprod Submission.ASP.FIg + 1) * (x : ℝ) ^ ((3 : ℝ) / 4)
      ≤ Acount (atil FIa) (x : ℝ) := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hKpos).mpr (by linarith [hmain])
  exact hfin

end Work.FIChain
