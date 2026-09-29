import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Scale.liouville_sep
import Submission.Work.TMC7Core.Scale.coprime_reduce

open Work.TMC7Core
open Filter Topology

namespace Work.TMC7Core.Scale

/-- **S3** of the lead's C7 design (see `Submission/Work/TMC7Core/Scale/S3_GUIDE.md`):
exponentially good Liouville approximants. -/
theorem liouville_approx (α : ℝ) (hα : Irrational α) (b : ℝ) (hb : 0 < b)
    (hL : Work.TMC7Core.LiouvilleAbove α b) (Q₀ : ℕ) :
    ∃ (a : ℤ) (q : ℕ), Q₀ ≤ q ∧ Nat.Coprime (Int.natAbs a) q ∧
      |α - (a : ℝ) / (q : ℝ)| < Real.exp (-(b * (q : ℝ))) := by
  -- Separation from rationals with bounded denominator.
  obtain ⟨δ, hδpos, hsepb⟩ := liouville_sep α hα Q₀
  -- A threshold beyond which `e^{-b k} < δ`.
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℕ, Real.exp (-(b * (K₂ : ℝ))) < δ := by
    obtain ⟨K₂, hK₃⟩ := exists_nat_gt (-(Real.log δ) / b)
    refine ⟨K₂, ?_⟩
    have h₁ : -(Real.log δ) < (K₂ : ℝ) * b := (div_lt_iff₀ hb).mp hK₃
    have h₂ : -(b * (K₂ : ℝ)) < Real.log δ := by nlinarith
    have h₃ : Real.exp (-(b * (K₂ : ℝ))) < Real.exp (Real.log δ) := Real.exp_lt_exp.mpr h₂
    rwa [Real.exp_log hδpos] at h₃
  -- Take a Liouville denominator beyond that threshold, beyond `Q₀`, and `≥ 2`.
  obtain ⟨k, hkK, hkfd⟩ :=
    Filter.frequently_atTop.1 hL (max (max K₂ Q₀) 2)
  have hK₂k : K₂ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hkK
  have hQ₀k : Q₀ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hkK
  have h₂k : 2 ≤ k := le_trans (le_max_right _ _) hkK
  have hk₁ : 1 ≤ k := by omega
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkexp : Real.exp (-(b * (k : ℝ))) < δ := by
    have h₄ : (K₂ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hK₂k
    have h₅ : -(b * (k : ℝ)) ≤ -(b * (K₂ : ℝ)) := by nlinarith [hb]
    linarith [Real.exp_le_exp.mpr h₅]
  -- Reduce `round (k α) / k` to lowest terms.
  obtain ⟨a, q, hq₁, hqk, hcop, heq⟩ := coprime_reduce (m := round ((k : ℝ) * α)) hk₁
  have hfdval : Work.TMC7Core.fracDist ((k : ℝ) * α) =
      (k : ℝ) * |α - (round ((k : ℝ) * α) : ℝ) / (k : ℝ)| := by
    rw [Work.TMC7Core.fracDist]
    have h : (k : ℝ) * α - (round ((k : ℝ) * α) : ℝ) =
        (k : ℝ) * (α - (round ((k : ℝ) * α) : ℝ) / (k : ℝ)) := by
      field_simp
    rw [h, abs_mul, abs_of_pos hkR]
  have habs : |α - (a : ℝ) / (q : ℝ)| = Work.TMC7Core.fracDist ((k : ℝ) * α) / (k : ℝ) := by
    rw [heq, hfdval]
    rw [eq_div_iff (ne_of_gt hkR)]
    ring
  have hsmall : |α - (a : ℝ) / (q : ℝ)| < δ := by
    rw [habs]
    have h₁ : Work.TMC7Core.fracDist ((k : ℝ) * α) / (k : ℝ) <
        Real.exp (-(b * (k : ℝ))) / (k : ℝ) := div_lt_div_of_pos_right hkfd hkR
    have h₂ : Real.exp (-(b * (k : ℝ))) / (k : ℝ) ≤ Real.exp (-(b * (k : ℝ))) :=
      div_le_self (Real.exp_pos _).le (by exact_mod_cast hk₁)
    linarith
  refine ⟨a, q, ?_, hcop, ?_⟩
  · -- `q ≥ Q₀`: otherwise `δ` would separate `α` from `a/q`.
    by_contra hcon
    have hqQ : q ≤ Q₀ := by omega
    have h := hsepb a q hq₁ hqQ
    linarith
  · have h₃ : |α - (a : ℝ) / (q : ℝ)| < Real.exp (-(b * (k : ℝ))) / (k : ℝ) := by
      rw [habs]; exact div_lt_div_of_pos_right hkfd hkR
    have h₄ : Real.exp (-(b * (k : ℝ))) / (k : ℝ) ≤ Real.exp (-(b * (q : ℝ))) := by
      have hbq : -(b * (k : ℝ)) ≤ -(b * (q : ℝ)) := by
        have hqk' : (q : ℝ) ≤ (k : ℝ) := by exact_mod_cast hqk
        nlinarith [hb]
      have hle : Real.exp (-(b * (k : ℝ))) / (k : ℝ) ≤ Real.exp (-(b * (k : ℝ))) :=
        div_le_self (Real.exp_pos _).le (by exact_mod_cast hk₁)
      linarith [Real.exp_le_exp.mpr hbq]
    linarith

end Work.TMC7Core.Scale
