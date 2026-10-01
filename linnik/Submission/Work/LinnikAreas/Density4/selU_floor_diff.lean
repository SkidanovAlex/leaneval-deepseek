import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs

namespace Work.LinnikAreas.Density4

open Finset

/-- Splitting `selU`: `selU x = muRecipSum ⌊x⌋₊ * log x - Σ_{m ≤ ⌊x⌋₊} μ(m) log m / m`. -/
lemma selU_eq_muRecipSum (x : ℝ) (hx : 0 < x) :
    selU x = Commons.NumberTheory.Moebius.muRecipSum ⌊x⌋₊ * Real.log x
      - ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
          (ArithmeticFunction.moebius m : ℝ) * Real.log (m : ℝ) / (m : ℝ) := by
  unfold selU Commons.NumberTheory.Moebius.muRecipSum
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  rw [Real.log_div (ne_of_gt hx) hmne]
  ring

theorem selU_floor_diff (x : ℝ) (hx : 1 ≤ x) :
    Work.LinnikAreas.Density4.selU x - Work.LinnikAreas.Density4.selU ((⌊x⌋₊ : ℕ) : ℝ)
      = Commons.NumberTheory.Moebius.muRecipSum ⌊x⌋₊ * Real.log (x / (⌊x⌋₊ : ℝ)) := by
  have hxpos : 0 < x := by linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have hNpos : (0 : ℝ) < (⌊x⌋₊ : ℕ) := by exact_mod_cast hN1
  have h1 := selU_eq_muRecipSum x hxpos
  have h2 := selU_eq_muRecipSum (((⌊x⌋₊ : ℕ) : ℝ)) hNpos
  rw [Nat.floor_natCast] at h2
  rw [h1, h2, Real.log_div (ne_of_gt hxpos) (ne_of_gt hNpos)]
  ring

end Work.LinnikAreas.Density4
