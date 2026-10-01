import Mathlib
import Submission.Work.LinnikAreas.Density4.selberg_U_aux
import Submission.Work.LinnikAreas.Density4.Udecay.intervalIntegrable_muRecip_div
import Submission.Work.LinnikAreas.Density4.Udecay.muRecip_unit_integral
import Submission.Work.LinnikAreas.Density4.Udecay.muRecip_tail_integral
import Submission.Work.LinnikAreas.Density4.Udecay.selU_abel

namespace Work.LinnikAreas.Density4.Udecay

open scoped BigOperators
open MeasureTheory

/-- `A(t) = Σ_{m ≤ ⌊t⌋} μ(m)/m` is a step function, so the integral of `A(t)/t` against
`dt/t` over `[1,x]` splits at the integers: it is the Abel sum
`Σ_{1 ≤ k < ⌊x⌋} muRecipSum k · (log(k+1) - log k)` together with the last piece
`muRecipSum ⌊x⌋ · (log x - log ⌊x⌋)` over `[⌊x⌋, x]`. -/
theorem step_integral_split (x : ℝ) (hx : 1 ≤ x) :
    ∫ t in (1 : ℝ)..x, Work.LinnikAreas.Density4.muRecip t / t
      = (∑ k ∈ Finset.Ico 1 ⌊x⌋₊, Commons.NumberTheory.Moebius.muRecipSum k
            * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)))
        + Commons.NumberTheory.Moebius.muRecipSum ⌊x⌋₊ * (Real.log x - Real.log (⌊x⌋₊ : ℝ)) := by
  have hK1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hK1r : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hK1
  have hKx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hn1 : ∀ k ∈ Set.Ico 1 ⌊x⌋₊,
      IntervalIntegrable (fun t : ℝ => Work.LinnikAreas.Density4.muRecip t / t)
        MeasureTheory.volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
    fun k hk => intervalIntegrable_muRecip_div (k : ℝ) ((k + 1 : ℕ) : ℝ)
      (by exact_mod_cast hk.1) (by push_cast; linarith)
  have hIK : IntervalIntegrable (fun t : ℝ => Work.LinnikAreas.Density4.muRecip t / t)
      MeasureTheory.volume ((1 : ℕ) : ℝ) ((⌊x⌋₊ : ℕ) : ℝ) :=
    IntervalIntegrable.trans_iterate_Ico
      (f := fun t : ℝ => Work.LinnikAreas.Density4.muRecip t / t)
      (μ := MeasureTheory.volume) (a := fun k => (k : ℝ)) hK1 hn1
  have hA : ∫ t in ((1 : ℕ) : ℝ)..((⌊x⌋₊ : ℕ) : ℝ), Work.LinnikAreas.Density4.muRecip t / t
      = ∑ k ∈ Finset.Ico 1 ⌊x⌋₊, ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ),
          Work.LinnikAreas.Density4.muRecip t / t := by
    rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico
      (f := fun t : ℝ => Work.LinnikAreas.Density4.muRecip t / t)
      (μ := MeasureTheory.volume) (a := fun k => (k : ℝ)) hK1 hn1]
  have hB : ∫ t in ((1 : ℕ) : ℝ)..x, Work.LinnikAreas.Density4.muRecip t / t
      = (∫ t in ((1 : ℕ) : ℝ)..((⌊x⌋₊ : ℕ) : ℝ), Work.LinnikAreas.Density4.muRecip t / t)
        + ∫ t in ((⌊x⌋₊ : ℕ) : ℝ)..x, Work.LinnikAreas.Density4.muRecip t / t := by
    rw [intervalIntegral.integral_add_adjacent_intervals hIK
      (intervalIntegrable_muRecip_div ((⌊x⌋₊ : ℕ) : ℝ) x hK1r hKx)]
  have hgoal : ∫ t in ((1 : ℕ) : ℝ)..x, Work.LinnikAreas.Density4.muRecip t / t
      = (∑ k ∈ Finset.Ico 1 ⌊x⌋₊, Commons.NumberTheory.Moebius.muRecipSum k
            * (Real.log ((k : ℝ) + 1) - Real.log (k : ℝ)))
        + Commons.NumberTheory.Moebius.muRecipSum ⌊x⌋₊ * (Real.log x - Real.log (⌊x⌋₊ : ℝ)) := by
    rw [hB, hA, muRecip_tail_integral x hx]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Nat.cast_add, Nat.cast_one]
    rw [muRecip_unit_integral k (Finset.mem_Ico.mp hk).1]
  simpa using hgoal

/-- `selU x = ∫_1^x A(t) dt/t` where `A(t) = muRecip t = Σ_{m ≤ ⌊t⌋} μ(m)/m`.
Summing by parts: expanding the integral over the unit steps gives the Abel sum
`Σ_{k < ⌊x⌋} muRecipSum k (log(k+1) - log k)`, which by `logWeightedMuSum_eq` is
`logWeightedMuSum ⌊x⌋ = Σ_{m ≤ ⌊x⌋} μ(m)(log ⌊x⌋ - log m)/m`, and the last piece contributes
`muRecipSum ⌊x⌋ (log x - log ⌊x⌋)`; the two together are `Σ_{m ≤ ⌊x⌋} μ(m) log(x/m)/m = selU x`. -/
theorem step_integral : ∀ x : ℝ, 1 ≤ x →
    Work.LinnikAreas.Density4.selU x
      = ∫ t in (1 : ℝ)..x, Work.LinnikAreas.Density4.muRecip t / t := by
  intro x hx
  rw [selU_abel x hx, step_integral_split x hx]
  rw [add_right_cancel_iff]
  have hK1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hIco : Finset.Ico 1 ⌊x⌋₊ = Finset.Icc 1 (⌊x⌋₊ - 1) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  conv_lhs => rw [← Nat.sub_add_cancel hK1]
  rw [hIco]
  exact Commons.NumberTheory.Moebius.logWeightedMuSum_eq (⌊x⌋₊ - 1)

end Work.LinnikAreas.Density4.Udecay
