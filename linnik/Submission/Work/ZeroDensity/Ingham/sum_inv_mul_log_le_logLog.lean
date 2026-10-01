import Mathlib

namespace Work.ZeroDensity.Ingham

/-- Reindexing the sum over `Icc n M` as a sum over `Ico (n-1) M` of the shifted argument;
this is the form in which the sum/integral comparison `AntitoneOn.sum_le_integral_Ico` applies. -/
private lemma sum_Icc_eq_sum_Ico_one_div_mul_log (M n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.Icc n M, (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)))
      = ∑ i ∈ Finset.Ico (n - 1) M,
          (1 : ℝ) / (((i + 1 : ℕ) : ℝ) * Real.log (((i + 1 : ℕ) : ℝ))) := by
  have hA : Finset.Ico n (M + 1) = Finset.Ico ((n - 1) + 1) (M + 1) := by
    rw [Nat.sub_add_cancel hn]
  calc (∑ k ∈ Finset.Icc n M, (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)))
      = ∑ k ∈ Finset.Ico n (M + 1), (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)) := by
          rw [Finset.Ico_add_one_right_eq_Icc n M]
      _ = ∑ k ∈ Finset.Ico ((n - 1) + 1) (M + 1),
            (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)) := by rw [hA]
      _ = ∑ i ∈ Finset.Ico (n - 1) M,
            (1 : ℝ) / (((1 + i : ℕ) : ℝ) * Real.log (((1 + i : ℕ) : ℝ))) := by
          rw [← Finset.sum_Ico_add (fun k : ℕ => (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)))
                (n - 1) M 1]
      _ = ∑ i ∈ Finset.Ico (n - 1) M,
            (1 : ℝ) / (((i + 1 : ℕ) : ℝ) * Real.log (((i + 1 : ℕ) : ℝ))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Nat.add_comm]

/-- For `2 ≤ a`, the function `x ↦ 1/(x log x)` is antitone on the interval `[a,b]`. -/
theorem antitoneOn_one_div_mul_log {a b : ℝ} (ha : 2 ≤ a) :
    AntitoneOn (fun x : ℝ => 1 / (x * Real.log x)) (Set.Icc a b) := by
  have hpos : ∀ x ∈ Set.Icc a b, 0 < x := fun x hx => by linarith [hx.1]
  have hlogpos : ∀ x ∈ Set.Icc a b, 0 < Real.log x :=
    fun x hx => Real.log_pos (by linarith [hx.1])
  have hmono : MonotoneOn (fun x : ℝ => x * Real.log x) (Set.Icc a b) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := hpos x hx
    have hlogle : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
    exact mul_le_mul hxy hlogle (le_of_lt (hlogpos x hx))
      (le_of_lt (lt_of_lt_of_le hx0 hxy))
  have hmap : Set.MapsTo (fun x : ℝ => x * Real.log x) (Set.Icc a b) (Set.Ioi 0) :=
    fun x hx => mul_pos (hpos x hx) (hlogpos x hx)
  have hcomp := AntitoneOn.comp_MonotoneOn (g := fun x : ℝ => x⁻¹)
    (f := fun x : ℝ => x * Real.log x) inv_antitoneOn_Ioi hmono hmap
  have hfun : ((fun x : ℝ => x⁻¹) ∘ fun x : ℝ => x * Real.log x)
      = (fun x : ℝ => 1 / (x * Real.log x)) := by
    funext x; simp [Function.comp, one_div]
  rwa [hfun] at hcomp

/-- `∫_a^b 1/(x log x) dx = log log b - log log a` for `2 ≤ a`, `2 ≤ b`. -/
theorem integral_one_div_mul_log {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (∫ x in a..b, 1 / (x * Real.log x))
      = Real.log (Real.log b) - Real.log (Real.log a) := by
  have hmem : ∀ x ∈ Set.uIcc a b, 2 ≤ x := by
    intro x hx
    simp only [Set.uIcc, Set.mem_Icc] at hx
    have h2 : 2 ≤ a ⊓ b := le_inf ha hb
    linarith [hx.1]
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => Real.log (Real.log y)) (1 / (x * Real.log x)) x := by
    intro x hx
    have hx2 : 2 ≤ x := hmem x hx
    have hx0 : x ≠ 0 := by linarith
    have hlogx : Real.log x ≠ 0 := by
      have : 0 < Real.log x := Real.log_pos (by linarith)
      linarith
    have h := (Real.hasDerivAt_log hx0).log hlogx
    have heq : x⁻¹ / Real.log x = 1 / (x * Real.log x) := by
      rw [div_eq_mul_inv, one_div, mul_inv_rev, mul_comm]
    rwa [heq] at h
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (x * Real.log x))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact continuousOn_id.mul (Real.continuousOn_log.mono (fun x hx => by
        have hx2 : 2 ≤ x := hmem x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith))
    · intro x hx
      have hx2 : 2 ≤ x := hmem x hx
      have : 0 < x * Real.log x := mul_pos (by linarith) (Real.log_pos (by linarith))
      linarith
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- The partial sum `∑_{k=n}^{M} 1/(k log k)` is bounded by the corresponding integral
`∫_{n-1}^{M} 1/(x log x) dx = log log M - log log (n-1)`. -/
theorem sum_inv_mul_log_le_logLog (M n : ℕ) (hn : 3 ≤ n) (hnM : n ≤ M) :
    (∑ k ∈ Finset.Icc n M, (1 : ℝ) / ((k : ℝ) * Real.log (k : ℝ)))
      ≤ Real.log (Real.log (M : ℝ)) - Real.log (Real.log (((n - 1 : ℕ) : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  rw [sum_Icc_eq_sum_Ico_one_div_mul_log M n hn1]
  have h2 : 2 ≤ ((n - 1 : ℕ) : ℝ) := by
    have : 2 ≤ n - 1 := by omega
    exact_mod_cast this
  have hM2 : 2 ≤ (M : ℝ) := by
    have : 2 ≤ M := by omega
    exact_mod_cast this
  have hnm : n - 1 ≤ M := by omega
  have hcmp := AntitoneOn.sum_le_integral_Ico (a := n - 1) (b := M) hnm
    (antitoneOn_one_div_mul_log (a := ((n - 1 : ℕ) : ℝ)) (b := (M : ℝ)) h2)
  have hint' := integral_one_div_mul_log (a := ((n - 1 : ℕ) : ℝ)) (b := (M : ℝ)) h2 hM2
  linarith

end Work.ZeroDensity.Ingham
