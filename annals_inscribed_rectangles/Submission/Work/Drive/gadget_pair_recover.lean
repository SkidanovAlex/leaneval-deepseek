import Mathlib

namespace Work.Drive

set_option linter.unusedVariables false in
/-- Recovering the datum from the normalized direction: if the two normalised points `d = u/r`,
`d' = u'/r'` agree and have the same (positive) radius `r = r'`, then the two data agree.

Here `u = (1 - lam H) √A dc` and `r = √(‖u‖² + H)`, with `H = A (1 - ‖dc‖²)`; the point is that
`u` determines `A` through `A = H + ‖u‖²` (since `‖u‖² = A ‖dc‖²`), so equality of the normalised
points plus equality of the radii forces `H = H'`, then `A = A'`, then `dc = dc'`. -/
theorem gadget_pair_recover (lam : ℝ → ℝ) {A A' H H' : ℝ} {dc dc' : ℂ} (hA : 0 < A) (hA' : 0 < A')
    (hdc : dc ≠ 0) (hdc' : dc' ≠ 0) (hk : 0 < 1 - lam H) (hk' : 0 < 1 - lam H')
    (hHA : H = A * (1 - ‖dc‖ ^ 2)) (hHA' : H' = A' * (1 - ‖dc'‖ ^ 2)) :
    (let u : ℂ := ((1 - lam H : ℝ) : ℂ) * ((Real.sqrt A : ℝ) : ℂ) * dc
     let u' : ℂ := ((1 - lam H' : ℝ) : ℂ) * ((Real.sqrt A' : ℝ) : ℂ) * dc'
     let r : ℝ := Real.sqrt (‖u‖ ^ 2 + H)
     let r' : ℝ := Real.sqrt (‖u'‖ ^ 2 + H')
     let d : ℂ := u / ((r : ℝ) : ℂ)
     let d' : ℂ := u' / ((r' : ℝ) : ℂ)
     0 < r → 0 < r' → r = r' → d = d' → H = H' ∧ A = A' ∧ dc = dc') := by
  dsimp only
  intro hr hr' hrr hdd
  set U : ℂ := ((1 - lam H : ℝ) : ℂ) * ((Real.sqrt A : ℝ) : ℂ) * dc with hU
  set U' : ℂ := ((1 - lam H' : ℝ) : ℂ) * ((Real.sqrt A' : ℝ) : ℂ) * dc' with hU'
  set s : ℝ := Real.sqrt (‖U‖ ^ 2 + H) with hs
  set s' : ℝ := Real.sqrt (‖U'‖ ^ 2 + H') with hs'
  rw [hs] at hr
  rw [hs'] at hr'
  have hs0 : 0 < ‖U‖ ^ 2 + H := Real.sqrt_pos.mp hr
  have hs0' : 0 < ‖U'‖ ^ 2 + H' := Real.sqrt_pos.mp hr'
  have hsq : ‖U‖ ^ 2 + H = ‖U'‖ ^ 2 + H' := by
    rw [hs, hs'] at hrr
    exact (Real.sqrt_inj hs0.le hs0'.le).mp hrr
  have hsC' : ((s' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr')
  have hu : U = U' := by
    have hdd' : U / ((s' : ℝ) : ℂ) = U' / ((s' : ℝ) : ℂ) := by
      rw [hrr] at hdd
      exact hdd
    have h2 : U / ((s' : ℝ) : ℂ) * ((s' : ℝ) : ℂ) = U' / ((s' : ℝ) : ℂ) * ((s' : ℝ) : ℂ) :=
      congrArg (fun z : ℂ => z * ((s' : ℝ) : ℂ)) hdd'
    rwa [div_mul_cancel₀ U hsC', div_mul_cancel₀ U' hsC'] at h2
  have hnorm : ‖U‖ = ‖U'‖ := by rw [hu]
  have hH : H = H' := by
    rw [hnorm] at hsq
    linarith
  have hcne : ((1 - lam H' : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    linarith
  have hsAB : ((Real.sqrt A : ℝ) : ℂ) * dc = ((Real.sqrt A' : ℝ) : ℂ) * dc' := by
    have h : ((1 - lam H' : ℝ) : ℂ) * (((Real.sqrt A : ℝ) : ℂ) * dc)
        = ((1 - lam H' : ℝ) : ℂ) * (((Real.sqrt A' : ℝ) : ℂ) * dc') := by
      have hh : U = U' := hu
      rw [hU, hU', hH] at hh
      simpa only [mul_assoc] using hh
    exact mul_left_cancel₀ hcne h
  have hnsA : Complex.normSq (((Real.sqrt A : ℝ) : ℂ) * dc) = A * ‖dc‖ ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
      Real.mul_self_sqrt hA.le]
  have hnsA' : Complex.normSq (((Real.sqrt A' : ℝ) : ℂ) * dc') = A' * ‖dc'‖ ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
      Real.mul_self_sqrt hA'.le]
  have hns : Complex.normSq (((Real.sqrt A : ℝ) : ℂ) * dc)
      = Complex.normSq (((Real.sqrt A' : ℝ) : ℂ) * dc') := by rw [hsAB]
  have hmult : A * ‖dc‖ ^ 2 = A' * ‖dc'‖ ^ 2 := by
    rw [← hnsA, ← hnsA']
    exact hns
  have e1 : A = H + A * ‖dc‖ ^ 2 := by rw [hHA]; ring
  have e2 : A' = H' + A' * ‖dc'‖ ^ 2 := by rw [hHA']; ring
  have hAeq : A = A' := by linarith
  have hdcEq : dc = dc' := by
    have hsqrtne : ((Real.sqrt A : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (Real.sqrt_pos_of_pos hA)
    have h := hsAB
    rw [← hAeq] at h
    exact mul_left_cancel₀ hsqrtne h
  exact ⟨hH, hAeq, hdcEq⟩

end Work.Drive
