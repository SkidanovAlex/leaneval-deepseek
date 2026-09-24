import Mathlib

noncomputable section

open Set

namespace Work.NumberTheory.Chen.APSwitchUpper

/-- The auxiliary function
`F t = log (1 + t) - log (1 - t) - (2 t + (2/3) t^3)` has derivative
`2/(1 - t^2) - (2 + 2 t^2)`, valid for `|t| < 1`. -/
private lemma logPad2_L2_hasDerivAt (a : ℝ) (ha1 : a < 1) (ha2 : -1 < a) :
    HasDerivAt (fun t : ℝ => Real.log (1 + t) - Real.log (1 - t) - (2 * t + (2 / 3) * t ^ 3))
      (2 / (1 - a ^ 2) - (2 + 2 * a ^ 2)) a := by
  have hp : (1 : ℝ) + a ≠ 0 := by linarith
  have hm : (1 : ℝ) - a ≠ 0 := by linarith
  have hm2 : (1 : ℝ) - a ^ 2 ≠ 0 := by nlinarith
  have h1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + a)) a := by
    have h : HasDerivAt (fun t : ℝ => (1 : ℝ) + t) 1 a := (hasDerivAt_id a).const_add 1
    simpa using h.log hp
  have h2 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) ((-1) / (1 - a)) a := by
    have h : HasDerivAt (fun t : ℝ => (1 : ℝ) - t) (-1) a := (hasDerivAt_id a).const_sub 1
    simpa using h.log hm
  have h3 : HasDerivAt (fun t : ℝ => 2 * t + (2 / 3) * t ^ 3) (2 + 2 * a ^ 2) a := by
    have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 a := by
      simpa using (hasDerivAt_id a).const_mul (2 : ℝ)
    have hcube : HasDerivAt (fun t : ℝ => (2 / 3) * t ^ 3) (2 * a ^ 2) a := by
      have h : HasDerivAt (fun t : ℝ => t ^ 3) (3 * a ^ 2) a := by
        simpa using hasDerivAt_pow 3 a
      exact (h.const_mul ((2 : ℝ) / 3)).congr_deriv (by ring_nf)
    exact hlin.add hcube
  have htot := (h1.sub h2).sub h3
  exact htot.congr_deriv (by field_simp; ring)

/-- Core sharp lower bound: for `0 ≤ s ≤ 1/4`,
`2 s + (2/3) s^3 ≤ log ((1 + s)/(1 - s))`.
This is the truncated Taylor series of `log ((1+s)/(1-s)) = 2 (s + s^3/3 + s^5/5 + ...)`. -/
private lemma logPad2_L2_core (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 4) :
    2 * s + (2 / 3 : ℝ) * s ^ 3 ≤ Real.log ((1 + s) / (1 - s)) := by
  have hF : 0 ≤ Real.log (1 + s) - Real.log (1 - s) - (2 * s + (2 / 3) * s ^ 3) := by
    let F : ℝ → ℝ := fun t => Real.log (1 + t) - Real.log (1 - t) - (2 * t + (2 / 3) * t ^ 3)
    have hA : ∀ y ∈ Set.Icc (0 : ℝ) s, HasDerivAt F (2 / (1 - y ^ 2) - (2 + 2 * y ^ 2)) y := by
      intro y hy
      exact logPad2_L2_hasDerivAt y (by linarith [hy.2, hs1]) (by linarith [hy.1])
    have hmono : MonotoneOn F (Set.Icc (0 : ℝ) s) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 s)
        (fun y hy => (hA y hy).continuousAt.continuousWithinAt)
        (fun y hy => (hA y (interior_subset hy)).hasDerivWithinAt) ?_
      intro y hy
      have hyi : y ∈ Set.Ioo (0 : ℝ) s := by simpa [interior_Icc] using hy
      have hy0 : 0 ≤ y := le_of_lt hyi.1
      have hylt : y < 1 := by linarith [hyi.2, hs1]
      have hden : 0 < 1 - y ^ 2 := by nlinarith
      have key : 2 / (1 - y ^ 2) - (2 + 2 * y ^ 2) = 2 * y ^ 4 / (1 - y ^ 2) := by
        field_simp
        ring
      rw [key]
      positivity
    have h0 : (0 : ℝ) ∈ Set.Icc 0 s := ⟨le_rfl, hs0⟩
    have hs : s ∈ Set.Icc 0 s := ⟨hs0, le_rfl⟩
    have hle := hmono h0 hs hs0
    have hz : F 0 = 0 := by simp [F]
    have : 0 ≤ F s := by linarith
    simpa [F] using this
  have hdiv : Real.log ((1 + s) / (1 - s)) = Real.log (1 + s) - Real.log (1 - s) :=
    Real.log_div (by linarith) (by linarith)
  rw [hdiv]
  linarith

/-- Chen's AP-switch sharp second-factor lower bound: for `2 ≤ u ≤ 4`,
`2 ((u-2)/(u+4)) + (2/3) ((u-2)/(u+4))^3 ≤ log ((u+1)/3)`. -/
theorem logPad2_L2_lower (u : ℝ) (h2 : 2 ≤ u) (h4 : u ≤ 4) :
    2 * ((u - 2) / (u + 4)) + (2 / 3 : ℝ) * ((u - 2) / (u + 4)) ^ 3
      ≤ Real.log ((u + 1) / 3) := by
  have hu4 : (0 : ℝ) < u + 4 := by linarith
  have hs0 : 0 ≤ (u - 2) / (u + 4) := by apply div_nonneg <;> linarith
  have hs1 : (u - 2) / (u + 4) ≤ 1 / 4 := by
    rw [div_le_iff₀ hu4]
    linarith
  have hcore := logPad2_L2_core ((u - 2) / (u + 4)) hs0 hs1
  have harg : (1 + (u - 2) / (u + 4)) / (1 - (u - 2) / (u + 4)) = (u + 1) / 3 := by
    field_simp
    ring
  rwa [harg] at hcore

end Work.NumberTheory.Chen.APSwitchUpper
