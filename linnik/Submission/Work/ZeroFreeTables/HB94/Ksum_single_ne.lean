import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Commons.NumberTheory.Linnik.le_windowSum_of_mem_ne

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.ZeroFreeTables.HB94

/-!
# HB (6.7) with the retained zero to the *right* of the base point

`Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi` (HB's (6.8)) requires every window zero
— including the retained one `ρ` — to satisfy `Re u ≤ Re s`.  In this file we remove that
requirement for `ρ` itself, at the cost of the extra hypothesis that the retained integral is
non-negative (HB's (6.7): "since `ρ₁` falls in this set, `Σ ≥ F(0)`"), using
`Commons.NumberTheory.Linnik.le_windowSum_of_mem_ne`.  This is exactly what HB's §9 argument for
`h ≥ 6` needs, where the base point `β = 1 - λ*/𝓛` lies to the *left* of the retained zero.
-/

/-- **(6.7)/(6.8) with a retained zero to the right of `s`.**  If `ρ` is a zero of the completed
`L`-function of the primitive character inducing `χ` lying in the window, if the integral over `ρ`
is non-negative, and if every *other* window zero is to the left of `s`, then
`K(s,χ) ≤ -𝓛·Re F((s-ρ)𝓛) + f(0)(c+ε)𝓛`. -/
theorem Ksum_le_single_of_L52_phi_ne (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hF : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1) {s ρ : ℂ},
        |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        |s.im| ≤ 10 * Real.log (q : ℝ) →
        1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ s.re →
        Commons.NumberTheory.Linnik.L52Hyp χ c ε δ →
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ →
        0 ≤ (∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - ρ) * (Real.log q)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re →
        (∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
            ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ ρ → u.re ≤ s.re) →
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log q))
          ≤ -(Real.log q) * ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * (Real.log q)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
            + f 0 * (c + ε) * Real.log q := by
  intro f hcont hsupp hf2 hBnd hf0 hF ε hε δ hδ0 hδ1
  obtain ⟨q₀, hq₀⟩ :=
    (Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim x₀ B c hx₀ hB)
      hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨q₀, ?_⟩
  intro q _inst hq χ _instc hχ s ρ hsre hsim hs1 hH hdiv hwin hρnn hzw
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hLnn : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg (by
    have h1 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast h1)
  have hHraw : ∀ s : ℂ, 1 + 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) ≤ s.re →
      s.re ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
      |s.im| ≤ 10 * Real.log (q : ℝ) →
    (-logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re
      + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
          (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
      ≤ (c + ε/4) * Real.log (q : ℝ) := hH
  have hsum := hq₀ hq χ hχ hHraw s hsre hsim hs1
  have hsingle := Commons.NumberTheory.Linnik.le_windowSum_of_mem_ne χ.primitiveCharacter hχ'
    hLnn hF hdiv hwin hρnn hzw
  have hkey : -(Real.log q) * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (Real.log q)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) else 0))
      ≤ -(Real.log q) * ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * (Real.log q)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) :=
    mul_le_mul_of_nonpos_left hsingle (by linarith only [hLnn])
  linarith only [hsum, hkey]

end Work.ZeroFreeTables.HB94
