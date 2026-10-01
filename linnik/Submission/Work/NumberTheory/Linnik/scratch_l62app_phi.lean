import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l52phi_imprim
import Submission.Commons.NumberTheory.Linnik.windowSum_nonneg_nonPrincipal
import Submission.Commons.NumberTheory.Linnik.le_windowSum_of_mem

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.Linnik

/-- The key hypothesis of the parametric Lemma 5.2 for the primitive character `χ*`, in the shape
produced by Lemma 3.1 (with `φ = 1/3` and slack `ε/4`). -/
def L52Hyp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (c ε δ : ℝ) : Prop :=
  ∀ s : ℂ, 1 + 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) ≤ s.re →
      s.re ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
      |s.im| ≤ 10 * Real.log (q : ℝ) →
    (-logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re
      + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
          (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
      ≤ (c + ε/4) * Real.log (q : ℝ)

/-- **(6.5)/(6.6)**: if every zero of the completed `L`-function of the primitive character
inducing `χ` that lies in the window `|1 + i·Im s - u| ≤ δ` is to the left of `s`, then the
window sum is nonnegative and Lemma 5.2 gives a bound with no window term. -/
theorem Ksum_le_self_of_L52_phi (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hF : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hχ : χ ≠ 1) {s : ℂ},
        |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        |s.im| ≤ 10 * Real.log (q : ℝ) →
        1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ≤ s.re →
        L52Hyp χ c ε δ →
        (∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
            ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re) →
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log q))
          ≤ f 0 * (c + ε) * Real.log q := by
  intro f hcont hsupp hf2 hBnd hf0 hF ε hε δ hδ0 hδ1
  obtain ⟨q₀, hq₀⟩ := (lemma5_2_of_logDeriv_bound_phi_imprim x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨q₀, ?_⟩
  intro q _inst hq χ _instc hχ s hsre hsim hs1 hH hzw
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
  have hwin := windowSum_nonneg_nonPrincipal χ.primitiveCharacter hχ' hLnn hF hzw
  have hkey : -(Real.log q) * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (Real.log q)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) else 0))
      ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith only [hLnn]) hwin
  linarith only [hsum, hkey]

/-- **(6.7)/(6.8)**: if `ρ` is a zero of the completed `L`-function of the primitive character
inducing `χ` lying in the window and every other window zero is to the left of `s`, Lemma 5.2
combined with the single-term lower bound for the window sum gives
`K(s,χ) ≤ -L·Re F((s-ρ)L) + f(0)(1/6+ε)L`. -/
theorem Ksum_le_single_of_L52_phi (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
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
        L52Hyp χ c ε δ →
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) ρ ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - ρ‖ ≤ δ →
        (∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
            ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re) →
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
            ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / Real.log q))
          ≤ -(Real.log q) * ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * (Real.log q)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
            + f 0 * (c + ε) * Real.log q := by
  intro f hcont hsupp hf2 hBnd hf0 hF ε hε δ hδ0 hδ1
  obtain ⟨q₀, hq₀⟩ := (lemma5_2_of_logDeriv_bound_phi_imprim x₀ B c hx₀ hB)
    hcont hsupp hf2 hBnd hf0 hε hδ0 hδ1
  refine ⟨q₀, ?_⟩
  intro q _inst hq χ _instc hχ s ρ hsre hsim hs1 hH hdiv hwin hzw
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
  have hsingle := le_windowSum_of_mem χ.primitiveCharacter hχ' hLnn hF hdiv hwin hzw
  have hkey : -(Real.log q) * (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter) (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
      (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then
        ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (Real.log q)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) else 0))
      ≤ -(Real.log q) * ((∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - ρ) * (Real.log q)) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re) :=
    mul_le_mul_of_nonpos_left hsingle (by linarith only [hLnn])
  linarith only [hsum, hkey]

end Commons.NumberTheory.Linnik
