/-
# Elementary auxiliary computations for `ratioZeroL1fixed`

The triangle-weighted sum `S(x) = Σ_{n ≤ x} λ(n) n^{-β} (1 - n/x)` (see `RatioDefs`) is the
finite Abel transform of the summatory function `A`, with weights
`W(u) = (1-β) u^{-β}/x + β u^{-(β+1)}`.  This file records the two elementary facts about `W`
that the assembly of the main theorem needs:

* `integral_abel_weights`: the exact value of `∫_1^x W(u) u du`, which produces the "main term"
  `x^{1-β}/((1-β)(2-β))` together with the two corrections `-β/(1-β)` and `-(1-β)/(x(2-β))`;
* `smoothed_main_split`, the algebraic rearrangement used to compare `S(x)` with the main term.
-/
import Mathlib
import Submission.Work.LinnikAreas.RatioDefs

namespace Work.LinnikAreas

open MeasureTheory intervalIntegral Set
open scoped BigOperators
noncomputable section

/-- The exact value of the weight integral `∫_1^x ((1-β)u^{-β}/x + βu^{-(β+1)}) u du`. -/
lemma integral_abel_weights (β : ℝ) (hβ : β < 1) {x : ℝ} (hx : 0 < x) :
    ∫ u in (1:ℝ)..x, (((1-β) : ℝ) * u ^ (-β) / x + β * u ^ (-(β+1))) * u
      = x ^ (1-β)/((1-β)*(2-β)) - β/(1-β) - (1-β)/(x*(2-β)) := by
  have hp : ∀ u ∈ uIcc (1:ℝ) x, 0 < u := by
    intro u hu
    rcases (mem_uIcc.mp hu) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hpt : ∀ u ∈ uIcc (1:ℝ) x,
      (((1-β) : ℝ) * u ^ (-β) / x + β * u ^ (-(β+1))) * u
        = ((1-β)/x) * u ^ (1-β) + β * u ^ (-β) := by
    intro u hu
    have h0 : (0:ℝ) < u := hp u hu
    have A1 : u ^ (-β) * u = u ^ (1-β) := by
      calc u ^ (-β) * u = u ^ (-β) * u ^ (1:ℝ) := by rw [Real.rpow_one]
        _ = u ^ (-β + 1) := (Real.rpow_add h0 (-β) 1).symm
        _ = u ^ (1-β) := by congr 1; ring
    have A2 : u ^ (-(β+1)) * u = u ^ (-β) := by
      calc u ^ (-(β+1)) * u = u ^ (-(β+1)) * u ^ (1:ℝ) := by rw [Real.rpow_one]
        _ = u ^ (-(β+1) + 1) := (Real.rpow_add h0 (-(β+1)) 1).symm
        _ = u ^ (-β) := by congr 1; ring
    rw [show (((1-β) : ℝ) * u ^ (-β) / x + β * u ^ (-(β+1))) * u
          = ((1-β) * (u ^ (-β) * u)) / x + β * (u ^ (-(β+1)) * u) by ring,
      A1, A2]
    ring
  rw [integral_congr hpt]
  have hcont1 : ContinuousOn (fun u : ℝ => u ^ (1-β)) (uIcc (1:ℝ) x) :=
    continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt (hp u hu)))
  have hcont2 : ContinuousOn (fun u : ℝ => u ^ (-β)) (uIcc (1:ℝ) x) :=
    continuousOn_id.rpow_const (fun u hu => Or.inl (ne_of_gt (hp u hu)))
  rw [intervalIntegral.integral_add (hcont1.const_mul _).intervalIntegrable
      (hcont2.const_mul _).intervalIntegrable]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_rpow (Or.inl (by linarith : (-1:ℝ) < 1 - β)),
      integral_rpow (Or.inl (by linarith : (-1:ℝ) < -β))]
  rw [show x ^ (1 - β + 1) = x * x ^ (1-β) by
        rw [show (1:ℝ) - β + 1 = 1 + (1-β) by ring, Real.rpow_add hx, Real.rpow_one],
      show x ^ (-β + 1) = x ^ (1-β) by congr 1; ring,
      Real.one_rpow, Real.one_rpow]
  rw [show (1:ℝ) - β + 1 = 2 - β by ring, show -β + 1 = 1 - β by ring]
  have h1 : (1:ℝ)-β ≠ 0 := by linarith
  have h2 : (2:ℝ)-β ≠ 0 := by linarith
  have h3 : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

/-- The same identity, in the complex form needed for the complex-valued integral coming from
`smoothedAbel`. -/
lemma integral_abel_weights_complex (β : ℝ) (hβ : β < 1) {x : ℝ} (hx : 0 < x) :
    ∫ u in (1:ℝ)..x, ((((1-β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ)
        + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1))) * (u:ℂ))
      = (x:ℂ) ^ ((1-β:ℝ):ℂ)/(((1-β:ℝ):ℂ)*((2-β:ℝ):ℂ)) - (β:ℂ)/((1-β:ℝ):ℂ)
        - ((1-β:ℝ):ℂ)/((x:ℂ)*((2-β:ℝ):ℂ)) := by
  have hp : ∀ u ∈ uIcc (1:ℝ) x, 0 < u := by
    intro u hu
    rcases (mem_uIcc.mp hu) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hpt : ∀ u ∈ uIcc (1:ℝ) x,
      ((((1-β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1))) * (u:ℂ))
        = (((((1-β) : ℝ) * u ^ (-β) / x + β * u ^ (-(β+1))) * u : ℝ) : ℂ) := by
    intro u hu
    have h0 : (0:ℝ) < u := hp u hu
    push_cast
    rw [Complex.ofReal_cpow h0.le, Complex.ofReal_cpow h0.le]
    push_cast
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_ofReal,
    integral_abel_weights β hβ hx]
  have h1 : (1:ℝ)-β ≠ 0 := by linarith
  have h2 : (2:ℝ)-β ≠ 0 := by linarith
  have h3 : x ≠ 0 := ne_of_gt hx
  push_cast
  rw [Complex.ofReal_cpow hx.le]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  try field_simp


end
end Work.LinnikAreas
