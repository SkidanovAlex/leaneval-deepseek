import Mathlib
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.annulus_of_planeHypothesis
import Submission.Work.Smooth.SphereJordan.plainAnnulusSetup
import Submission.Work.Smooth.Jordan.All

/-!
# The parametrised boundary curves of the two-cuts construction

This module contains the definitions (and elementary facts) on which the two-cuts proof of
`Work.Smooth.SphereJordan.annulusInjectionTwoCutsAlt` rests: the two crosscut parametrisations, the
two half-annulus boundary curves `srcUpB`, `srcDnB`, the two target boundary curves `tgtUpB`,
`tgtDnB` (with the pairing flag `b` selecting the complementary pair of `γ`-arcs), and the glued
annulus map `annMap`.

It is kept import-light so that the lemmas proving the spanning properties of these curves
(`Work.SphereJordan.annulusSourceSpans`, `Work.SphereJordan.annulusTargetSpans`) can import it
without a cycle.
-/

open Set
open Classical
open scoped InnerProductSpace

namespace Work.Smooth.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## The parametrised boundary arcs -/

/-- The first crosscut of the target annulus, parametrised from its outer endpoint `cutDir S` to its
inner endpoint `a₁ = base S + t₁ • cutDir S` (parameter `x ∈ [0,1]`). -/
def tgtCut₁ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ : ℝ) (x : ℝ) : ℂ :=
  (Work.Smooth.SphereJordan.base S : ℂ) + ((s₁ + x * (t₁ - s₁) : ℝ) : ℂ) * cutDir S

/-- The second crosscut, parametrised from its outer endpoint `-cutDir S` to its inner endpoint
`a₂ = base S - t₂ • cutDir S` (parameter `x ∈ [0,1]`). -/
def tgtCut₂ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ s₂ : ℝ) (x : ℝ) : ℂ :=
  (Work.Smooth.SphereJordan.base S : ℂ) - ((s₂ + x * (t₂ - s₂) : ℝ) : ℂ) * cutDir S

/-- The upper inner semicircle of the model annulus, from `-(1/2) u` to `(1/2) u` through
`(1/2) I u`: the inner boundary arc of the upper half of the model annulus. -/
def srcInnerUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * cutDir S * Complex.exp (((Real.pi * (1 - x) : ℝ) : ℂ) * Complex.I)

/-- The lower inner semicircle, from `(1/2) u` to `-(1/2) u` through `-(1/2) I u`. -/
def srcInnerDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * cutDir S * Complex.exp (((-(Real.pi * x) : ℝ) : ℂ) * Complex.I)

/-- The upper outer semicircle, from `u` to `-u` through `I u`. -/
def srcOuterUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  cutDir S * Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The lower outer semicircle, from `-u` to `u` through `-I u`. -/
def srcOuterDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  -cutDir S * Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- **The two crosscuts meet the boundary circle at the points `cutDir S` and `-cutDir S`.** -/
theorem cut_outer_eq (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {s₁ s₂ : ℝ} (hs₁0 : 0 < s₁) (hs₂0 : 0 < s₂)
    (hs₁ : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) * cutDir S ∈ Metric.sphere (0 : ℂ) 1)
    (hs₂ : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) * cutDir S ∈ Metric.sphere (0 : ℂ) 1) :
    (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) * cutDir S = cutDir S ∧
      (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) * cutDir S = -cutDir S := by
  have hb : ‖(Work.Smooth.SphereJordan.base S : ℂ)‖ < 1 := norm_base_lt_one S hball
  have hb' : ((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ : ℝ) : ℂ) * cutDir S =
      (Work.Smooth.SphereJordan.base S : ℂ) := (base_eq_smul_cutDir S).symm
  have h1 : (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) * cutDir S =
      (((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ + s₁ : ℝ)) : ℂ) * cutDir S := by
    calc (Work.Smooth.SphereJordan.base S : ℂ) + (s₁ : ℂ) * cutDir S
        = ((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ : ℝ) : ℂ) * cutDir S +
            (s₁ : ℂ) * cutDir S := by rw [hb']
      _ = (((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ + s₁ : ℝ)) : ℂ) * cutDir S := by
            push_cast; ring
  have h2 : (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) * cutDir S =
      (((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ - s₂ : ℝ)) : ℂ) * cutDir S := by
    calc (Work.Smooth.SphereJordan.base S : ℂ) - (s₂ : ℂ) * cutDir S
        = ((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ : ℝ) : ℂ) * cutDir S -
            (s₂ : ℂ) * cutDir S := by rw [hb']
      _ = (((‖(Work.Smooth.SphereJordan.base S : ℂ)‖ - s₂ : ℝ)) : ℂ) * cutDir S := by
            push_cast; ring
  have e1 : |‖(Work.Smooth.SphereJordan.base S : ℂ)‖ + s₁| = 1 := by
    have h := (mem_sphere_one_iff _).mp hs₁
    rw [h1, norm_mul, norm_cutDir S, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have e2 : |‖(Work.Smooth.SphereJordan.base S : ℂ)‖ - s₂| = 1 := by
    have h := (mem_sphere_one_iff _).mp hs₂
    rw [h2, norm_mul, norm_cutDir S, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hp1 : 0 < ‖(Work.Smooth.SphereJordan.base S : ℂ)‖ + s₁ := by
    have := norm_nonneg (Work.Smooth.SphereJordan.base S : ℂ); linarith
  constructor
  · have h : ‖(Work.Smooth.SphereJordan.base S : ℂ)‖ + s₁ = 1 := by
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp e1 with h | h
      · exact h
      · exfalso; linarith
    rw [h1, h, Complex.ofReal_one, one_mul]
  · have h : ‖(Work.Smooth.SphereJordan.base S : ℂ)‖ - s₂ = -1 := by
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp e2 with h | h
      · exfalso; linarith
      · exact h
    rw [h2, h]
    push_cast
    ring

/-! ## The four boundary curves, as `2π`-periodic functions of the parameter -/

/-- The "one period" parameter of a real number: the representative in `[0, 2π)`. -/
def perPt (τ : ℝ) : ℝ := τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)

theorem perPt_shift (τ : ℝ) : perPt (τ + 2 * Real.pi) = perPt τ := by
  have h : ⌊(τ + 2 * Real.pi) / (2 * Real.pi)⌋ = ⌊τ / (2 * Real.pi)⌋ + 1 := by
    rw [add_div, div_self (by positivity : (2 * Real.pi) ≠ 0)]
    exact Int.floor_add_one _
  rw [perPt, perPt, h]
  push_cast
  ring

/-- The boundary curve of the **upper half of the model annulus** `{1/2 ≤ ‖z‖ ≤ 1, 0 ≤ Im (z/u)}`:
outer semicircle, inward radial segment, upper inner semicircle, outward radial segment. -/
def srcUpB (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (τ : ℝ) : ℂ :=
  let σ := perPt τ
  if σ ≤ Real.pi / 2 then srcOuterUp S (σ / (Real.pi / 2))
  else if σ ≤ Real.pi then (-1 + (σ - Real.pi / 2) / (Real.pi / 2) / 2) • cutDir S
  else if σ ≤ 3 * Real.pi / 2 then srcInnerUp S ((σ - Real.pi) / (Real.pi / 2))
  else (1 / 2 + (σ - 3 * Real.pi / 2) / (Real.pi / 2) / 2) • cutDir S

/-- The boundary curve of the **lower half of the model annulus**. -/
def srcDnB (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (τ : ℝ) : ℂ :=
  let σ := perPt τ
  if σ ≤ Real.pi / 2 then srcOuterDn S (σ / (Real.pi / 2))
  else if σ ≤ Real.pi then (1 - (σ - Real.pi / 2) / (Real.pi / 2) / 2) • cutDir S
  else if σ ≤ 3 * Real.pi / 2 then srcInnerDn S ((σ - Real.pi) / (Real.pi / 2))
  else (-(1 / 2) - (σ - 3 * Real.pi / 2) / (Real.pi / 2) / 2) • cutDir S

/-- The target boundary curve of the **upper piece**: upper outer semicircle, the second crosscut
inward, the inner `γ`-arc (the pair selected by `b`), the first crosscut outward. -/
def tgtUpB (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ) (τ : ℝ) : ℂ :=
  let σ := perPt τ
  if σ ≤ Real.pi / 2 then srcOuterUp S (σ / (Real.pi / 2))
  else if σ ≤ Real.pi then tgtCut₂ S t₂ s₂ ((σ - Real.pi / 2) / (Real.pi / 2))
  else if σ ≤ 3 * Real.pi / 2 then
    (if b then γ.γ (θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂))
     else γ.γ (θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂ - 2 * Real.pi)))
  else tgtCut₁ S t₁ s₁ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2))

/-- The target boundary curve of the **lower piece**: lower outer semicircle, the first crosscut
inward, the inner `γ`-arc (the complementary pair), the second crosscut outward. -/
def tgtDnB (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ) (τ : ℝ) : ℂ :=
  let σ := perPt τ
  if σ ≤ Real.pi / 2 then srcOuterDn S (σ / (Real.pi / 2))
  else if σ ≤ Real.pi then tgtCut₁ S t₁ s₁ ((σ - Real.pi / 2) / (Real.pi / 2))
  else if σ ≤ 3 * Real.pi / 2 then
    (if b then γ.γ (θ₁ - 2 * Real.pi + ((σ - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁ + 2 * Real.pi))
     else γ.γ (θ₁ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁)))
  else tgtCut₂ S t₂ s₂ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2))

/-! ## The glued annulus map -/

/-- The "relative imaginary part" of a point of the model disc, with respect to the diameter
through the base point: `0 ≤ relIm` selects the upper half of the annulus. -/
def relIm (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (z : Work.Smooth.SphereJordan.Disc) : ℝ :=
  ((z : ℂ) / cutDir S).im

/-- The inverse of an injective boundary parametrisation, as a partial map given by choice. -/
def invOf {Ψ : C(Work.Smooth.SphereJordan.Disc, ℂ)} (hΨ : Function.Injective Ψ) (x : ℂ) :
    Work.Smooth.SphereJordan.Disc :=
  if h : ∃ w : Work.Smooth.SphereJordan.Disc, Ψ w = x then h.choose else 0

theorem invOf_spec {Ψ : C(Work.Smooth.SphereJordan.Disc, ℂ)} (hΨ : Function.Injective Ψ)
    {x : ℂ} (hx : ∃ w : Work.Smooth.SphereJordan.Disc, Ψ w = x) : Ψ (invOf hΨ x) = x := by
  unfold invOf
  rw [dif_pos hx]
  exact hx.choose_spec

/-- **The map of the annulus `1/2 ≤ ‖z‖ ≤ 1`**: on the upper (resp. lower) half it is the
target-side spanning disc read through the inverse of the source-side spanning disc. -/
def annMap (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (Φ_up Φ_dn : C(Work.Smooth.SphereJordan.Disc, ℂ))
    (Ψ_up Ψ_dn : C(Work.Smooth.SphereJordan.Disc, ℂ))
    (hΨup : Function.Injective Ψ_up) (hΨdn : Function.Injective Ψ_dn)
    (z : Work.Smooth.SphereJordan.Disc) : ℂ :=
  if 0 ≤ relIm S z then Φ_up (invOf hΨup (z : ℂ)) else Φ_dn (invOf hΨdn (z : ℂ))

end
end Work.Smooth.SphereJordan
