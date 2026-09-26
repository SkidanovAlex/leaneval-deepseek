import Mathlib
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.PCopy.Setup
import Submission.Work.Smooth.SphereJordan.PCopy.plainAnnulusSetup
import Submission.Work.Smooth.Jordan.All

/-!
# The parametrised boundary curves of the two-pccuts construction

This module contains the definitions (and elementary facts) on which the two-pccuts proof of
`Work.Smooth.SphereJordan.pcannulusInjectionTwoCutsAlt` rests: the two crosscut parametrisations, the
two half-pcannulus boundary curves `pcsrcUpB`, `pcsrcDnB`, the two target boundary curves `pctgtUpB`,
`pctgtDnB` (with the pairing flag `b` selecting the complementary pair of `γ`-arcs), and the glued
pcannulus map `pcannMap`.

It is kept import-light so that the lemmas proving the spanning properties of these curves
(`Work.SphereJordan.pcannulusSourceSpans`, `Work.SphereJordan.pcannulusTargetSpans`) can import it
without a cycle.
-/

open Set
open Classical
open scoped InnerProductSpace

namespace Work.Smooth.SphereJordan

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## The parametrised boundary arcs -/

/-- The first crosscut of the target pcannulus, parametrised from its outer endpoint `pccutDir S` to its
inner endpoint `a₁ = pcbase S + t₁ • pccutDir S` (parameter `x ∈ [0,1]`). -/
def pctgtCut₁ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ : ℝ) (x : ℝ) : ℂ :=
  (Work.Smooth.SphereJordan.pcbase S : ℂ) + ((s₁ + x * (t₁ - s₁) : ℝ) : ℂ) * pccutDir S

/-- The second crosscut, parametrised from its outer endpoint `-pccutDir S` to its inner endpoint
`a₂ = pcbase S - t₂ • pccutDir S` (parameter `x ∈ [0,1]`). -/
def pctgtCut₂ (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₂ s₂ : ℝ) (x : ℝ) : ℂ :=
  (Work.Smooth.SphereJordan.pcbase S : ℂ) - ((s₂ + x * (t₂ - s₂) : ℝ) : ℂ) * pccutDir S

/-- The upper inner semicircle of the model pcannulus, from `-(1/2) u` to `(1/2) u` through
`(1/2) I u`: the inner boundary arc of the upper half of the model pcannulus. -/
def pcsrcInnerUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * pccutDir S * Complex.exp (((Real.pi * (1 - x) : ℝ) : ℂ) * Complex.I)

/-- The lower inner semicircle, from `(1/2) u` to `-(1/2) u` through `-(1/2) I u`. -/
def pcsrcInnerDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * pccutDir S * Complex.exp (((-(Real.pi * x) : ℝ) : ℂ) * Complex.I)

/-- The upper outer semicircle, from `u` to `-u` through `I u`. -/
def pcsrcOuterUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  pccutDir S * Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The lower outer semicircle, from `-u` to `u` through `-I u`. -/
def pcsrcOuterDn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) : ℂ :=
  -pccutDir S * Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- **The two crosscuts meet the boundary circle at the points `pccutDir S` and `-pccutDir S`.** -/
theorem pccut_outer_eq (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) {s₁ s₂ : ℝ} (hs₁0 : 0 < s₁) (hs₂0 : 0 < s₂)
    (hs₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S ∈ Metric.sphere (0 : ℂ) 1)
    (hs₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S ∈ Metric.sphere (0 : ℂ) 1) :
    (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S = pccutDir S ∧
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S = -pccutDir S := by
  have hb : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ < 1 := pcnorm_base_lt_one S hball
  have hb' : ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ : ℝ) : ℂ) * pccutDir S =
      (Work.Smooth.SphereJordan.pcbase S : ℂ) := (pcbase_eq_smul_cutDir S).symm
  have h1 : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S =
      (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + s₁ : ℝ)) : ℂ) * pccutDir S := by
    calc (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) * pccutDir S
        = ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ : ℝ) : ℂ) * pccutDir S +
            (s₁ : ℂ) * pccutDir S := by rw [hb']
      _ = (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + s₁ : ℝ)) : ℂ) * pccutDir S := by
            push_cast; ring
  have h2 : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S =
      (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - s₂ : ℝ)) : ℂ) * pccutDir S := by
    calc (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) * pccutDir S
        = ((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ : ℝ) : ℂ) * pccutDir S -
            (s₂ : ℂ) * pccutDir S := by rw [hb']
      _ = (((‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - s₂ : ℝ)) : ℂ) * pccutDir S := by
            push_cast; ring
  have e1 : |‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + s₁| = 1 := by
    have h := (pcmem_sphere_one_iff _).mp hs₁
    rw [h1, norm_mul, pcnorm_cutDir S, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have e2 : |‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - s₂| = 1 := by
    have h := (pcmem_sphere_one_iff _).mp hs₂
    rw [h2, norm_mul, pcnorm_cutDir S, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hp1 : 0 < ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + s₁ := by
    have := norm_nonneg (Work.Smooth.SphereJordan.pcbase S : ℂ); linarith
  constructor
  · have h : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ + s₁ = 1 := by
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp e1 with h | h
      · exact h
      · exfalso; linarith
    rw [h1, h, Complex.ofReal_one, one_mul]
  · have h : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ - s₂ = -1 := by
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp e2 with h | h
      · exfalso; linarith
      · exact h
    rw [h2, h]
    push_cast
    ring

/-! ## The four boundary curves, as `2π`-periodic functions of the parameter -/

/-- The "one period" parameter of a real number: the representative in `[0, 2π)`. -/
def pcperPt (τ : ℝ) : ℝ := τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)

theorem pcperPt_shift (τ : ℝ) : pcperPt (τ + 2 * Real.pi) = pcperPt τ := by
  have h : ⌊(τ + 2 * Real.pi) / (2 * Real.pi)⌋ = ⌊τ / (2 * Real.pi)⌋ + 1 := by
    rw [add_div, div_self (by positivity : (2 * Real.pi) ≠ 0)]
    exact Int.floor_add_one _
  rw [pcperPt, pcperPt, h]
  push_cast
  ring

/-- The boundary curve of the **upper half of the model pcannulus** `{1/2 ≤ ‖z‖ ≤ 1, 0 ≤ Im (z/u)}`:
outer semicircle, inward radial segment, upper inner semicircle, outward radial segment. -/
def pcsrcUpB (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (τ : ℝ) : ℂ :=
  let σ := pcperPt τ
  if σ ≤ Real.pi / 2 then pcsrcOuterUp S (σ / (Real.pi / 2))
  else if σ ≤ Real.pi then (-1 + (σ - Real.pi / 2) / (Real.pi / 2) / 2) • pccutDir S
  else if σ ≤ 3 * Real.pi / 2 then pcsrcInnerUp S ((σ - Real.pi) / (Real.pi / 2))
  else (1 / 2 + (σ - 3 * Real.pi / 2) / (Real.pi / 2) / 2) • pccutDir S

/-- The boundary curve of the **lower half of the model pcannulus**. -/
def pcsrcDnB (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (τ : ℝ) : ℂ :=
  let σ := pcperPt τ
  if σ ≤ Real.pi / 2 then pcsrcOuterDn S (σ / (Real.pi / 2))
  else if σ ≤ Real.pi then (1 - (σ - Real.pi / 2) / (Real.pi / 2) / 2) • pccutDir S
  else if σ ≤ 3 * Real.pi / 2 then pcsrcInnerDn S ((σ - Real.pi) / (Real.pi / 2))
  else (-(1 / 2) - (σ - 3 * Real.pi / 2) / (Real.pi / 2) / 2) • pccutDir S

/-- The target boundary curve of the **upper piece**: upper outer semicircle, the second crosscut
inward, the inner `γ`-arc (the pair selected by `b`), the first crosscut outward. -/
def pctgtUpB (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ) (τ : ℝ) : ℂ :=
  let σ := pcperPt τ
  if σ ≤ Real.pi / 2 then pcsrcOuterUp S (σ / (Real.pi / 2))
  else if σ ≤ Real.pi then pctgtCut₂ S t₂ s₂ ((σ - Real.pi / 2) / (Real.pi / 2))
  else if σ ≤ 3 * Real.pi / 2 then
    (if b then γ.γ (θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂))
     else γ.γ (θ₂ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₁ - θ₂ - 2 * Real.pi)))
  else pctgtCut₁ S t₁ s₁ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2))

/-- The target boundary curve of the **lower piece**: lower outer semicircle, the first crosscut
inward, the inner `γ`-arc (the complementary pair), the second crosscut outward. -/
def pctgtDnB (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (t₁ s₁ t₂ s₂ : ℝ) (b : Bool)
    (θ₁ θ₂ : ℝ) (τ : ℝ) : ℂ :=
  let σ := pcperPt τ
  if σ ≤ Real.pi / 2 then pcsrcOuterDn S (σ / (Real.pi / 2))
  else if σ ≤ Real.pi then pctgtCut₁ S t₁ s₁ ((σ - Real.pi / 2) / (Real.pi / 2))
  else if σ ≤ 3 * Real.pi / 2 then
    (if b then γ.γ (θ₁ - 2 * Real.pi + ((σ - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁ + 2 * Real.pi))
     else γ.γ (θ₁ + ((σ - Real.pi) / (Real.pi / 2)) * (θ₂ - θ₁)))
  else pctgtCut₂ S t₂ s₂ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2))

/-! ## The glued pcannulus map -/

/-- The "relative imaginary part" of a point of the model disc, with respect to the diameter
through the pcbase point: `0 ≤ pcrelIm` selects the upper half of the pcannulus. -/
def pcrelIm (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (z : Work.Smooth.SphereJordan.Disc) : ℝ :=
  ((z : ℂ) / pccutDir S).im

/-- The inverse of an injective boundary parametrisation, as a partial map given by choice. -/
def pcinvOf {Ψ : C(Work.Smooth.SphereJordan.Disc, ℂ)} (hΨ : Function.Injective Ψ) (x : ℂ) :
    Work.Smooth.SphereJordan.Disc :=
  if h : ∃ w : Work.Smooth.SphereJordan.Disc, Ψ w = x then h.choose else 0

theorem pcinvOf_spec {Ψ : C(Work.Smooth.SphereJordan.Disc, ℂ)} (hΨ : Function.Injective Ψ)
    {x : ℂ} (hx : ∃ w : Work.Smooth.SphereJordan.Disc, Ψ w = x) : Ψ (pcinvOf hΨ x) = x := by
  unfold pcinvOf
  rw [dif_pos hx]
  exact hx.choose_spec

/-- **The map of the pcannulus `1/2 ≤ ‖z‖ ≤ 1`**: on the upper (resp. lower) half it is the
target-side spanning disc read through the inverse of the source-side spanning disc. -/
def pcannMap (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (Φ_up Φ_dn : C(Work.Smooth.SphereJordan.Disc, ℂ))
    (Ψ_up Ψ_dn : C(Work.Smooth.SphereJordan.Disc, ℂ))
    (hΨup : Function.Injective Ψ_up) (hΨdn : Function.Injective Ψ_dn)
    (z : Work.Smooth.SphereJordan.Disc) : ℂ :=
  if 0 ≤ pcrelIm S z then Φ_up (pcinvOf hΨup (z : ℂ)) else Φ_dn (pcinvOf hΨdn (z : ℂ))

end
end Work.Smooth.SphereJordan
