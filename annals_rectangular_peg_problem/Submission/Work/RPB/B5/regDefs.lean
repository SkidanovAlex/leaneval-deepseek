import Mathlib

/-!
# B5: the regularised phase integrand

This file sets up the objects used to prove `Work.RPB.B5.regularizedPhaseIntegrand`.

Given a smooth, even-in-`r` family `hc : ℝ → ℝ → ℝ → ℂ`, we want a smooth function `g` which
is odd in `s` and which on the strip `τ ∈ [0,1]`, `|s| < ρa` agrees with the "phase derivative"
`Complex.im (deriv (fun u => hc τ t u) s / hc τ t s)`.

The (only) obstruction to reading off `g` directly from `Im (hc'/hc)` is that `hc` is only known
to be non-vanishing on `τ ∈ [0,1]`, `|s| < δ`; outside that region `hc` may vanish and `hc'/hc`
may blow up.  We therefore *regularise the denominator*: replace `|hc|²` by `|hc|² + κ` where
`κ ≥ 0` is a smooth bump which vanishes exactly on `τ ∈ [0,1]`, `|s| ≤ ρa` (chosen with
`ρa < ρb < δ`).  On that closed set the regularised integrand still equals `Im (hc'/hc)`, while
the denominator is everywhere positive, so the expression is smooth on all of `ℝ³`.

The regularised integrand is
`regF hc ρa τ t s = (Im(∂₃ hc)·Re(hc) - Re(∂₃ hc)·Im(hc)) / (|hc|² + κ(τ,s))`,
which is automatically odd in `s` because `hc` is even in `s`.

## Contents

* `phaseBumpT`, `phaseBumpS`, `phaseBumpK`: the smooth non-negative bumps with zero sets
  `[0,1]`, `[-ρa,ρa]` and `[0,1] × [-ρa,ρa]`;
* `pds`: the partial derivative `∂₃ hc`, written via `fderiv` so that its smoothness is automatic;
* `regDen`, `regNum`, `regF`: the regularised denominator, numerator and integrand.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- A smooth non-negative bump whose zero set is exactly `[0,1]`:
`τ ↦ smoothTransition (-τ) + smoothTransition (τ - 1)`. -/
def phaseBumpT (τ : ℝ) : ℝ :=
  Real.smoothTransition (-τ) + Real.smoothTransition (τ - 1)

/-- A smooth non-negative bump whose zero set is exactly `[-ρa, ρa]`:
`s ↦ smoothTransition (-(s+ρa)) + smoothTransition (s-ρa)`. -/
def phaseBumpS (ρa s : ℝ) : ℝ :=
  Real.smoothTransition (-(s + ρa)) + Real.smoothTransition (s - ρa)

/-- The regularising weight `κ(τ,s) = phaseBumpT τ + phaseBumpS ρa s`, a smooth non-negative
function whose zero set is exactly `[0,1] × [-ρa,ρa]`. -/
def phaseBumpK (ρa τ s : ℝ) : ℝ :=
  phaseBumpT τ + phaseBumpS ρa s

/-- The partial derivative `∂₃ hc` of `hc` in its third argument, written through `fderiv` so that
its joint smoothness is immediate. -/
def pds (hc : ℝ → ℝ → ℝ → ℂ) (τ t s : ℝ) : ℂ :=
  (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => hc z.1 z.2.1 z.2.2) (τ, (t, s)))
    ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))

/-- The regularised denominator `|hc(τ,t,s)|² + κ(τ,s)`. -/
def regDen (hc : ℝ → ℝ → ℝ → ℂ) (ρa : ℝ) (τ t s : ℝ) : ℝ :=
  (hc τ t s).re * (hc τ t s).re + (hc τ t s).im * (hc τ t s).im + phaseBumpK ρa τ s

/-- The numerator `Im(∂₃ hc)·Re(hc) - Re(∂₃ hc)·Im(hc)`; this is
`Im(∂₃ hc · conj hc)` and, where `hc ≠ 0`, equals `Im(∂₃hc/hc) · |hc|²`. -/
def regNum (hc : ℝ → ℝ → ℝ → ℂ) (τ t s : ℝ) : ℝ :=
  (pds hc τ t s).im * (hc τ t s).re - (pds hc τ t s).re * (hc τ t s).im

/-- The regularised phase integrand. -/
def regF (hc : ℝ → ℝ → ℝ → ℂ) (ρa : ℝ) (τ t s : ℝ) : ℝ :=
  regNum hc τ t s / regDen hc ρa τ t s

/-! ### Elementary properties of the bumps -/

lemma phaseBumpT_nonneg (τ : ℝ) : 0 ≤ phaseBumpT τ := by
  unfold phaseBumpT
  have a := Real.smoothTransition.nonneg (-τ)
  have b := Real.smoothTransition.nonneg (τ - 1)
  linarith

lemma phaseBumpS_nonneg (ρa s : ℝ) : 0 ≤ phaseBumpS ρa s := by
  unfold phaseBumpS
  have a := Real.smoothTransition.nonneg (-(s + ρa))
  have b := Real.smoothTransition.nonneg (s - ρa)
  linarith

lemma phaseBumpK_nonneg (ρa τ s : ℝ) : 0 ≤ phaseBumpK ρa τ s := by
  unfold phaseBumpK
  have a := phaseBumpT_nonneg τ
  have b := phaseBumpS_nonneg ρa s
  linarith

lemma phaseBumpT_eq_zero_iff (τ : ℝ) : phaseBumpT τ = 0 ↔ τ ∈ Set.Icc (0 : ℝ) 1 := by
  unfold phaseBumpT
  rw [Set.mem_Icc]
  constructor
  · intro h
    have a := Real.smoothTransition.nonneg (-τ)
    have b := Real.smoothTransition.nonneg (τ - 1)
    have h1 : Real.smoothTransition (-τ) = 0 := by linarith
    have h2 : Real.smoothTransition (τ - 1) = 0 := by linarith
    rw [Real.smoothTransition.zero_iff_nonpos] at h1 h2
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : -τ ≤ 0),
      Real.smoothTransition.zero_of_nonpos (by linarith : τ - 1 ≤ 0)]
    ring

lemma phaseBumpS_eq_zero_iff (ρa s : ℝ) : phaseBumpS ρa s = 0 ↔ |s| ≤ ρa := by
  unfold phaseBumpS
  constructor
  · intro h
    have a := Real.smoothTransition.nonneg (-(s + ρa))
    have b := Real.smoothTransition.nonneg (s - ρa)
    have h1 : Real.smoothTransition (-(s + ρa)) = 0 := by linarith
    have h2 : Real.smoothTransition (s - ρa) = 0 := by linarith
    rw [Real.smoothTransition.zero_iff_nonpos] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  · intro h
    rw [abs_le] at h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : -(s + ρa) ≤ 0),
      Real.smoothTransition.zero_of_nonpos (by linarith : s - ρa ≤ 0)]
    ring

lemma phaseBumpK_eq_zero_iff (ρa τ s : ℝ) :
    phaseBumpK ρa τ s = 0 ↔ τ ∈ Set.Icc (0 : ℝ) 1 ∧ |s| ≤ ρa := by
  unfold phaseBumpK
  constructor
  · intro h
    have a := phaseBumpT_nonneg τ
    have b := phaseBumpS_nonneg ρa s
    have h1 : phaseBumpT τ = 0 := by linarith
    have h2 : phaseBumpS ρa s = 0 := by linarith
    exact ⟨(phaseBumpT_eq_zero_iff τ).mp h1, (phaseBumpS_eq_zero_iff ρa s).mp h2⟩
  · rintro ⟨h1, h2⟩
    rw [(phaseBumpT_eq_zero_iff τ).mpr h1, (phaseBumpS_eq_zero_iff ρa s).mpr h2]
    ring

lemma phaseBumpS_neg (ρa s : ℝ) : phaseBumpS ρa (-s) = phaseBumpS ρa s := by
  unfold phaseBumpS
  ring_nf

lemma phaseBumpK_neg (ρa τ s : ℝ) : phaseBumpK ρa τ (-s) = phaseBumpK ρa τ s := by
  unfold phaseBumpK
  rw [phaseBumpS_neg]

end Work.RPB.B5
