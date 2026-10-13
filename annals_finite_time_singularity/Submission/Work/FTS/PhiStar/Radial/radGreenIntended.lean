/-
# `radGreenIntended` — the radial Green's function as *intended* by `Radial/Defs.lean`

`Submission/Work/FTS/PhiStar/Radial/Defs.lean` defines (`Work.FTS.PhiStar.Radial.radGreen`)

```
def radGreen (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ :=
  1 / (α * (4 * (m : ℝ) + 5)) *
    (z ^ (-(2 * (m : ℝ) + 5) / α) * ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)
      + z ^ (2 * (m : ℝ) / α) * ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))
```

(the body of the *first* integral is **not** parenthesised).  The body of `∫ t in (0:ℝ)..z, ·`
extends as far to the right as possible, so the summand `+ z ^ (2m/α) * ∫ t in Set.Ioi z, …` is
**swallowed into the first integral**; the term that actually elaborates is (this is verified
mechanically: `unfold radGreen; rfl`)

```
radGreen α m c z = 1/(α(4m+5)) * (z ^ s⁻ * ∫_0^z ( c t * t^(...) + z ^ s⁺ * ∫_{Ioi z} c t * t^(...) ) dt)
                  = 1/(α(4m+5)) * (z ^ s⁻ * ∫_0^z c t * t^(...)
                                     + z ^ (1 - 5/α) * ∫_{Ioi z} c t * t^(...))
```

with `s⁻ = -(2m+5)/α`, `s⁺ = 2m/α`: the second term of the *intended* decaying solution
(`z ^ s⁺ * ∫_z^∞ …`) has been replaced by the one with the `m`-independent power `z ^ (1 - 5/α)`.
Consequently the identity requested in `radGreen_solves` is **false** as stated — a counterexample
is `α = 1`, `m = 0`, `c t = t * exp (-t)` (it satisfies all four hypotheses), `z = 2`, where the
left-hand side of the claimed identity is `(7/20) * exp (-2)` while `c 2 = 2 * exp (-2)`
(see `NOTES_radGreen_solves_parse_bug.md` in this directory).

This file contains the corrected function `radGreenI` — the same formula with the body of the first
integral parenthesised — together with a **complete proof** of the intended ODE

`-α²z² a'' - α(5+α) z a' + λ_m a = c`     (`λ_m = lamR m`),

so that repairing `Radial/Defs.lean` only requires adding the parentheses, and the proof below can
be re-used verbatim (only the name of the function changes).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Radial.intervalIntegrable_of_Ioi_Ioo
import Submission.Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo
import Submission.Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Radial

set_option autoImplicit false

/-- **The intended radial Green's function** (the explicit decaying solution of the mode-`m` Euler
equation `-α²z²a'' - α(5+α)z a' + λ_m a = c`, `λ_m = 2m(2m+5)`).  This is the formula of
`Work.FTS.PhiStar.Radial.radGreen` with the body of the first integral parenthesised; for the
function defined in `Radial/Defs.lean` that parenthesis is missing and the two differ. -/
def radGreenI (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ :=
  1 / (α * (4 * (m : ℝ) + 5)) *
    (z ^ (-(2 * (m : ℝ) + 5) / α) * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      + z ^ (2 * (m : ℝ) / α) * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1)))

/-! ### Private scaffolding -/

/-- The decaying indicial exponent `s⁻ = -(2m+5)/α`. -/
private def sgN (α : ℝ) (m : ℕ) : ℝ := -(2 * (m : ℝ) + 5) / α
/-- The growing indicial exponent `s⁺ = 2m/α`. -/
private def sgP (α : ℝ) (m : ℕ) : ℝ := 2 * (m : ℝ) / α
/-- The normalising constant `1/(α(4m+5)) = 1/(α²(s⁺-s⁻))`. -/
private def gK (α : ℝ) (m : ℕ) : ℝ := 1 / (α * (4 * (m : ℝ) + 5))
/-- The integrand of the `0..z` integral. -/
private def gf1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)
/-- The integrand of the `Ioi z` integral. -/
private def gf2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ (-(2 * (m : ℝ) / α) - 1)
/-- The `0..z` integral. -/
private def gA (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..z, gf1 α m c t
/-- The `Ioi z` integral. -/
private def gB (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Set.Ioi z, gf2 α m c t
/-- The derivative of `radGreenI`. -/
private def gd1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  gK α m * ((sgN α m * y ^ (sgN α m - 1)) * gA α m c y
            + (sgP α m * y ^ (sgP α m - 1)) * gB α m c y)
/-- The second derivative of `radGreenI`. -/
private def gd2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  gK α m * (((sgN α m * ((sgN α m - 1) * y ^ (sgN α m - 2))) * gA α m c y
            + (sgN α m * y ^ (sgN α m - 1)) * gf1 α m c y)
          + ((sgP α m * ((sgP α m - 1) * y ^ (sgP α m - 2))) * gB α m c y
            + (sgP α m * y ^ (sgP α m - 1)) * (-(gf2 α m c y))))

private lemma radGreenI_eq (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    radGreenI α m c
      = fun z => gK α m * (z ^ (sgN α m) * gA α m c z + z ^ (sgP α m) * gB α m c z) := by
  funext z
  rfl

/-! ### The main computation -/

theorem radGreenI_solves {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (radGreenI α m c)) z
        - α * (5 + α) * z * deriv (radGreenI α m c) z
        + lamR m * radGreenI α m c z = c z := by
  intro z hz
  have hαne : α ≠ 0 := ne_of_gt hα
  have h0i : IntegrableOn (gf1 α m c) (Set.Ioo 0 1) := h0
  have h0i' : IntegrableOn (gf2 α m c) (Set.Ioo 0 1) := h0'
  have hinfi : IntegrableOn (gf2 α m c) (Set.Ioi 1) := hinf
  have hf1c : ContinuousOn (gf1 α m c) (Set.Ioi 0) :=
    hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))
  have hf2c : ContinuousOn (gf2 α m c) (Set.Ioi 0) :=
    hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))
  -- Differentiability of the two building blocks, at every `y > 0`.
  have hAall : ∀ y ∈ Set.Ioi (0 : ℝ), HasDerivAt (gA α m c) (gf1 α m c y) y := by
    intro y hy
    have hsm : StronglyMeasurableAtFilter (gf1 α m c) (𝓝 y) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hf1c y hy
    exact intervalIntegral.integral_hasDerivAt_right (a := 0) (b := y)
      (intervalIntegrable_of_Ioi_Ioo hy hf1c h0i) hsm (hf1c.continuousAt (Ioi_mem_nhds hy))
  have hBall : ∀ y ∈ Set.Ioi (0 : ℝ), HasDerivAt (gB α m c) (-(gf2 α m c y)) y := by
    intro y hy
    have hy0 : 0 < y := hy
    exact hasDerivAt_integral_Ioi (a := y / 2) (by linarith)
      (hf2c.mono (fun t ht => by
        have h := ht; simp only [Set.mem_Ioi] at h ⊢; linarith))
      (integrableOn_Ioi_of_Ioi_Ioo (by linarith) hf2c hinfi)
  -- First derivative.
  have hGreen1 : ∀ y ∈ Set.Ioi (0 : ℝ), HasDerivAt (radGreenI α m c) (gd1 α m c y) y := by
    intro y hy
    have hy0 : 0 < y := hy
    have hyne : y ≠ 0 := ne_of_gt hy0
    have hA := hAall y hy
    have hB := hBall y hy
    have hp1 : HasDerivAt (fun t : ℝ => t ^ (sgN α m)) (sgN α m * y ^ (sgN α m - 1)) y :=
      Real.hasDerivAt_rpow_const (Or.inl hyne)
    have hp2 : HasDerivAt (fun t : ℝ => t ^ (sgP α m)) (sgP α m * y ^ (sgP α m - 1)) y :=
      Real.hasDerivAt_rpow_const (Or.inl hyne)
    have hm1 : HasDerivAt (fun t : ℝ => t ^ (sgN α m) * gA α m c t)
        ((sgN α m * y ^ (sgN α m - 1)) * gA α m c y + y ^ (sgN α m) * gf1 α m c y) y :=
      hp1.mul hA
    have hm2 : HasDerivAt (fun t : ℝ => t ^ (sgP α m) * gB α m c t)
        ((sgP α m * y ^ (sgP α m - 1)) * gB α m c y
          + y ^ (sgP α m) * (-(gf2 α m c y))) y :=
      hp2.mul hB
    have h3 : HasDerivAt (fun t : ℝ =>
        gK α m * (t ^ (sgN α m) * gA α m c t + t ^ (sgP α m) * gB α m c t))
        (gK α m * (((sgN α m * y ^ (sgN α m - 1)) * gA α m c y
                      + y ^ (sgN α m) * gf1 α m c y)
                    + ((sgP α m * y ^ (sgP α m - 1)) * gB α m c y
                      + y ^ (sgP α m) * (-(gf2 α m c y))))) y :=
      (hm1.add hm2).const_mul (gK α m)
    have hc1 : y ^ (sgN α m) * gf1 α m c y = c y / y := by
      have he : (2 * (m : ℝ) + 5) / α - 1 = -1 - (-(2 * (m : ℝ) + 5) / α) := by ring
      have hf : gf1 α m c y = c y * y ^ (-1 - sgN α m) := by
        simp only [gf1, sgN]; rw [he]
      calc y ^ (sgN α m) * gf1 α m c y
          = y ^ (sgN α m) * (c y * y ^ (-1 - sgN α m)) := by rw [hf]
        _ = c y * (y ^ (sgN α m) * y ^ (-1 - sgN α m)) := by ring
        _ = c y * y ^ (-(1 : ℝ)) := by
              have hExp : sgN α m + (-1 - sgN α m) = -(1 : ℝ) := by ring
              rw [← Real.rpow_add hy0, hExp]
        _ = c y / y := by rw [Real.rpow_neg_one, div_eq_mul_inv]
    have hc2 : y ^ (sgP α m) * gf2 α m c y = c y / y := by
      have he : -(2 * (m : ℝ) / α) - 1 = -1 - (2 * (m : ℝ) / α) := by ring
      have hf : gf2 α m c y = c y * y ^ (-1 - sgP α m) := by
        simp only [gf2, sgP]; rw [he]
      calc y ^ (sgP α m) * gf2 α m c y
          = y ^ (sgP α m) * (c y * y ^ (-1 - sgP α m)) := by rw [hf]
        _ = c y * (y ^ (sgP α m) * y ^ (-1 - sgP α m)) := by ring
        _ = c y * y ^ (-(1 : ℝ)) := by
              have hExp : sgP α m + (-1 - sgP α m) = -(1 : ℝ) := by ring
              rw [← Real.rpow_add hy0, hExp]
        _ = c y / y := by rw [Real.rpow_neg_one, div_eq_mul_inv]
    have hval : gK α m * (((sgN α m * y ^ (sgN α m - 1)) * gA α m c y
                      + y ^ (sgN α m) * gf1 α m c y)
                    + ((sgP α m * y ^ (sgP α m - 1)) * gB α m c y
                      + y ^ (sgP α m) * (-(gf2 α m c y)))) = gd1 α m c y := by
      simp only [gd1]
      rw [mul_neg, hc1, hc2]
      ring
    rw [radGreenI_eq]
    exact h3.congr_deriv hval
  -- Second derivative.
  have hD1 : HasDerivAt (gd1 α m c) (gd2 α m c z) z := by
    have hzne : z ≠ 0 := ne_of_gt hz
    have hA := hAall z hz
    have hB := hBall z hz
    have hp1 : HasDerivAt (fun t : ℝ => sgN α m * t ^ (sgN α m - 1))
        (sgN α m * ((sgN α m - 1) * z ^ (sgN α m - 2))) z := by
      have h := (Real.hasDerivAt_rpow_const (x := z) (p := sgN α m - 1)
        (Or.inl hzne)).const_mul (sgN α m)
      rwa [show (sgN α m - 1) - 1 = sgN α m - 2 from by ring] at h
    have hp2 : HasDerivAt (fun t : ℝ => sgP α m * t ^ (sgP α m - 1))
        (sgP α m * ((sgP α m - 1) * z ^ (sgP α m - 2))) z := by
      have h := (Real.hasDerivAt_rpow_const (x := z) (p := sgP α m - 1)
        (Or.inl hzne)).const_mul (sgP α m)
      rwa [show (sgP α m - 1) - 1 = sgP α m - 2 from by ring] at h
    have h3 : HasDerivAt (gd1 α m c) (gd2 α m c z) z :=
      ((hp1.mul hA).add (hp2.mul hB)).const_mul (gK α m)
    exact h3
  have hderivEq : deriv (radGreenI α m c) =ᶠ[𝓝 z] gd1 α m c :=
    eventually_of_mem (Ioi_mem_nhds hz) (fun y hy => (hGreen1 y hy).deriv)
  have hdd : deriv (deriv (radGreenI α m c)) z = gd2 α m c z := by
    rw [hderivEq.deriv_eq, hD1.deriv]
  have hd1z : deriv (radGreenI α m c) z = gd1 α m c z := (hGreen1 z hz).deriv
  have hgz : radGreenI α m c z
      = gK α m * (z ^ (sgN α m) * gA α m c z + z ^ (sgP α m) * gB α m c z) :=
    congrFun (radGreenI_eq α m c) z
  rw [hdd, hd1z, hgz]
  -- The `rpow` clearing identities.
  have hzs1 : z * z ^ (sgN α m - 1) = z ^ (sgN α m) := by
    nth_rewrite 1 [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hzs2 : z ^ 2 * z ^ (sgN α m - 2) = z ^ (sgN α m) := by
    rw [← Real.rpow_two z, ← Real.rpow_add hz]
    congr 1
    ring
  have hzp1 : z * z ^ (sgP α m - 1) = z ^ (sgP α m) := by
    nth_rewrite 1 [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hzp2 : z ^ 2 * z ^ (sgP α m - 2) = z ^ (sgP α m) := by
    rw [← Real.rpow_two z, ← Real.rpow_add hz]
    congr 1
    ring
  have hc1 : z ^ 2 * z ^ (sgN α m - 1) * gf1 α m c z = c z := by
    have he : (2 * (m : ℝ) + 5) / α - 1 = -1 - (-(2 * (m : ℝ) + 5) / α) := by ring
    have hf : gf1 α m c z = c z * z ^ (-1 - sgN α m) := by
      simp only [gf1, sgN]; rw [he]
    have h2 : z ^ 2 * z ^ (sgN α m - 1) = z ^ (sgN α m + 1) := by
      rw [← Real.rpow_two z, ← Real.rpow_add hz]; congr 1; ring
    have hE : (sgN α m + 1) + (-1 - sgN α m) = 0 := by ring
    have hcomb : z ^ 2 * z ^ (sgN α m - 1) * z ^ (-1 - sgN α m) = 1 := by
      rw [h2, ← Real.rpow_add hz, hE, Real.rpow_zero]
    calc z ^ 2 * z ^ (sgN α m - 1) * gf1 α m c z
        = z ^ 2 * z ^ (sgN α m - 1) * (c z * z ^ (-1 - sgN α m)) := by rw [hf]
      _ = c z * (z ^ 2 * z ^ (sgN α m - 1) * z ^ (-1 - sgN α m)) := by ring
      _ = c z * 1 := by rw [hcomb]
      _ = c z := by ring
  have hc2 : z ^ 2 * z ^ (sgP α m - 1) * gf2 α m c z = c z := by
    have he : -(2 * (m : ℝ) / α) - 1 = -1 - (2 * (m : ℝ) / α) := by ring
    have hf : gf2 α m c z = c z * z ^ (-1 - sgP α m) := by
      simp only [gf2, sgP]; rw [he]
    have h2 : z ^ 2 * z ^ (sgP α m - 1) = z ^ (sgP α m + 1) := by
      rw [← Real.rpow_two z, ← Real.rpow_add hz]; congr 1; ring
    have hE : (sgP α m + 1) + (-1 - sgP α m) = 0 := by ring
    have hcomb : z ^ 2 * z ^ (sgP α m - 1) * z ^ (-1 - sgP α m) = 1 := by
      rw [h2, ← Real.rpow_add hz, hE, Real.rpow_zero]
    calc z ^ 2 * z ^ (sgP α m - 1) * gf2 α m c z
        = z ^ 2 * z ^ (sgP α m - 1) * (c z * z ^ (-1 - sgP α m)) := by rw [hf]
      _ = c z * (z ^ 2 * z ^ (sgP α m - 1) * z ^ (-1 - sgP α m)) := by ring
      _ = c z * 1 := by rw [hcomb]
      _ = c z := by ring
  have hzA1 : z * gd1 α m c z = gK α m * (sgN α m * (z ^ (sgN α m) * gA α m c z)
      + sgP α m * (z ^ (sgP α m) * gB α m c z)) := by
    simp only [gd1]
    linear_combination (gK α m * sgN α m * gA α m c z) * hzs1
      + (gK α m * sgP α m * gB α m c z) * hzp1
  have hzA2 : z ^ 2 * gd2 α m c z
      = gK α m * (sgN α m * (sgN α m - 1) * (z ^ (sgN α m) * gA α m c z)
        + sgP α m * (sgP α m - 1) * (z ^ (sgP α m) * gB α m c z)
        + (sgN α m - sgP α m) * c z) := by
    simp only [gd2]
    linear_combination (gK α m * sgN α m * (sgN α m - 1) * gA α m c z) * hzs2
      + (gK α m * sgP α m * (sgP α m - 1) * gB α m c z) * hzp2
      + (gK α m * sgN α m) * hc1 - (gK α m * sgP α m) * hc2
  have hind1 : -α ^ 2 * sgN α m * (sgN α m - 1) - α * (5 + α) * sgN α m + lamR m = 0 := by
    simp only [sgN, lamR]
    field_simp
    ring
  have hind2 : -α ^ 2 * sgP α m * (sgP α m - 1) - α * (5 + α) * sgP α m + lamR m = 0 := by
    simp only [sgP, lamR]
    field_simp
    ring
  have hK : α ^ 2 * gK α m * (sgP α m - sgN α m) = 1 := by
    simp only [gK, sgP, sgN]
    field_simp
    ring
  linear_combination (-(α ^ 2)) * hzA2 - (α * (5 + α)) * hzA1
    + (gK α m * (z ^ (sgN α m) * gA α m c z)) * hind1
    + (gK α m * (z ^ (sgP α m) * gB α m c z)) * hind2 + (c z) * hK

end Work.FTS.PhiStar.Radial
