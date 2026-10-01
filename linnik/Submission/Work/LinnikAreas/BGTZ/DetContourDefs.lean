/-
# Vocabulary for the contour shift of the BGTZ detector

`Work.LinnikAreas.BGTZ.detector χ₁ χ N θw ρ` is the finite smoothed sum
`Σ_{n ≤ N} a(n)χ(n)(Σ_{d|n}θ_d)² n^{-ρ}(1 - n/N)` (see `BGTZSetup`), and
`detJ χ₁ χ R θw N ρ` (see `DetectorDefs`) is the integral along the line `Re s = 1/2 - Re ρ` of the
integrand `L(χ,ρ+s)L(χχ₁,ρ+s)G(ρ+s,χ)N^s/(s(s+1))`.  The purpose of this file is to set up the
*analytic* objects that the contour shift from the Perron line `Re s = 1` down to the critical line
`Re s = 1/2 - Re ρ` manipulates:

* `detInt χ₁ χ R θw N ρ s` — the integrand itself;
* `detA … s` — its numerator with the pole at `s = 1 - ρ` divided out: `detA s = (s-(1-ρ))·detInt s`
  (away from the two exceptional points `s = 0` and `s = 1-ρ`).  When one of `χ`, `χχ₁` is the
  principal character the factor `s - (1-ρ)` times that principal `L`-function is replaced by
  Mathlib's entire function `LFunctionTrivChar₁ q (ρ+s)` (the "multiplied away piece" of the
  principal `L`-function);
* `detM … s = dslope (detA …) 0 s / (s+1)` — the analytic continuation of `detA s/(s(s+1))`
  (the `s = 0` singularity is removable by the vanishing of `L(ρ,χ)L(ρ,χχ₁)`);
* `detH … s = dslope (detM …) (1-ρ) s` — the patched integrand, entire on the strip;
* `detRes … = detM … (1-ρ)` — the residue of the integrand at the pole `s = 1-ρ`.

The main algebraic identity (proved in `DetectorContour`) is

`detInt … s = detRes …/(s - (1-ρ)) + detH … s` for `s ∉ {0, 1-ρ}`,

so that the vertical contour shift across `s = 1-ρ` (with the pole at `s = 0` removable because
`L(ρ,χ) = 0` or `L(ρ,χχ₁) = 0`) produces exactly the residue `detRes`, which is then bounded by
`detResBound` through `G(1,χ₁) = G(1,1)` and `∏_{p|q}(1-p⁻¹) = φ(q)/q ≤ q/φ(q)`.
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorDefs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

/-- The integrand of the detector contour integral:
`L(χ,ρ+s)L(χχ₁,ρ+s)G(ρ+s,χ)N^s/(s(s+1))`.  Its integral against `dt/(2π)` over the line
`Re s = 1/2 - Re ρ` is `detJ`. -/
def detInt (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ (ρ + s) * DirichletCharacter.LFunction (χ * χ₁) (ρ + s)
    * sieveG χ₁ R θw (ρ + s) χ * (N : ℂ) ^ s / (s * (s + 1))

/-- The non-principal `L`-function factor of the integrand.  If `χ` is principal it is `χχ₁`, if
`χχ₁` is principal it is `χ` (which is not principal then), otherwise the two factors are kept
together (encoded by the trivial character, signalled by the flag used in `detA`). -/
def detOther (χ₁ χ : DirichletCharacter ℂ q) : DirichletCharacter ℂ q :=
  if χ = 1 then χ * χ₁ else χ

/-- The numerator of the integrand: `(s-(1-ρ))·detInt … s`, made analytic at `s = 1-ρ` by
replacing `(s-(1-ρ))·L(ρ+s,χ₀)` with Mathlib's entire `LFunctionTrivChar₁ q (ρ+s)`. -/
def detA (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (s : ℂ) : ℂ :=
  (if χ = 1 ∨ χ * χ₁ = 1 then
      DirichletCharacter.LFunctionTrivChar₁ q (ρ + s)
        * DirichletCharacter.LFunction (detOther χ₁ χ) (ρ + s)
    else
      (s - (1 - ρ)) * DirichletCharacter.LFunction χ (ρ + s)
        * DirichletCharacter.LFunction (χ * χ₁) (ρ + s))
    * sieveG χ₁ R θw (ρ + s) χ * (N : ℂ) ^ s

/-- The analytic continuation of `detA … s/(s(s+1))` at `s = 0`. -/
def detM (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (s : ℂ) : ℂ :=
  dslope (detA χ₁ χ R θw N ρ) 0 s / (s + 1)

/-- The patched integrand: `detInt … s - detRes …/(s - (1-ρ))`, analytic on the strip. -/
def detH (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ)
    (s : ℂ) : ℂ :=
  dslope (detM χ₁ χ R θw N ρ) (1 - ρ) s

/-- The residue of the integrand at its pole `s = 1 - ρ`. -/
def detRes (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ) : ℂ :=
  detM χ₁ χ R θw N ρ (1 - ρ)

/-- `detInt` is the integrand of `detJ`: the latter is `(1/2π)∫_ℝ detInt (detLine ρ + t·I) dt`. -/
lemma detJ_eq_integral (χ₁ χ : DirichletCharacter ℂ q) (R : ℕ) (θw : ℕ → ℝ) (N : ℕ) (ρ : ℂ) :
    detJ χ₁ χ R θw N ρ
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, detInt χ₁ χ R θw N ρ (detLine ρ + (t : ℂ) * I) := by
  rw [detJ]
  congr 1
  refine MeasureTheory.integral_congr_ae (.of_forall fun t => ?_)
  simp only [detInt, detLine]
  ring_nf

end Work.LinnikAreas.BGTZ
