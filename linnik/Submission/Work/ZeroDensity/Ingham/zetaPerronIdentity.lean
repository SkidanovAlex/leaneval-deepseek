import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs
import Submission.Work.ZeroDensity.Montgomery.zeroDetAltPerron

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-! ### Bridge lemmas from the Ingham vocabulary to the Montgomery vocabulary at `q = 1`

The Mellin/Perron identity for the smoothed mollified zeta series is the `q = 1` case of
`Work.ZeroDensity.Montgomery.zeroDetAltPerron`, once one identifies the Ingham objects
(`mCoef`, `MK`, `perronInt`) with the Montgomery ones (`Montgomery.mCoef`, `MX`, `PhiNaive`)
for the unique Dirichlet character of level `1`. -/

/-- The unique Dirichlet character of level `1` takes the value `1` everywhere
(`ZMod 1` is a subsingleton, so every element is a unit and the trivial character is given by
`MulChar.one_apply_coe`). -/
lemma dcOne_apply (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
  rw [show (n : ZMod 1) = ((1 : (ZMod 1)ˣ) : ZMod 1) from Subsingleton.elim _ _]
  exact MulChar.one_apply_coe 1

/-- The truncated Möbius polynomial of Montgomery at `q = 1` is Ingham's `M_K`. -/
lemma MX_one (K : ℕ) (s : ℂ) :
    Work.ZeroDensity.Montgomery.MX (1 : DirichletCharacter ℂ 1) (K : ℝ) s = MK K s := by
  simp only [Work.ZeroDensity.Montgomery.MX, MK_apply, Nat.floor_natCast]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [dcOne_apply]
  ring

/-- The truncated Möbius convolution coefficient of Montgomery at `X = K ∈ ℕ` is Ingham's. -/
lemma mCoef_cast (K n : ℕ) : Work.ZeroDensity.Montgomery.mCoef (K : ℝ) n = mCoef K n := by
  simp [Work.ZeroDensity.Montgomery.mCoef, mCoef, Nat.cast_le]

/-- Montgomery's naive integrand at `q = 1` and `X = K` is the Ingham Perron integrand:
the only difference is the order of the factors and the identification
`L(·, 1) = ζ` of `DirichletCharacter.LFunction_modOne_eq`. -/
lemma PhiNaive_one_eq (K : ℕ) (Y : ℝ) (ρ w : ℂ) :
    Work.ZeroDensity.Montgomery.PhiNaive (1 : DirichletCharacter ℂ 1) ρ (K : ℝ) Y w
      = perronInt K Y ρ w := by
  simp only [Work.ZeroDensity.Montgomery.PhiNaive, perronInt,
    DirichletCharacter.LFunction_modOne_eq]
  rw [MX_one]
  ring

/-- (Put this in namespace `Work.ZeroDensity.Ingham`, with `open scoped Classical BigOperators` and
`open MeasureTheory`; import `Submission.Work.ZeroDensity.Ingham.Defs`,
`Submission.Work.ZeroDensity.Ingham.zetaDetectorDefs`,
`Submission.Work.ZeroDensity.Montgomery.zeroDetAltPerron`.)

**Mellin/Perron inversion for the smoothed, mollified zeta series at a point `ρ` with `Re ρ > 0`.**

`Σ_{n≥1} a_K(n) n^{-ρ} e^{-n/Y} = (1/2π) ∫_ℝ Γ(2+it) Y^{2+it} ζ(ρ+2+it) M_K(ρ+2+it) dt`,

i.e. `detSum K Y ρ = (1/2π) ∫_t perronInt K Y ρ (2 + t*I)`, where `a_K(n) = mCoef K n` and
`M_K(s) = MK K s` (Montgomery–Vaughan (28.7), (28.35)).

The integral runs over the vertical line `Re w = 2`, on which `Re (ρ+w) = Re ρ + 2 > 1`, so the
Dirichlet series `ζ(s)M_K(s) = Σ_n a_K(n)n^{-s}` converges absolutely there and the inverse Mellin
transform of `Γ` (`∫_ℝ y^{-(2+it)}Γ(2+it)dt = 2π e^{-y}`, i.e. `mellinKernelExpScaled` in
`Submission/Work/ZeroDensity/Ingham/mellinMollified.lean`) applies termwise.

A ready-made proof: apply `Work.ZeroDensity.Montgomery.zeroDetAltPerron` (file
`Submission/Work/ZeroDensity/Montgomery/zeroDetAltPerron.lean`) with modulus `q = 1`, the unique
(trivial) character `χ : DirichletCharacter ℂ 1`, `X = (K : ℝ)` and `c = 2`.  For `q = 1` one has
`DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = riemannZeta s` (the `L`-function is
`ZMod.LFunction` of the underlying function, and `ZMod.LFunction_modOne_eq` gives
`LFunction Φ s = Φ 0 * riemannZeta s`), the only element of `ZMod 1` is `1` so `χ (n : ZMod 1) = 1`
and `MX 1 X s = MK ⌊X⌋₊ s = MK K s`, and `mCoef (K:ℝ) n = mCoef K n`.  Alternatively prove the
identity directly by imitating `mellinMollified` (the same identity for `1 < Re s`); there the
hypothesis `1 < Re s` is only used in summability steps that are valid for `-1 < Re s`. -/
theorem zetaPerronIdentity (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ) (hρ : 0 < ρ.re) :
    detSum K Y ρ = (1 / (2 * Real.pi)) * ∫ t : ℝ, perronInt K Y ρ (2 + (t : ℂ) * Complex.I) := by
  -- Montgomery's Perron formula at `q = 1`, `X = K` and `c = 2` (so `1 - Re ρ < 2`).
  have h := Work.ZeroDensity.Montgomery.zeroDetAltPerron (1 : DirichletCharacter ℂ 1) ρ hρ
    (K : ℝ) Y 2 (by norm_num) (by linarith) hY
  simp only [Complex.ofReal_ofNat] at h
  -- The integrand of the Perron formula is the Ingham Perron integrand.
  have hint : (∫ t : ℝ, Work.ZeroDensity.Montgomery.PhiNaive (1 : DirichletCharacter ℂ 1) ρ
        (K : ℝ) Y (2 + (t : ℂ) * Complex.I))
      = ∫ t : ℝ, perronInt K Y ρ (2 + (t : ℂ) * Complex.I) :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => PhiNaive_one_eq K Y ρ _)
  rw [← hint] at *
  rw [h]
  -- The remaining sum is `detSum` termwise.
  rw [detSum]
  refine tsum_congr fun n => ?_
  rw [mCoef_cast, dcOne_apply]
  ring

end Work.ZeroDensity.Ingham
