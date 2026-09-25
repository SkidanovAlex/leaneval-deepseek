import Mathlib
import Submission.Work.Maximal.mstWide_defs

/-!
# The band-limited interpolant of the wide-bump multiplier (MST Theorem 1, Half 2)

This module fixes the vocabulary of the *sampling* step of the wide-model maximal bound
(`Work.Maximal.mstWideModel_lr_maximal`): the sequence
`mstModSeq (star ∘ mstG P) E g x` (the folded/modulated input of the level-`s` model) is fed to the
single-bump multiplier `opMul (ϱ_s)`; the *band-limited extension* of that multiplier is the function
on `ℝ`

`mstWideLat P χ η s F T = 𝓕⁻ (mstWideExt P χ η s F T)`,

where `mstWideExt` is the (smooth, compactly supported) zero-extension of `ϱ_s · 𝓕F` to `ℝ`, read
through the explicit trigonometric polynomial `Σ_{n ∈ T} F n · e^{2πi n ·}`:

`mstWideExt x = η (c_s x) · Σ_{n ∈ T} F n · e^{2πi n x}`,  `c_s = mstWideC P s`.

The two outputs (proved in the companion modules) are that `mstWideLat` is band-limited to the ball
of radius `1/(2 c_s)` (so that the lattice sampling principle `hLattice` of the target applies with
this `δ`), that its values at the integers are the multiplier values
`mstWideLat j = opMul (ϱ_s) F (-j)`, and the curve identity
`opMul (star (Φ_N) · ϱ_s) F n = ∫_0^1 mstWideLat (-n - P(N u)) du` which turns the maximal
function over `N` into a Hardy–Littlewood maximal function.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.Maximal

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- The **zero-extension of the wide-bump multiplier's amplitude**: the function
`x ↦ η (c_s x) · Σ_{n ∈ T} F n e^{2πi n x}` on `ℝ`.  Here `T` is a finite set containing the
support of `F`; for `x` in the fundamental domain this is `ϱ_s (x) · 𝓕F (x)` (with `𝓕F` the discrete
Fourier transform of `F`), and it is the smooth compactly supported "amplitude" whose inverse
Fourier transform is the band-limited interpolant `mstWideLat`. -/
def mstWideExt (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (F : ℤ → ℂ) (T : Finset ℤ)
    (x : ℝ) : ℂ :=
  η (mstWideC P s * x) * ∑ n ∈ T, F n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (x : ℂ)))

/-- The **band-limited interpolant** of the wide-bump multiplier applied to `F`: the inverse Fourier
transform of `mstWideExt`.  Its values at the integers are the multiplier values (see
`mstWideLat_apply_int`), its Fourier transform is supported in `[-1/(2 c_s), 1/(2 c_s)]` (see
`mstWideLat_fourier_support`), and it drives the curve/maximal identity
(`mstWideLat_curve`). -/
def mstWideLat (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (F : ℤ → ℂ) (T : Finset ℤ) :
    ℝ → ℂ :=
  FourierTransformInv.fourierInv (mstWideExt P χ η s F T)

@[simp] theorem mstWideLat_apply (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (F : ℤ → ℂ)
    (T : Finset ℤ) (x : ℝ) :
    mstWideLat P χ η s F T x
      = FourierTransformInv.fourierInv (mstWideExt P χ η s F T) x := rfl

/-- **The amplitude agrees with the circle function on the fundamental domain**: for `x ∈ 𝕋` lifted
to the fundamental interval, `mstWideExt` is `ϱ_s · 𝓕F` read through the discrete Fourier transform
`discFourier F` (this is the identity that makes `mstWideLat` the interpolant of the multiplier
values). -/
theorem mstWideExt_eq_discFourier (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (F : ℤ → ℂ)
    {T : Finset ℤ} (hT : ∀ n ∉ T, F n = 0) (x : ℝ) :
    mstWideExt P χ η s F T x
      = η (mstWideC P s * x)
          * Work.BourgainPlan.IonescuWainger.discFourier F (((x : ℝ)) : Circ) := by
  rw [mstWideExt, Work.BourgainPlan.IonescuWainger.discFourier_eq_sum_of_support hT]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [fourier_coe_apply]
  congr 2
  push_cast
  ring

end

end Work.Maximal
