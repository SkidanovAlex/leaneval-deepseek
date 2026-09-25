import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs

/-!
# The `ℓ²`-multiplier `opMul` as an inverse Fourier transform

This file proves `Work.Maximal.mstMax_bridge`: for an essentially bounded circle function `φ`, a
square-summable sequence `g` and an integer `m`, the multiplier `opMul (φ) g m` — the `m`-th
coefficient of `ξ ↦ φ ξ · 𝓕g ξ` on the circle — equals the inverse Fourier transform at `m` of the
**fundamental-domain lift** of that same symbol.

The whole content is the identification of the `ℓ²(ℤ) ≅ L²(𝕋)` coefficient
`inner (fourierBasis m) (Φ • 𝓕g)` with the concrete circle integral of `ξ ↦ φ ξ · 𝓕g ξ · conj e_m ξ`
and the change of variables `circleLift f x = f (-(x : Circ))` (on the fundamental domain) together
with the sign convention of `FourierTransformInv.fourierInv` (kernel `e^{2πi x m}`), which turns the
reflection `x ↦ -x` into the complex conjugation `conj (e^{2πi m ·})`.

## Contents

* `mstChirp` with `mstChirp_eq_star_fourier` and `mstChirp_neg` — the exponential bookkeeping;
* `circleLift_fourierInv` — `𝓕⁻ (circleLift f) m` is the `m`-th Fourier coefficient of `f` on the
  circle, i.e. `∫ ξ, f ξ * star (fourier m ξ) ∂haar`;
* `opMul_eq_circleIntegral` — the `ℓ²`-inner-product definition of `opMul` rewritten as that same
  circle integral for the symbol `ξ ↦ φ ξ · 𝓕g ξ`;
* `mstMax_bridge` — the two together.
-/

open MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace lp ENNReal

set_option autoImplicit false

namespace Work.Maximal

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-- The character `u ↦ e^{-2πi m u}` of a *real* parameter, in the exact `ofReal`-shape produced by
`Real.fourierInv_eq'`: it is `star (fourier m (↑u))` (`mstChirp_eq_star_fourier`) and satisfies
`mstChirp m (-v) = e^{2πi m v}` (`mstChirp_neg`). -/
def mstChirp (m : ℤ) (u : ℝ) : ℂ :=
  Complex.exp (-((↑(2 * Real.pi * u * (m : ℝ)) : ℂ) * Complex.I))

/-- `mstChirp m u = conj (e^{2πi m u})`: the chirp is the conjugate of the `m`-th Fourier monomial
evaluated at `(u : 𝕋)`. -/
lemma mstChirp_eq_star_fourier (m : ℤ) (u : ℝ) :
    mstChirp m u = star (fourier m ((u : ℝ) : Circ)) := by
  rw [mstChirp, Complex.star_def,
    ← fourier_neg (n := m) (x := ((u : ℝ) : Circ)), fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- The reflection in the real variable turns the chirp into the *direct* character
`e^{2πi m v}`: this is what makes the change of variables `x ↦ -x` on the fundamental domain
produce exactly `conj (e^{2πi m x})`. -/
lemma mstChirp_neg (m : ℤ) (v : ℝ) :
    mstChirp m (-v) = Complex.exp ((↑(2 * Real.pi * (v * (m : ℝ))) : ℂ) * Complex.I) := by
  rw [mstChirp]
  congr 1
  push_cast
  ring

/-- **`𝓕⁻` of the fundamental-domain lift is the circle Fourier coefficient.**
For any `f : 𝕋 → ℂ`, the inverse Fourier transform at `m` of the lift
`circleLift f x = if x ∈ Ioc (-1/2) (1/2] then f (-(x : 𝕋)) else 0` is the `m`-th Fourier
coefficient of `f` against the monomial `e_m`, i.e. `∫ ξ, f ξ * conj (e^{2πi m ξ})`.

The proof: `Real.fourierInv_eq'` writes the left-hand side as the full-line integral of
`e^{2πi x m} · circleLift f x`; the lift's support reduces it to the fundamental domain
`Ioc (-1/2) (1/2]`, on which `circleLift f x = f (-(x : 𝕋))`; the substitution `x ↦ -x`
(`intervalIntegral.integral_comp_neg`) turns `e^{2πi x m} f (-x)` into
`mstChirp m x · f ((x : 𝕋)) = conj (e^{2πi m x}) f x`; and `AddCircle.integral_preimage` identifies
the fundamental-domain integral with the Haar integral over the circle. -/
theorem circleLift_fourierInv (f : Circ → ℂ) (m : ℤ) :
    FourierTransformInv.fourierInv (Work.BourgainPlan.Thm52.circleLift f) (m : ℝ)
      = ∫ ξ : Circ, f ξ * star (fourier m ξ) ∂AddCircle.haarAddCircle := by
  -- the standard measure of the circle is the (normalised) Haar measure, so that
  -- `AddCircle.integral_preimage` applies to integrals written with the default instance
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle (T := 1) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  rw [← hvol]
  rw [Real.fourierInv_eq']
  simp only [smul_eq_mul, Real.inner_apply]
  -- the lift is supported on the fundamental domain
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Ioc (-(1/2 : ℝ)) (1/2))
    (f := fun v : ℝ => Complex.exp (↑(2 * Real.pi * (v * (m : ℝ))) * Complex.I)
      * Work.BourgainPlan.Thm52.circleLift f v)
    (fun v hv => by rw [Work.BourgainPlan.Thm52.circleLift_of_notMem hv, mul_zero])]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-(1/2 : ℝ)) ≤ 1/2)]
  -- on `Ioc (-1/2) (1/2]` the lift is `x ↦ f (-(x : 𝕋))` and the chirp is `conj e_m`
  have hae : ∀ᵐ v : ℝ ∂volume, v ∈ Set.uIoc (-(1/2 : ℝ)) (1/2) →
      Complex.exp (↑(2 * Real.pi * (v * (m : ℝ))) * Complex.I)
        * Work.BourgainPlan.Thm52.circleLift f v
      = mstChirp m (-v) * f (↑(-v) : Circ) := by
    filter_upwards with v hv
    rw [Set.uIoc_of_le (by norm_num : (-(1/2 : ℝ)) ≤ 1/2)] at hv
    rw [Work.BourgainPlan.Thm52.circleLift_of_mem hv, AddCircle.coe_neg, mstChirp_neg m v]
  rw [intervalIntegral.integral_congr_ae hae]
  -- the substitution `x ↦ -x` on the symmetric interval
  have hneg : (∫ v in (-(1/2 : ℝ))..(1/2), mstChirp m (-v) * f (↑(-v) : Circ))
      = ∫ u in (-(1/2 : ℝ))..(1/2), mstChirp m u * f (↑u : Circ) := by
    simpa only [neg_neg] using intervalIntegral.integral_comp_neg
      (f := fun u : ℝ => mstChirp m u * f (↑u : Circ)) (a := (-(1/2 : ℝ))) (b := (1/2))
  rw [hneg]
  rw [intervalIntegral.integral_of_le (by norm_num : (-(1/2 : ℝ)) ≤ 1/2)]
  -- the chirp is the conjugate monomial
  rw [MeasureTheory.setIntegral_congr_fun
    (f := fun u : ℝ => mstChirp m u * f (↑u : Circ))
    (g := fun u : ℝ => star (fourier m (↑u : Circ)) * f (↑u : Circ))
    measurableSet_Ioc
    (fun u _ => by
      show mstChirp m u * f (↑u : Circ) = star (fourier m (↑u : Circ)) * f (↑u : Circ)
      rw [mstChirp_eq_star_fourier m u])]
  -- the fundamental domain is one period of the circle
  have hpre : (∫ u in Set.Ioc (-(1/2 : ℝ)) (1/2), star (fourier m (↑u : Circ)) * f (↑u : Circ))
      = ∫ ξ : Circ, star (fourier m ξ) * f ξ := by
    simpa only [show (-(1/2 : ℝ) + 1) = 1/2 by norm_num] using
      AddCircle.integral_preimage 1 (-(1/2 : ℝ))
        (fun ξ : Circ => star (fourier m ξ) * f ξ)
  rw [hpre, MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun ξ => mul_comm (star (fourier m ξ)) (f ξ)))]

/-- **The multiplier `opMul` of the symbol `ξ ↦ φ ξ · 𝓕g ξ`, read as a circle integral.**
By definition `opMul Φ g hg m` is the `m`-th coefficient of the `ℓ²(ℤ)`-sequence `Φ • 𝓕g` in the
Hilbert basis `fourierBasis`; unfolding the inner product (`MeasureTheory.L2.inner_def`) and the
heterogeneous product (`Lp.coeFn_lpSMul`), and using `MemLp.coeFn_toLp` for `Φ = φ` and
`coeFn_fourierLp` for the basis element, this is exactly
`∫ θ, (φ θ · 𝓕g θ) · conj (e^{2πi m θ})`. -/
theorem opMul_eq_circleIntegral (φ : Circ → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (g : ℤ → ℂ) (hg : Memℓp g 2) (m : ℤ) :
    Work.BourgainPlan.IonescuWainger.opMul (hφ.toLp φ) g hg m
      = ∫ θ : Circ, (φ θ * (Work.BourgainPlan.IonescuWainger.ftLp g hg : Circ → ℂ) θ)
          * star (fourier m θ) ∂AddCircle.haarAddCircle := by
  rw [Work.BourgainPlan.IonescuWainger.opMul_apply, Work.BourgainPlan.IonescuWainger.opMulLp,
    MeasureTheory.L2.inner_def]
  rw [MeasureTheory.integral_congr_ae]
  have h1 : (fun a => ((fourierBasis (T := 1) m : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) a))
      =ᵐ[AddCircle.haarAddCircle] ⇑(fourier (T := 1) m) := by
    simpa only [coe_fourierBasis] using coeFn_fourierLp (T := 1) (p := 2) (n := m)
  filter_upwards [h1,
      MeasureTheory.Lp.coeFn_lpSMul (r := 2) (hφ.toLp φ)
        (Work.BourgainPlan.IonescuWainger.ftLp g hg),
      MeasureTheory.MemLp.coeFn_toLp hφ] with θ h1' h2 h3
  simp only [h1', h2, h3, Pi.mul_apply, smul_eq_mul, RCLike.inner_apply, starRingEnd_apply]

theorem mstMax_bridge (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (g : ℤ → ℂ) (hg : Memℓp g 2) (m : ℤ) :
    Work.BourgainPlan.IonescuWainger.opMul (hφ.toLp φ) g hg m
      = FourierTransformInv.fourierInv
          (Work.BourgainPlan.Thm52.circleLift
            (fun ξ => φ ξ * (Work.BourgainPlan.IonescuWainger.ftLp g hg :
              Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ)) (m : ℝ) := by
  rw [circleLift_fourierInv, opMul_eq_circleIntegral]

end

end Work.Maximal
