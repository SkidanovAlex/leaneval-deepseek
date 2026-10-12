import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseFixB3.Defs
import Submission.Work.BoseKinLoc.Momentum.memLp_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Parseval pairing for the corpus's `p`-convention Fourier transform, `L¹ ∩ L²` version

For real `u v ∈ L¹ ∩ L²(ℝ³)`,

`∫_x u x * v x = (2π)⁻³ ∫_p Re(conj(kinFT u p) * kinFT v p)`,

where `kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy` is the corpus's `p`-convention Fourier transform
(`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier` identifies it with Mathlib's `𝓕 u ((2π)⁻¹•p)`).

The proof is the `p`-convention version of the sesquilinear Parseval identity, established in
three steps.

* `fourier_inner_memLp` — sesquilinear Parseval in Mathlib's unitary convention for `L¹ ∩ L²`
  functions, `∫_ξ ⟪𝓕 f ξ, 𝓕 g ξ⟫ = ∫_x ⟪f x, g x⟫`, obtained from the `L²` Fourier isometry
  (`Lp.inner_fourier_eq`) together with the a.e. identification of the `L²` Fourier transform with
  the pointwise Fourier integral (`Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp`).
* `kinFT_inner_eq_fourier` — the change of variables `p = 2π ξ`, which produces the factor `(2π)³`
  on the Fourier side (no integrability needed: `Measure.integral_comp_inv_smul_of_nonneg` is valid
  for arbitrary functions).
* `kinFT_parseval_c` — the two combined, in the corpus's convention, for complex `L¹ ∩ L²`
  functions; `parseval_L1L2` is its real-part reduction.

Since `u v ∈ L²` and the functions are real, the complex pairing
`∫_x ⟪ũ x, ṽ x⟫ = ∫_x u x * v x` is automatically real, and taking real parts of
`kinFT_parseval_c` gives the claimed identity.
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform

namespace Work.BoseFixB3.HighMassAux

/-! ## 1. Sesquilinear Parseval in Mathlib's convention -/

/-- **Sesquilinear Parseval for `L¹ ∩ L²` functions on `ℝ³`** (Mathlib's unitary Fourier
convention): for `f g ∈ L¹ ∩ L²`,

`∫_ξ ⟪𝓕 f ξ, 𝓕 g ξ⟫ = ∫_x ⟪f x, g x⟫`.

The pointwise Fourier integrals `𝓕 f`, `𝓕 g` are well defined by integrability, and they represent
the `L²` Fourier transforms of the `L²` classes of `f` and `g`
(`Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp`), so the `L²` Fourier isometry
`Lp.inner_fourier_eq` transfers to the pointwise integrals. -/
theorem fourier_inner_memLp {f g : Submission.BoseGases.kcE3 → ℂ}
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume)
    (hg1 : MemLp g 1 volume) (hg2 : MemLp g 2 volume) :
    (∫ ξ : Submission.BoseGases.kcE3, inner ℂ (𝓕 f ξ) (𝓕 g ξ)) = ∫ x : Submission.BoseGases.kcE3, inner ℂ (f x) (g x) := by
  have hiso : inner ℂ (𝓕 (hf2.toLp f)) (𝓕 (hg2.toLp g))
      = inner ℂ (hf2.toLp f) (hg2.toLp g) :=
    Lp.inner_fourier_eq _ _
  rw [L2.inner_def, L2.inner_def] at hiso
  have hFae : ((𝓕 (hf2.toLp f) : Lp ℂ 2 volume) : Submission.BoseGases.kcE3 → ℂ) =ᵐ[volume] 𝓕 f :=
    Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp hf1 hf2
  have hGae : ((𝓕 (hg2.toLp g) : Lp ℂ 2 volume) : Submission.BoseGases.kcE3 → ℂ) =ᵐ[volume] 𝓕 g :=
    Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp hg1 hg2
  have hfa : ((hf2.toLp f : Lp ℂ 2 volume) : Submission.BoseGases.kcE3 → ℂ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hga : ((hg2.toLp g : Lp ℂ 2 volume) : Submission.BoseGases.kcE3 → ℂ) =ᵐ[volume] g := hg2.coeFn_toLp
  have hL : (∫ a : Submission.BoseGases.kcE3, inner ℂ ((𝓕 (hf2.toLp f) : Lp ℂ 2 volume) a)
        ((𝓕 (hg2.toLp g) : Lp ℂ 2 volume) a))
      = ∫ ξ : Submission.BoseGases.kcE3, inner ℂ (𝓕 f ξ) (𝓕 g ξ) := by
    apply integral_congr_ae
    filter_upwards [hFae, hGae] with ξ h1 h2
    rw [h1, h2]
  have hR : (∫ a : Submission.BoseGases.kcE3, inner ℂ ((hf2.toLp f : Lp ℂ 2 volume) a)
        ((hg2.toLp g : Lp ℂ 2 volume) a))
      = ∫ x : Submission.BoseGases.kcE3, inner ℂ (f x) (g x) := by
    apply integral_congr_ae
    filter_upwards [hfa, hga] with x h1 h2
    rw [h1, h2]
  rw [← hL, ← hR]
  exact hiso

/-! ## 2. The `p`-convention change of variables -/

/-- **Change of variables `p = 2π ξ` for the `kinFT` pairing.**  For arbitrary
`f g : ℝ³ → ℂ`,

`∫_p ⟪kinFT f p, kinFT g p⟫ = (2π)³ ∫_ξ ⟪𝓕 f ξ, 𝓕 g ξ⟫`.

No integrability is needed: `kinFT f p = 𝓕 f ((2π)⁻¹ • p)` pointwise, and
`Measure.integral_comp_inv_smul_of_nonneg` is valid for arbitrary functions (the Bochner
convention settles the non-integrable case). -/
theorem kinFT_inner_eq_fourier (f g : Submission.BoseGases.kcE3 → ℂ) :
    (∫ p : Submission.BoseGases.kcE3, inner ℂ (Submission.BoseGases.kinFT f p) (Submission.BoseGases.kinFT g p))
      = (((2 * Real.pi) ^ 3 : ℝ) : ℂ)
        * ∫ ξ : Submission.BoseGases.kcE3, inner ℂ (𝓕 f ξ) (𝓕 g ξ) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : (∫ p : Submission.BoseGases.kcE3,
        inner ℂ (Submission.BoseGases.kinFT f p) (Submission.BoseGases.kinFT g p))
      = ∫ p : Submission.BoseGases.kcE3, inner ℂ (𝓕 f ((2 * Real.pi)⁻¹ • p))
          (𝓕 g ((2 * Real.pi)⁻¹ • p)) := by
    apply integral_congr_ae
    filter_upwards with p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier,
      Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
  rw [h1]
  have h2 := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure (Submission.BoseGases.kcE3))
    (fun ξ : Submission.BoseGases.kcE3 => inner ℂ (𝓕 f ξ) (𝓕 g ξ)) (R := 2 * Real.pi) hpi.le
  rw [show Module.finrank ℝ Submission.BoseGases.kcE3 = 3 from by simp] at h2
  rw [h2, RCLike.real_smul_eq_coe_mul]
  rfl

/-! ## 3. Integrability of the `p`-integrand -/

/-- The pairing `p ↦ ⟪kinFT f p, kinFT g p⟫` of two `L¹ ∩ L²` functions is integrable: `kinFT f`
and `kinFT g` are in `L²` (`Work.BoseKinLoc.Momentum.memLp_kinFT`), and the inner product of two
`L²` functions is integrable (`MeasureTheory.L2.integrable_inner`). -/
theorem integrable_inner_kinFT {f g : Submission.BoseGases.kcE3 → ℂ}
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume)
    (hg1 : MemLp g 1 volume) (hg2 : MemLp g 2 volume) :
    Integrable (fun p : Submission.BoseGases.kcE3 =>
      inner ℂ (Submission.BoseGases.kinFT f p) (Submission.BoseGases.kinFT g p)) := by
  have hF : MemLp (Submission.BoseGases.kinFT f) 2 volume :=
    Work.BoseKinLoc.Momentum.memLp_kinFT (memLp_one_iff_integrable.mp hf1) hf2
  have hG : MemLp (Submission.BoseGases.kinFT g) 2 volume :=
    Work.BoseKinLoc.Momentum.memLp_kinFT (memLp_one_iff_integrable.mp hg1) hg2
  have h := L2.integrable_inner (𝕜 := ℂ) (hF.toLp (Submission.BoseGases.kinFT f))
    (hG.toLp (Submission.BoseGases.kinFT g))
  refine h.congr ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with p h1 h2
  rw [h1, h2]

/-! ## 4. Complex Parseval in the corpus's `p`-convention -/

/-- **Sesquilinear Parseval in the corpus's `p`-convention** for complex `L¹ ∩ L²` functions:

`∫_p ⟪kinFT f p, kinFT g p⟫ = (2π)³ ∫_x ⟪f x, g x⟫`. -/
theorem kinFT_parseval_c {f g : Submission.BoseGases.kcE3 → ℂ}
    (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume)
    (hg1 : MemLp g 1 volume) (hg2 : MemLp g 2 volume) :
    (∫ p : Submission.BoseGases.kcE3, inner ℂ (Submission.BoseGases.kinFT f p) (Submission.BoseGases.kinFT g p))
      = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) * ∫ x : Submission.BoseGases.kcE3, inner ℂ (f x) (g x) := by
  rw [kinFT_inner_eq_fourier, fourier_inner_memLp hf1 hf2 hg1 hg2]

/-! ## 5. The real pairing -/

/-- For real-valued `f g` (viewed in `ℂ`) the sesquilinear pairing `x ↦ ⟪f x, g x⟫` is the
constant `u x * v x`, so its integral is the real integral of the product. -/
theorem integral_inner_ofReal_eq (u v : Submission.BoseGases.kcE3 → ℝ) :
    (∫ x : Submission.BoseGases.kcE3, inner ℂ ((u x : ℂ)) ((v x : ℂ)))
      = ((∫ x : Submission.BoseGases.kcE3, u x * v x : ℝ) : ℂ) := by
  have h1 : (∫ x : Submission.BoseGases.kcE3, inner ℂ ((u x : ℂ)) ((v x : ℂ)))
      = ∫ x : Submission.BoseGases.kcE3, ((u x * v x : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, mul_comm]
  rw [h1]
  exact integral_ofReal

/-- Parseval pairing in the corpus's `p`-convention for real `L¹ ∩ L²` functions:
`∫_x u x * v x = (2π)⁻³ ∫_p Re(conj(kinFT u p) * kinFT v p)`.

Provable either by polarization from `Work.BoseFixB3.HighMassAux.plancherel_L1L2`
(with `kinFT` linearity and the pointwise expansion of `‖kinFT (u+v)‖²`), or directly
by `kinFT_eq_fourier` + Mathlib's `∫ ⟪𝓕f, 𝓕g⟫ = ∫ ⟪f,g⟫` for `L²` + the a.e. identification. -/
theorem parseval_L1L2 {u v : Submission.BoseGases.kcE3 → ℝ}
    (hu1 : MeasureTheory.MemLp u 1 MeasureTheory.volume)
    (hu2 : MeasureTheory.MemLp u 2 MeasureTheory.volume)
    (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (hv2 : MeasureTheory.MemLp v 2 MeasureTheory.volume) :
    ∫ x : Submission.BoseGases.kcE3, u x * v x
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : Submission.BoseGases.kcE3,
          (starRingEnd ℂ (Submission.BoseGases.kinFT (fun z => (u z : ℂ)) p)
            * Submission.BoseGases.kinFT (fun z => (v z : ℂ)) p).re := by
  set f : Submission.BoseGases.kcE3 → ℂ := fun z => (u z : ℂ) with hf
  set g : Submission.BoseGases.kcE3 → ℂ := fun z => (v z : ℂ) with hg
  have hf1 : MemLp f 1 volume := by rw [hf]; exact hu1.ofReal
  have hf2 : MemLp f 2 volume := by rw [hf]; exact hu2.ofReal
  have hg1 : MemLp g 1 volume := by rw [hg]; exact hv1.ofReal
  have hg2 : MemLp g 2 volume := by rw [hg]; exact hv2.ofReal
  have hC := kinFT_parseval_c hf1 hf2 hg1 hg2
  have hint := integrable_inner_kinFT hf1 hf2 hg1 hg2
  -- real parts: `(∫ p, φ p).re = ∫ p, (φ p).re` via `Complex.reCLM`
  have hre_int : (∫ p : Submission.BoseGases.kcE3,
        (inner ℂ (Submission.BoseGases.kinFT f p) (Submission.BoseGases.kinFT g p)).re)
      = (∫ p : Submission.BoseGases.kcE3,
        inner ℂ (Submission.BoseGases.kinFT f p) (Submission.BoseGases.kinFT g p)).re := by
    simpa [Complex.reCLM_apply] using
      (ContinuousLinearMap.integral_comp_comm Complex.reCLM hint)
  -- the position-space pairing of two real functions
  have hx : (∫ x : Submission.BoseGases.kcE3, inner ℂ (f x) (g x))
      = ((∫ x : Submission.BoseGases.kcE3, u x * v x : ℝ) : ℂ) := by
    rw [hf, hg]
    exact integral_inner_ofReal_eq u v
  -- take real parts of the complex Parseval identity
  have hre : (∫ p : Submission.BoseGases.kcE3,
        (inner ℂ (Submission.BoseGases.kinFT f p) (Submission.BoseGases.kinFT g p)).re)
      = (2 * Real.pi) ^ 3 * ∫ x : Submission.BoseGases.kcE3, u x * v x := by
    have h := congrArg Complex.re hC
    rw [← hre_int, hx] at h
    rw [Complex.re_ofReal_mul] at h
    simpa using h
  -- replace the sesquilinear integrand by the product `conj (kinFT f p) * kinFT g p`
  have hleft : (∫ p : Submission.BoseGases.kcE3,
        (inner ℂ (Submission.BoseGases.kinFT f p) (Submission.BoseGases.kinFT g p)).re)
      = ∫ p : Submission.BoseGases.kcE3, (starRingEnd ℂ (Submission.BoseGases.kinFT f p)
          * Submission.BoseGases.kinFT g p).re := by
    apply integral_congr_ae
    filter_upwards with p
    rw [RCLike.inner_apply, mul_comm]
  rw [hleft] at hre
  have hne : (2 * Real.pi) ^ 3 ≠ 0 := pow_ne_zero 3 (by positivity)
  rw [hre, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Work.BoseFixB3.HighMassAux
