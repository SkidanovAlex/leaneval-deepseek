/-
# `MSW` — the single-torsion sampling (de Leeuw) reduction: definitions

This module contains the fixed objects used in the proof of
`Work.KMTAreas.MSW_single_torsion`: the sampling cutoff `χ`, its inverse Fourier transform `K`,
the "Shannon interpolation" operator attached to a finitely supported sequence, the trigonometric
polynomial of a sequence, and the modulation of a sequence by a character.

The mathematical content of the reduction is:

* the IW projection at the single torsion set `(1/Q)ℤ/ℤ` with a symbol supported in the arc
  `[-2^k,2^k]`, `2^k · 2Q ≤ 1`, is the *periodisation* (de Leeuw transfer) of the continuous
  multiplier with the same symbol;
* the transfer is proved at the level of the duality pairing: for finitely supported `f, g` on `ℤ`
  the pairing `∑_n (T_Φ f)(n) conj (g n)` equals the `L²(ℝ)` pairing
  `⟪T_φ (I f), I g⟫`, where `I` is the Shannon interpolation operator (`mswInterp`) whose symbol is
  the cutoff `χ`; the `L^p` bound then follows from Hölder and from the `ℓ^p(ℤ) → L^p(ℝ)` bound for
  `I` (`mswInterp_eLpNorm_le`, proved in `MSW_interp_bound`).
-/
import Mathlib
import Submission.Work.KMTAreas.iw_family
import Submission.Work.KMTContract.periodizeCoeEqTsum

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.KMTAreas

/-! ## The fixed cutoff `χ` and its inverse Fourier transform `K` -/

/-- A fixed smooth bump function which is `1` on `[-2,2]` and vanishes outside `[-3,3]`. -/
noncomputable def mswBump : ContDiffBump (0 : ℝ) := ⟨2, 3, by norm_num, by norm_num⟩

theorem mswBump_rIn : mswBump.rIn = 2 := rfl

theorem mswBump_rOut : mswBump.rOut = 3 := rfl

/-- The cutoff as a `ℂ`-valued function. -/
noncomputable def mswChiFun : ℝ → ℂ := fun x => ((mswBump x : ℝ) : ℂ)

theorem mswChiFun_cs : HasCompactSupport mswChiFun :=
  mswBump.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by norm_num)

theorem mswChiFun_cd : ContDiff ℝ (⊤ : ℕ∞) mswChiFun :=
  Complex.ofRealCLM.contDiff.comp mswBump.contDiff

/-- The fixed cutoff `χ`, as a Schwartz function on `ℝ`: it is `1` on `[-2,2]`, real-valued, and
smooth with compact support. -/
noncomputable def mswChi : SchwartzMap ℝ ℂ := mswChiFun_cs.toSchwartzMap mswChiFun_cd

theorem mswChi_apply (x : ℝ) : mswChi x = mswChiFun x := rfl

theorem mswChi_eq_one {x : ℝ} (hx : |x| ≤ 2) : mswChi x = 1 := by
  show mswChiFun x = 1
  rw [show mswChiFun x = ((mswBump x : ℝ) : ℂ) from rfl,
    ContDiffBump.one_of_mem_closedBall mswBump (by
      rw [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs, mswBump_rIn]; simpa using hx)]
  norm_num

theorem mswChi_real (x : ℝ) : mswChi x = starRingEnd ℂ (mswChi x) := by
  show mswChiFun x = starRingEnd ℂ (mswChiFun x)
  simp [mswChiFun, Complex.conj_ofReal]

/-- The inverse Fourier transform `K = 𝓕⁻χ` of the cutoff: a Schwartz function whose Fourier
transform is exactly `χ`. -/
noncomputable def mswK : SchwartzMap ℝ ℂ := 𝓕⁻ mswChi

theorem mswChi_eq_fourier_mswK : 𝓕 mswK = mswChi := FourierInvPair.fourier_fourierInv_eq mswChi

/-! ## Trigonometric polynomials and the Shannon interpolation operator -/

/-- The trigonometric polynomial on `ℝ` with the coefficients of a finitely supported sequence
`u`: `∑_{m ∈ s} u m · e^{2πi m x}`. -/
noncomputable def mswTrig (s : Finset ℤ) (u : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ m ∈ s, u m * Complex.exp (2 * ↑Real.pi * Complex.I * (m : ℂ) * (x : ℂ))

/-- The same trigonometric polynomial as a function on the frequency circle `ℝ/ℤ`. -/
noncomputable def mswTrigC (s : Finset ℤ) (u : ℤ → ℂ) :
    Work.Analysis.IonescuWainger.Circle → ℂ :=
  ∑ m ∈ s, u m • (fourier m : Work.Analysis.IonescuWainger.Circle → ℂ)

/-- The Shannon interpolation of a finitely supported sequence `u` with the kernel `K`:
`∑_{m ∈ s} u m · K(· + m)`.  Its Fourier transform is `χ · mswTrig s u`, so it is the (unique)
function with Fourier support in `[-2,2]` whose samples are `u`. -/
noncomputable def mswInterp (s : Finset ℤ) (u : ℤ → ℂ) : SchwartzMap ℝ ℂ :=
  ∑ m ∈ s, u m • (mswK.compSubConstCLM ℝ (-(m : ℝ)))

/-- The modulation `u_c(m) = u(m) · e^{2πi m c}` of a sequence.  The trigonometric polynomial of
the modulated sequence is the translate of the trigonometric polynomial of `u`:
`mswTrig s (mswMod c u) x = mswTrig s u (x + c)`. -/
noncomputable def mswMod (c : ℝ) (u : ℤ → ℂ) : ℤ → ℂ :=
  fun m => u m * Complex.exp (2 * ↑Real.pi * Complex.I * (m : ℂ) * (c : ℂ))

end Work.KMTAreas
