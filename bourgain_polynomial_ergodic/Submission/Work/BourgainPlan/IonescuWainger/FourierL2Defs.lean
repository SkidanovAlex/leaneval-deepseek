import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc

/-!
# The `ℓ²(ℤ) ≅ L²(𝕋)` dictionary for the band-limited major-arc systems

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4
(Lemma `ortho`(ii)(iii) and Theorem `ortho-apply`), see `ARC_ARITH_STATUS.md` / `PLAN.md` (the
"band-limited / `ℓ²(ℤ)`-with-arcs lane").

The results of `FreqArc.lean` / `OrthoAssembly.lean` / `BandLimited.lean` are stated for *finitely
supported* and for *absolutely summable* `ℤ`-functions.  The major-arc systems of the
Ionescu–Wainger theorem are instead **band-limited**: `f_α ∈ ℓ²(ℤ)` with Fourier support in a small
arc around `α`.  For that setting one needs the unitary identification
`ℓ²(ℤ) ≅ L²(𝕋)`, `h ↦ 𝓕h = Σ_n h n · e_n`, provided by Mathlib's Hilbert basis `fourierBasis`.

This file fixes the vocabulary:

* `ftLp h hh` — the Fourier transform of the square-summable sequence `h`, an element of
  `Lp ℂ 2 haarAddCircle` (`= repr.symm ⟨h, hh⟩`), i.e. the `L²` class of the (formal) series
  `Σ_n h n · e^{2πi n ·}`;
* `HasFreqSupport h hh E` — the statement that the Fourier transform of `h` vanishes a.e. outside
  `E`, i.e. that `h` is band-limited with frequency support in `E`.

The companion lemmas (the coefficient formula `h m = ⟪e_m, ftLp h hh⟫`, the isometry
`‖ftLp h hh‖² = Σ_n ‖h n‖²`, and the bridge `ftLp h =ᵐ discFourier h` for `h ∈ ℓ¹`) are stated
in the sibling files.
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- The **Fourier transform** of a square-summable sequence `h : ℤ → ℂ`, as an element of
`L²(𝕋) = Lp ℂ 2 haarAddCircle`: the unique `L²` function whose `n`-th Fourier coefficient is `h n`,
i.e. the class of the formal series `Σ_n h n · e^{2πi n ·}`.

This is Mathlib's Hilbert-basis expansion along `fourierBasis : HilbertBasis ℤ ℂ (Lp ℂ 2
AddCircle.haarAddCircle)`. -/
noncomputable def ftLp (h : ℤ → ℂ) (hh : Memℓp h 2) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) :=
  (fourierBasis (T := 1)).repr.symm ⟨h, hh⟩

/-- `h : ℤ → ℂ` is **band-limited with frequency support in `E`**: its Fourier transform (the `L²`
function `ftLp h hh`) vanishes almost everywhere outside `E`. -/
def HasFreqSupport (h : ℤ → ℂ) (hh : Memℓp h 2) (E : Set Circle) : Prop :=
  ∀ᵐ θ ∂(AddCircle.haarAddCircle (T := 1)), θ ∉ E → (ftLp h hh : Circle → ℂ) θ = 0

/-- The **modulation** of a sequence by a character: `m ↦ ρ m · e^{2πi m θ}`.  Its Fourier
transform is the translate `η ↦ 𝓕ρ (η + θ)` of that of `ρ` (same file, `hasFreqSupport_modSeq`),
which is the mechanism by which the band-limited orthogonality induction shifts the frequency
supports. -/
noncomputable def modSeq (ρ : ℤ → ℂ) (θ : Circle) : ℤ → ℂ := fun m => ρ m * fourier m θ

/-- `‖e^{2πi m θ}‖ = 1`. -/
theorem norm_fourier_apply' (m : ℤ) (θ : Circle) : ‖fourier m θ‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- A modulation of a square-summable sequence is square-summable. -/
theorem memℓp_modSeq {ρ : ℤ → ℂ} (hρ : Memℓp ρ 2) (θ : Circle) : Memℓp (modSeq ρ θ) 2 := by
  have hρ' : Summable (fun m : ℤ => ‖ρ m‖ ^ (2 : ℝ)) := by simpa [Memℓp] using hρ
  refine memℓp_gen ?_
  have hm : (fun m : ℤ => ‖modSeq ρ θ m‖ ^ (2 : ℝ)) = fun m : ℤ => ‖ρ m‖ ^ (2 : ℝ) := by
    funext m
    simp only [modSeq, norm_mul, norm_fourier_apply', mul_one]
  rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) from ENNReal.toReal_ofNat 2, hm]
  exact hρ'

end Work.BourgainPlan.IonescuWainger
