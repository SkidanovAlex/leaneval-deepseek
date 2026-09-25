import Mathlib
import Submission.Work.Beltrami.diffQuot_fourier_norm
import Submission.Work.Beltrami.memLp_poly_mul_fourier
import Submission.Work.Beltrami.integrable_of_fourier_moments
import Submission.Work.Beltrami.contDiff_fourierInv_of_moments
import Submission.Work.Beltrami.ae_eq_fourierInv_of_fourier_eq

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff FourierTransform

/-- **Sobolev-type smoothness criterion via `L²` bounds on iterated forward differences.**
If `u : ℂ → ℂ` is continuous and every iterated forward difference of `u` satisfies the sharp `L²`
bound `‖Δ_h^N u‖_{L²} ≤ C N * ‖h‖^N` (for every `N : ℕ` and every `h : ℂ`), then `u` is smooth.

Sketch: applying the hypothesis with `h = t • e` (`e = 1` or `e = Complex.I`, `t → 0`) and using
`𝓕(Δ_h^N u) = (e^{i⟨h,ξ⟩} - 1)^N 𝓕u` together with Fatou gives that `ξ_1^N 𝓕u` and `ξ_2^N 𝓕u` are
square integrable for every `N`, i.e. every polynomial multiple of `𝓕u` is in `L²`. Hence `u ∈ H^s`
for every `s`, and writing `𝓕u = (1+‖ξ‖²)^{-s/2} · w` with `w ∈ L²` and using that
`K_s := 𝓕⁻[(1+‖·‖²)^{-s/2}]` is a Schwartz function gives `u = K_s * 𝓕⁻w`; convolution of a Schwartz
function with an `L²` function is `C^∞` (differentiate under the integral using the rapid decay of
`K_s`), whence `ContDiff ℝ ∞ u`. -/
theorem contDiff_of_diffQuot_L2 {u : ℂ → ℂ} (hu : Continuous u) (C : ℕ → ℝ)
    (h : ∀ (N : ℕ) (h : ℂ), eLpNorm ((fun f : ℂ → ℂ => (fun x => f (x + h) - f x))^[N] u) 2 volume
        ≤ ENNReal.ofReal (C N * ‖h‖ ^ N)) :
    ContDiff ℝ ∞ u := by
  -- `u ∈ L²`, from the hypothesis at `N = 0`.
  have hL2 : MemLp u 2 volume := by
    have h0 := h 0 0
    rw [Function.iterate_zero] at h0
    simp only [id_eq, norm_zero, pow_zero, mul_one] at h0
    exact memLp_iff.mpr (lt_of_le_of_lt h0 ENNReal.ofReal_lt_top)
  set V : Lp ℂ 2 volume := 𝓕 (hL2.toLp u) with hV
  -- The sharp Fourier-side bounds.
  have hbound := diffQuot_fourier_norm hL2 C h
  -- Every polynomial multiple of `𝓕u` is in `L²`.
  have hmom : ∀ N : ℕ, MemLp (fun ξ : ℂ => (1 + ‖ξ‖ ^ 2) ^ N * V ξ) 2 volume :=
    memLp_poly_mul_fourier C (fun N hh => by rw [hV]; exact hbound N hh)
  -- The inverse Fourier transform of `V` is smooth ...
  have hw : ContDiff ℝ ∞ (fun x : ℂ => ∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ) :=
    contDiff_fourierInv_of_moments hmom
  -- ... and equals `u` almost everywhere.
  have hint : Integrable (fun ξ : ℂ => V ξ) := integrable_of_fourier_moments hmom
  have hae : u =ᵐ[volume] (fun x : ℂ => ∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ) :=
    ae_eq_fourierInv_of_fourier_eq hL2 hV.symm hint
  have heq : u = fun x : ℂ => ∫ ξ : ℂ, 𝐞 (inner ℝ ξ x) • V ξ :=
    (Continuous.ae_eq_iff_eq (μ := volume) hu hw.continuous).mp hae
  rw [heq]
  exact hw

end Work.Beltrami
