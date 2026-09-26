/-
# Section 5 of CKMRV: the status of the two recurrences of Proposition 5.1

CKMRV Proposition 5.1 asserts the two identities
`F₂|^τ_{d/2}(T-I)² = -F₁|^τ_{d/2}(T-I)²` and `F₂|^τ_{d/2}S(T-I)² = 0` for the kernel transform
`F₂(τ,r) = 4 sin²(πr²/2) ∫_0^∞ K(τ,it)e^{-πr²t}dt` and `F₁ = e^{πiτr²}`.  They are stated in
this workspace as the hypotheses `h5a`, `h5b` of
`Work.Kernels.satisfiesThm31_of_analysis`.  This file records their exact status for the
*projective* (total Bochner integral) reading of `Work.Kernels.kernelTransform`:

* `Work.Residues.T2op_gaussTerm` computes `T2op (gaussTerm · r)`:
  `= -4 e^{πir²(τ+1)} sin²(πr²/2)`, which is *not* zero;
* `Work.Asymptotics.T2op_kernelTransform` shows that the integral itself has vanishing
  `(T-I)²`-defect (`T2op (kernelTransform K · r) = 0`, the pointwise kernel identity of
  Theorem 4.9(2) integrated against the Gaussian).  Hence
  `Work.Residues.h5a_false` : **`h5a` is false** for `K = Kfun logLambda d` as literally
  stated (for every `r` with `sin(πr²/2) ≠ 0` and every `τ` at which the contour integrand is
  integrable), and `Work.Kernels.satisfiesThm31_of_analysis` cannot be applied to
  `(Fgen K, Ftgen K̂)` with `h5a` supplied from the kernel.
  The paper's `F₂` is not this integral: it is the *analytic continuation* of the integral past
  `Re τ = ±1` (CKMRV Proposition 4.6 and (matchF2sharp)), which differs from the integral by
  the residue term `4 e^{πir²(τ-1)} sin²(πr²/2)`; see also `Work.Asymptotics.Obstruction` for
  the companion obstruction (the contour is not even free of poles on `Re τ = 1`).

* Consequently the two recurrences must be stated for the *corrected* function
  `F₂ + G`, where `G` encodes the continuation.  `Work.Residues.T2op_kernelTransform_add` and
  `Work.Residues.slash_Kfun_kernelTransform_add` show that the two recurrences are stable under
  adding such a correction: if `T2op G = -T2op (gaussTerm · r)` and
  `slash (d/2) (S(T-I)²) G = 0`, then `F₂ + G` satisfies both of the paper's identities.  The
  missing analytic input is precisely the continuation `G = F₂ - F₂^♯` of CKMRV Proposition 4.6.

* `Work.Residues.slash_Kfun_kernelTransform_eq_zero` (in `Work.Residues.Section5`) is the
  unconditional, linearity-only half of `h5b`, and
  `Work.Residues.slash_Kfun_kernelTransform` is `h5b` in the form asked for by
  `Work.Kernels.Section5Pack`, modulo the Bochner integrability of the three contour
  integrands -- which holds exactly on the contours that carry no pole (see
  `Work.Asymptotics.Obstruction`; the hypothesis is *false* on the translates of the imaginary
  axis, where the integral takes the junk value `0`).
-/
import Mathlib
import Submission.Work.Residues.T2op_gaussTerm
import Submission.Work.Residues.Section5
import Submission.Work.Kernels.KernelEquations
import Submission.Work.Asymptotics.T2op_kernelTransform
import Submission.Work.Asymptotics.Basic

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix MeasureTheory
open scoped MatrixGroups Manifold
open Filter
open scoped Topology

namespace Work.Residues

open Work.Kernels

/-- The integrand `t ↦ K(σ,it) e^{-πr²t}` of the contour integral (5.2), at a fixed point `σ`
of `ℍ`: this is the function whose Bochner integrability the recurrences of Proposition 5.1
require, and it is the integrand of `Work.Kernels.kernelTransform`. -/
def contourIntegrand (ℓ : LogLambdaData) (d : ℕ) (r : ℝ) (σ : ℍ) : ℝ → ℂ :=
  fun t => Kaxis (Kfun ℓ d) σ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))

/-- **`h5a` of CKMRV Proposition 5.1 is false as literally stated.**  For the projective
contour integral `F₂^♯ = kernelTransform (Kfun ℓ d) · r` (which is what
`Work.Kernels.Fgen` uses) one has `T2op F₂^♯ = 0`, while
`-T2op (gaussTerm · r) = 4 e^{πir²(τ+1)} sin²(πr²/2) ≠ 0` whenever `sin(πr²/2) ≠ 0` and the
contour integrands at `τ`, `τ+1`, `τ+2` are Bochner integrable. -/
theorem h5a_false (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ) (τ : ℍ)
    (hs : Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ≠ 0)
    (h0 : IntegrableOn (contourIntegrand ℓ d r τ) (Set.Ioi 0))
    (h1 : IntegrableOn (contourIntegrand ℓ d r ((1 : ℝ) +ᵥ τ)) (Set.Ioi 0))
    (h2 : IntegrableOn (contourIntegrand ℓ d r ((2 : ℝ) +ᵥ τ)) (Set.Ioi 0)) :
    T2op (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r)
      ≠ - T2op (fun σ : ℍ => gaussTerm σ r) := by
  intro hcontra
  have hk : T2op (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) τ = 0 :=
    Work.Asymptotics.T2op_kernelTransform ℓ d hd r τ h0 h1 h2
  have hval : T2op (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) τ
      = (- T2op (fun σ : ℍ => gaussTerm σ r)) τ := by rw [hcontra]
  rw [hk, Pi.neg_apply, T2op_gaussTerm] at hval
  have hg : gaussTerm ((1 : ℝ) +ᵥ τ) r ≠ 0 := by
    rw [gaussTerm]; exact Complex.exp_ne_zero _
  have hsin : Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hs
  have hzero : (0 : ℂ) = 4 * gaussTerm ((1 : ℝ) +ᵥ τ) r
      * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2 := by
    rw [show -(-4 * gaussTerm ((1 : ℝ) +ᵥ τ) r
        * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2)
      = 4 * gaussTerm ((1 : ℝ) +ᵥ τ) r
        * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2 by ring] at hval
    exact hval
  exact mul_ne_zero (mul_ne_zero (by norm_num) hg) hsin hzero.symm

/-- **The `(T-I)²`-recurrence is stable under adding a correction.**  If `G` satisfies the
paper's first recurrence (`T2op G = -T2op (gaussTerm · r)`, the condition that CKMRV's
continuation `G = F₂ - F₂^♯` satisfies by construction) and the contour integrands are
Bochner integrable, then the corrected kernel transform `F₂^♯ + G` satisfies it too.  This is
the interface through which the missing analytic continuation of CKMRV Proposition 4.6 enters
`Work.Kernels.satisfiesThm31_of_analysis`. -/
theorem T2op_kernelTransform_add (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    (G : ℍ → ℂ)
    (hint : ∀ σ : ℍ, IntegrableOn (contourIntegrand ℓ d r σ) (Set.Ioi 0))
    (hG : T2op G = - T2op (fun σ : ℍ => gaussTerm σ r)) :
    T2op (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r + G σ)
      = - T2op (fun σ : ℍ => gaussTerm σ r) := by
  have hk : T2op (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) = 0 := by
    ext τ
    exact Work.Asymptotics.T2op_kernelTransform ℓ d hd r τ
      (hint τ) (hint ((1 : ℝ) +ᵥ τ)) (hint ((2 : ℝ) +ᵥ τ))
  rw [T2op_add', hk, zero_add, hG]

/-- **The `S(T-I)²`-recurrence is stable under adding a correction.**  If `G` satisfies the
paper's second recurrence (`slash (d/2) (S(T-I)²) G = 0`) and the contour integrands are
Bochner integrable, then the corrected kernel transform `F₂^♯ + G` satisfies it too. -/
theorem slash_Kfun_kernelTransform_add (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) (G : ℍ → ℂ) (τ : ℍ)
    (hint : ∀ γ ∈ (R_S * (R_T - 1) ^ 2).coeff.support,
      IntegrableOn (contourIntegrand ℓ d r (γ • τ)) (Set.Ioi 0))
    (hG : slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2) G = 0) :
    slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2)
      (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r + G σ) τ = 0 := by
  rw [show (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r + G σ)
      = (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) + G from rfl]
  rw [Work.Kernels.slash_add_F, Pi.add_apply,
    Work.Residues.slash_Kfun_kernelTransform_eq_zero ℓ d hd r τ (by
      intro γ hγ; exact hint γ hγ),
    zero_add, congr_fun hG τ, Pi.zero_apply]

/-- The sine factor of `h5a` is not identically zero: at `r = 1` it equals `1`. -/
lemma sin_pi_div_two_ne_zero : Complex.sin (Real.pi * (1 : ℂ) ^ 2 / 2) ≠ 0 := by
  have h : Real.pi * (1 : ℂ) ^ 2 / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, ← Complex.ofReal_sin, Real.sin_pi_div_two]
  norm_num

/-- **The refutation of `h5a` at `r = 1`** (`sin(π/2) = 1`), the case in which the paper's
first recurrence reads `F₂|^τ_{d/2}(T-I)² = 4 e^{πi(τ+1)}`. -/
theorem h5a_false_one (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ)
    (h0 : IntegrableOn (contourIntegrand ℓ d 1 τ) (Set.Ioi 0))
    (h1 : IntegrableOn (contourIntegrand ℓ d 1 ((1 : ℝ) +ᵥ τ)) (Set.Ioi 0))
    (h2 : IntegrableOn (contourIntegrand ℓ d 1 ((2 : ℝ) +ᵥ τ)) (Set.Ioi 0)) :
    T2op (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ 1)
      ≠ - T2op (fun σ : ℍ => gaussTerm σ 1) :=
  h5a_false ℓ d hd 1 τ sin_pi_div_two_ne_zero h0 h1 h2

/-- **`h5b` from the contour-cleanness characterization.**  The single analytic input needed to
remove the integrability hypotheses of `Work.Residues.slash_Kfun_kernelTransform_eq_zero` is the
implication "no pole of `z ↦ K(σ,z)` on the contour implies the contour integrand is
Bochner integrable" (the direction assembled in `Work.Asymptotics.Instances`/`Divisor` from the
flat/tail/divisor estimates).  Given it, `h5b` holds at every `τ` whose three contour points
`S•τ`, `S T•τ`, `S T²•τ` are contour-clean.  (The cleanness hypotheses cannot be dropped: at
`τ = i` the point `S•i = i` is clean, while `S T•i` and `S T²•i` carry the poles
`z = i` of `ζ ↦ K(S T•i, ζ)` and `ζ ↦ K(S T²•i, ζ)` respectively, so the projective identity
collapses to the single surviving term.) -/
theorem slash_Kfun_kernelTransform_of_contourClean (ℓ : LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) (τ : ℍ)
    (hβ : ∀ σ : ℍ, Work.Asymptotics.ContourClean (Kfun ℓ d) σ →
      IntegrableOn (contourIntegrand ℓ d r σ) (Set.Ioi 0))
    (hclean : ∀ γ ∈ (R_S * (R_T - 1) ^ 2).coeff.support,
      Work.Asymptotics.ContourClean (Kfun ℓ d) (γ • τ)) :
    slash ((d : ℤ) / 2) (R_S * (R_T - 1) ^ 2)
      (fun σ : ℍ => kernelTransform (Kfun ℓ d) σ r) τ = 0 :=
  slash_Kfun_kernelTransform_eq_zero ℓ d hd r τ
    (fun γ hγ => hβ (γ • τ) (hclean γ hγ))

end Work.Residues
