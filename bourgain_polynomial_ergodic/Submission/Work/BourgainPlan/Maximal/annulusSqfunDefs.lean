import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSymbolDefs
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

/-!
# The annulus-localised square function: vocabulary and the frontier statements of rung (ii-e)

`WINDOW_WEAK_TYPE_STATUS_S10.md` §9--§10 fix the shape of rung (ii) of MST's `(eq:52)` input 2: the
weak-`(1,1)` bound for the vector-valued square function

  `S_j f (x) = (∑'_n ‖(K_{j+n} * f)(x)‖²)^{1/2}`,   `K_m = 𝓕⁻ (b m)`,

for an annulus-symbol family `b` (`AnnulusSymbolSmooth b`, plus `C^∞` smoothness of each member),
with a constant uniform in `j`.  This file fixes the notation (`annulusK`, `annulusConv`,
`annulusSqfun`) and the three predicates that the rung is proved through:

* `AnnulusSquareL2 b` — the `L²` bound of the square function (piece (ii-d) of §9, = the
  bounded-overlap half of `anisoAnnulus_facts` plus Plancherel);
* `AnnulusBadPartBound b` — the Calderón--Zygmund *bad part* estimate (pièce (ii-e) step 4 of §10):
  for a mean-zero `L¹` function `h` living in the dyadic cell `dyCell n k`, the square function of
  `h` is controlled outside the doubled cell, with the *sharp* constant uniform in `j`, `n`, `k`;
* `AnnulusSquareWeakType b` — the conclusion of rung (ii).

The three are related by a single Calderón--Zygmund assembly (`annulusSquareWeakType_of_parts`),
which is the content of step (ii-e) of `WINDOW_WEAK_TYPE_STATUS_S10.md` §10.  The two analytic inputs
are the *only* deep ones: the `L²` bound and the bad-part estimate.  (The linearisation (ii-c)
`sqrt_sum_sq_eq_iSup_dot` is *not* needed: because the operator is scalar-valued into `ℓ²`, the
good/bad split is handled by the triangle inequality of the `ℓ²` norm alone.)

Notation and conventions match the four already-proved inputs of the rung:
`annulusLocalizedKernelHormander` (piece (i)), `annulusKernel_size` (ii-a),
`annulusKernel_translation` (ii-b) and `sqrt_sum_sq_eq_iSup_dot` (ii-c); the two-sided scale sum
`∑' n : ℤ` (with the base scale `j`) is the one used throughout, since the difference
`K_m(z - y) - K_m(z)` decays for both signs of the scale.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.Maximal (hlMax)

/-- The annulus-localised kernel at scale `m`: the inverse Fourier transform of the symbol `b m`. -/
noncomputable def annulusK (b : ℤ → ℝ → ℂ) (m : ℤ) : ℝ → ℂ :=
  FourierTransform.fourierInv (b m)

/-- The convolution `(K_m * f)(x) = ∫ y, K_m (x - y) * f y` of the annulus kernel with `f`.  This
is the explicit Bochner integral (Mathlib's `MeasureTheory.convolution` would require the
`ContinuousLinearMap.mul` bookkeeping, and its argument order is the same but its normalisation
has to be unfolded at every use). -/
noncomputable def annulusConv (b : ℤ → ℝ → ℂ) (m : ℤ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, annulusK b m (x - y) * f y

/-- **The annulus square function** at base scale `j`:
`annulusSqfun b j f x = (∑'_n ‖(K_{j+n} * f)(x)‖²)^{1/2}`. -/
noncomputable def annulusSqfun (b : ℤ → ℝ → ℂ) (j : ℤ) (f : ℝ → ℂ) : ℝ → ℝ≥0∞ :=
  fun x => (∑' n : ℤ, ‖annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)

/-- **Piece (ii-d)**: the `L²` bound of the annulus square function,
`∫⁻ x, (∑'_n ‖(K_{j+n} * f)(x)‖²) ≤ C ∫⁻ x, ‖f x‖²`, with `C` uniform in `j ∈ ℤ` (the sum is over
*all* scales, and finiteness comes from the bounded overlap of the frequency annuli
`1/2 < |2^m ξ| < 2`). -/
def AnnulusSquareL2 (b : ℤ → ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (f : ℝ → ℂ), MemLp f 1 volume → MemLp f 2 volume →
    ∫⁻ x, ∑' n : ℤ, ‖annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)

/-- **Step 4 of (ii-e)**: the Calderón--Zygmund bad-part estimate.  For a mean-zero `L¹` function `h`
supported in the dyadic cell `dyCell n k` (= `[k·2^n, (k+1)·2^n)`, whose left endpoint is the pivot
`k·2^n` used in the kernel estimate `annulusKernel_translation`), the square function of `h` is
controlled outside the interval `{|x - k·2^n| > 2^{n+1}}` by the `L¹` mass of `h`, with a constant
uniform in `j`, `n`, `k`.  The two features that make it work are the mean-zero identity
(`K * h(x) = ∫ (K(x-y) - K(x - k2^n)) h y dy`, so only the *difference* of the kernel appears) and
the sharp translation bound (ii-b), which integrates to a constant against `2^n/|x - k2^n|²`. -/
def AnnulusBadPartBound (b : ℤ → ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (n : ℤ) (k : ℤ) (h : ℝ → ℂ),
    MemLp h 1 volume →
    (∀ x : ℝ, x ∉ dyCell n k → h x = 0) →
    (∫ x in dyCell n k, h x) = 0 →
    ∫⁻ x in {x : ℝ | 2 * (2 : ℝ) ^ n < |x - (k : ℝ) * (2 : ℝ) ^ n|}, annulusSqfun b j h x
      ≤ ENNReal.ofReal C * ∫⁻ x, ‖h x‖ₑ

/-- **Rung (ii)**: the weak-`(1,1)` bound for the annulus square function, with a constant uniform
in the base scale `j`.  This is MST's `(eq:52)` input 2, i.e. the Littlewood--Paley square-function
weak-type estimate for the localised family `S_{j+n}`. -/
def AnnulusSquareWeakType (b : ℤ → ℝ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (f : ℝ → ℂ), MemLp f 1 volume → ∀ lam : ℝ, 0 < lam →
    volume {x : ℝ | ENNReal.ofReal lam < annulusSqfun b j f x}
      ≤ ENNReal.ofReal (C / lam) * ∫⁻ x, ‖f x‖ₑ

end Work.BourgainPlan.Maximal
