import Mathlib
import Submission.Work.GM.Affine.WinMass_fejer_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.WinMass_basic

/-!
# Vocabulary for the near-correlation bound `Work.GM.Affine.near_correlation_le_Gfun`

The target lemma bounds the Fejér-weighted near integral

  `∫_{|x| ≤ K T/M₂} ‖Bsum f M₂ x‖² · fejerK M₃ x`

by `C K² M₂ ∫ f̃(u) Gfun(u) du`, where `f̃ = smoothed psiSmooth T f` is GM's smoothed test
function.  The route is the classical one for GM §9:

* on `|x| ≤ K T/M₂` the Fourier transform `Ĥ = Bsum f M₂` is comparable to the Fourier
  transform of the *smoothed profile* `A = H ⋆ ρ`, `ρ(t) = s⁻¹ ψ(t/s)`, `s = M₂/(2KT)`
  (because `ψ̂` is bounded below by `1/2` on `|y| ≤ 1/2`);
* the Fejér kernel has nonnegative Fourier coefficients `1 - |k|/N` (`N = fejerN M₃`), so
  the weighted integral is a sum of correlations `∫ A(v) A(v+k) dv` over `k ∈ [-N, N]`;
* the correlations vanish for `|k| > ⌊2 C₀ M₂⌋` (support of `A`), and are dominated by the
  smoothed correlations `∫ f̃(u) f̃((m u + k)/m') du`, which is what `Gfun` sums.

This file only contains the definitions (and the immediate sign lemmas) used by all the
pieces of the argument.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The smoothing scale `s = M₂/(2 K T)` of GM §9. -/
def smScale (K T M₂ : ℝ) : ℝ := M₂ / (2 * K * T)

/-- The smoothed profile `A(v) = ∫ u, Hprof f M₂ (v - s u) ψ(u) du`, `s = smScale K T M₂`.

It is the convolution of `Hprof f M₂` with the probability density `ρ(t) = s⁻¹ ψ(t/s)`,
written as an integral against `ψ` after the change of variables `t = s u`. -/
def Afun (f : ℝ → ℝ) (M₂ K T : ℝ) (v : ℝ) : ℝ :=
  ∫ u : ℝ, Hprof f M₂ (v - smScale K T M₂ * u) * psiSmooth u

/-- The `m`-th smoothed piece of the profile: `g_m(u) = ∫ f(u') (m/s) ψ(m (u-u')/s) du'`.

`Afun` satisfies `A v = Σ_{m ∈ R2 M₂} g_m (v/m)`, and each `g_m` is dominated by `4K f̃`
(`rho_kernel_domination`). -/
def gm (f : ℝ → ℝ) (s : ℝ) (m : ℤ) (u : ℝ) : ℝ :=
  ∫ u' : ℝ, f u' * (((m : ℝ) / s) * psiSmooth ((m : ℝ) * (u - u') / s))

lemma smScale_pos {K T M₂ : ℝ} (hK : 0 < K) (hT : 0 < T) (hM₂ : 0 < M₂) :
    0 < smScale K T M₂ := by
  rw [smScale]; positivity

lemma gm_nonneg {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) {s : ℝ} (hs : 0 < s)
    {m : ℤ} (hm : 0 ≤ (m : ℝ)) (u : ℝ) : 0 ≤ gm f s m u := by
  rw [gm]
  refine integral_nonneg fun u' => ?_
  have h1 : 0 ≤ (m : ℝ) / s := div_nonneg hm hs.le
  exact mul_nonneg (hf u') (mul_nonneg h1 (psiSmooth_nonneg _))

lemma Afun_nonneg {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (M₂ K T v : ℝ) :
    0 ≤ Afun f M₂ K T v := by
  rw [Afun]
  refine integral_nonneg fun u => ?_
  have hH : 0 ≤ Hprof f M₂ (v - smScale K T M₂ * u) :=
    Finset.sum_nonneg fun m _ => hf _
  exact mul_nonneg hH (psiSmooth_nonneg _)

lemma Hprof_nonneg {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (M₂ u : ℝ) : 0 ≤ Hprof f M₂ u :=
  Finset.sum_nonneg fun m _ => hf _

end

end Work.GM.Affine

namespace Work.GM.Affine

noncomputable section

/-- The smoothed correlation term `∫ u, f̃(u) · f̃((m·u + k)/m')` that `Gfun` sums. -/
def NTerm (T : ℝ) (f : ℝ → ℝ) (m m' : ℤ) (k : ℝ) : ℝ :=
  ∫ u : ℝ, smoothed psiSmooth T f u * smoothed psiSmooth T f (((m : ℝ) * u + k) / (m' : ℝ))

end

end Work.GM.Affine
