import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusSymbol_tsum_sq_le
import Submission.Work.BourgainPlan.Maximal.annulusK_memLp
import Submission.Work.Analysis.Fourier.lintegral_convolution_sq_eq

/-!
# Piece (ii-d): the `L²` bound of the annulus square function

This file proves `annulusSquare_l2`, the `L²` half of rung (ii) of MST's `(eq:52)` input 2
(cf. `WINDOW_WEAK_TYPE_STATUS_S10.md` §9): for an annulus symbol family `b`
(`AnnulusSymbolSmooth b`, with each `b m` moreover `C^∞`) there is a constant `C > 0`, **uniform
in the base scale `j`**, with

  `∫⁻ x, ∑'_n ‖(K_{j+n} * f)(x)‖² ≤ C ∫⁻ x, ‖f x‖²`,   `K_m = 𝓕⁻ (b m)`.

The mathematics is Littlewood--Paley: the annuli `1/2 < |2^m ξ| < 2` overlap boundedly, so for
every frequency `ξ` at most two of the symbols `b (j+n) ξ` are non-zero
(`annulusSymbol_tsum_sq_le`).  Hence

  `∑_n ‖K_{j+n} * f‖₂² = ∑_n ∫ ‖b (j+n) ξ‖² ‖𝓕 f ξ‖² = ∫ (∑_n ‖b (j+n) ξ‖²) ‖𝓕 f ξ‖²
                        ≤ C ∫ ‖𝓕 f ξ‖² = C ‖f‖₂²`,

with `C` independent of `j`; the middle identity is Plancherel applied to each convolution
(`𝓕 (K_m * f) = b m · 𝓕 f`).

In the formalisation the per-scale Plancherel is obtained from the already-proven
`multiplier_eq_convolution_ae`: the kernel `K_m = 𝓕⁻ (b m)` is integrable (its Fourier transform
`𝓕 (𝓕⁻ (b m)) = b m` by the inversion formula, and `b m` is smooth with compact support), and
convolving with it is the multiplier operator with symbol `b m`.  The bounded-overlap sum is then
the already-proven `l2_multiplier_sum_square_function`, which had already absorbed the
Tonelli/measurability bookkeeping for a countable multiplier family.

The supporting facts about the kernel `K_m` are the following three lemmas, all consequences of
`b m` being a smooth compactly supported function.
-/

open MeasureTheory Filter
open scoped ENNReal BigOperators FourierTransform
open Commons.Analysis.Fourier

namespace Work.BourgainPlan.Maximal

/-- **Fourier inversion for the annulus kernel.**  `b m` is smooth and compactly supported
(hence integrable with integrable Fourier transform), so `𝓕 (𝓕⁻ (b m)) = b m`; and
`annulusK b m` *is* `𝓕⁻ (b m)`. -/
lemma annulusK_fourier_eq (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) :
    FourierTransform.fourier (annulusK b m) = b m := by
  have hcs : HasCompactSupport (b m) := annulusK_hasCompactSupport b hb m
  have hint : Integrable (b m) volume :=
    (hsmooth m).continuous.integrable_of_hasCompactSupport hcs
  have hFint : Integrable (𝓕 (b m)) volume :=
    Commons.Analysis.Fourier.integrable_fourier_of_contDiff_hasCompactSupport hcs (hsmooth m)
  have hmain := Continuous.fourier_fourierInv_eq (f := b m) (hsmooth m).continuous hint hFint
  simpa [annulusK] using hmain

/-- **The annulus kernel is integrable.**  The inverse Fourier transform of a smooth compactly
supported function is integrable. -/
lemma integrable_annulusK (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) :
    Integrable (annulusK b m) volume := by
  have h := Commons.Analysis.Fourier.integrable_fourierInv_of_contDiff_hasCompactSupport
    (annulusK_hasCompactSupport b hb m) (hsmooth m)
  simpa [annulusK] using h

/-- **The symbols are essentially bounded.**  This is the case `k = 0` of the derivative bound of
`AnnulusSymbolSmooth`, and it is what makes the symbol a bounded multiplier. -/
lemma annulusSymbol_memLp_top (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) :
    MemLp (b m) ⊤ volume := by
  obtain ⟨C, _hC, hCb⟩ := hb.2 0
  refine memLp_top_of_bound (hsmooth m).continuous.aestronglyMeasurable C ?_
  filter_upwards with ξ
  have h := hCb m ξ
  simpa using h

/-- The multiplier operator depends only on the symbol (the proof of essential boundedness is
irrelevant by proof irrelevance). -/
lemma boundaryLayer_multiplier_congr {m m' : ℝ → ℂ} (hm : MemLp m ⊤ volume)
    (hm' : MemLp m' ⊤ volume) (h : m = m') (f : Lp ℂ 2 volume) :
    BoundaryLayer.multiplier m hm f = BoundaryLayer.multiplier m' hm' f := by
  subst h
  exact congrArg (fun hh => BoundaryLayer.multiplier m hh f) (Subsingleton.elim hm hm')

/-- **The convolution with the annulus kernel is the multiplier with the symbol `b m`.**  This is
`multiplier_eq_convolution_ae` applied to the kernel `K_m = 𝓕⁻ (b m)`, whose Fourier transform is
`b m` by `annulusK_fourier_eq`. -/
lemma annulusConv_ae_eq_multiplier (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) (g : Lp ℂ 2 volume) :
    (fun x => annulusConv b m (g : ℝ → ℂ) x)
      =ᵐ[volume] (fun x => BoundaryLayer.multiplier (b m)
        (annulusSymbol_memLp_top b hb hsmooth m) g x) := by
  have hk : Integrable (annulusK b m) volume := integrable_annulusK b hb hsmooth m
  have hsym : (fun ξ => 𝓕 (annulusK b m) ξ) = b m := by
    funext ξ
    exact congrFun (annulusK_fourier_eq b hb hsmooth m) ξ
  have hm : MemLp (fun ξ => 𝓕 (annulusK b m) ξ) ⊤ volume := by
    rw [hsym]
    exact annulusSymbol_memLp_top b hb hsmooth m
  have key := Commons.Analysis.Fourier.multiplier_eq_convolution_ae (annulusK b m) hk hm g
  have hfun : (fun x => annulusConv b m (g : ℝ → ℂ) x)
      = (fun x => ∫ y, (g : ℝ → ℂ) y * annulusK b m (x - y)) := by
    funext x
    exact integral_congr_ae (Filter.EventuallyEq.of_eq (funext (fun y => mul_comm _ _)))
  rw [hfun]
  refine key.trans ?_
  filter_upwards with x
  rw [boundaryLayer_multiplier_congr hm (annulusSymbol_memLp_top b hb hsmooth m) hsym g]

/-- **Piece (ii-d).**  The `L²` bound of the annulus square function, with a constant uniform in
the base scale `j`. -/
theorem annulusSquare_l2 (b : ℤ → ℝ → ℂ)
    (hb : Work.BourgainPlan.Maximal.AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) :
    Work.BourgainPlan.Maximal.AnnulusSquareL2 b := by
  obtain ⟨C₁, _hC₁nn, _hsup, htsum⟩ := annulusSymbol_tsum_sq_le b hb
  have hA2 : Real.sqrt (C₁ + 1) ^ 2 = C₁ + 1 := Real.sq_sqrt (by linarith)
  refine ⟨C₁ + 1, by linarith, fun j f _hf1 hf2 => ?_⟩
  -- put `f` in `L²` as an `Lp` element
  set g : Lp ℂ 2 volume := hf2.toLp f with hgdef
  have hgcoe : (g : ℝ → ℂ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hconv_eq : ∀ m : ℤ, (fun x => annulusConv b m f x)
      = (fun x => annulusConv b m (g : ℝ → ℂ) x) := by
    intro m
    funext x
    simp only [annulusConv]
    exact integral_congr_ae (by filter_upwards [hgcoe] with y hy; rw [hy])
  -- replace each scale by the multiplier with symbol `b (j+n)`
  have hB : ∫⁻ x, ∑' n : ℤ, ‖annulusConv b (j + n) (g : ℝ → ℂ) x‖ₑ ^ (2:ℝ)
      = ∫⁻ x, ∑' n : ℤ, ‖(BoundaryLayer.multiplier (b (j + n))
          (annulusSymbol_memLp_top b hb hsmooth (j+n)) g : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ x ∂volume, ∀ n : ℤ,
        annulusConv b (j + n) (g : ℝ → ℂ) x
          = (BoundaryLayer.multiplier (b (j + n))
              (annulusSymbol_memLp_top b hb hsmooth (j+n)) g : ℝ → ℂ) x :=
      ae_all_iff.mpr (fun n => annulusConv_ae_eq_multiplier b hb hsmooth (j+n) g)
    filter_upwards [hae] with x hx
    exact tsum_congr (fun n => by rw [hx n])
  -- the square function of a bounded-overlap multiplier family is bounded in `L²`
  have hC : ∫⁻ x, ∑' n : ℤ, ‖(BoundaryLayer.multiplier (b (j + n))
        (annulusSymbol_memLp_top b hb hsmooth (j+n)) g : ℝ → ℂ) x‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal (C₁ + 1) * ‖g‖ₑ ^ (2:ℝ) := by
    have hmain := Commons.Analysis.Fourier.l2_multiplier_sum_square_function
      (fun n : ℤ => b (j + n))
      (fun n => annulusSymbol_memLp_top b hb hsmooth (j+n)) g (Real.sqrt (C₁+1)) ?_
    · rwa [hA2] at hmain
    · intro ξ
      refine le_trans (htsum j ξ) ?_
      rw [hA2]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Plancherel turns `‖g‖²` into the integral of `‖f‖²`
  have hD : ‖g‖ₑ ^ (2:ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    rw [BoundaryLayer.lp_enorm_sq_eq_lintegral g]
    refine lintegral_congr_ae ?_
    filter_upwards [hgcoe] with x hx
    rw [hx]
  calc ∫⁻ x, ∑' n : ℤ, ‖annulusConv b (j + n) f x‖ₑ ^ (2:ℝ)
      = ∫⁻ x, ∑' n : ℤ, ‖annulusConv b (j + n) (g : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := by
        refine lintegral_congr_ae ?_
        filter_upwards with x
        exact tsum_congr (fun n => by rw [congrFun (hconv_eq (j+n)) x])
    _ = ∫⁻ x, ∑' n : ℤ, ‖(BoundaryLayer.multiplier (b (j + n))
          (annulusSymbol_memLp_top b hb hsmooth (j+n)) g : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := hB
    _ ≤ ENNReal.ofReal (C₁ + 1) * ‖g‖ₑ ^ (2:ℝ) := hC
    _ = ENNReal.ofReal (C₁ + 1) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by rw [hD]

end Work.BourgainPlan.Maximal
