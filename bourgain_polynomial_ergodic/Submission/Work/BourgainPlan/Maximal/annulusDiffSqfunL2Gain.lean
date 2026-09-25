import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusDiffSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusSquare_l2
import Submission.Work.BourgainPlan.Maximal.annulusSquareLpDefs
import Submission.Commons.Analysis.Fourier.fourierInv_sub_pt

/-!
# The concrete `L²` gain of the *difference* annulus square function

`annulusDiffSqfunDecay.lean` proves MST's `(eq:51)` (the decay in the base scale) from two endpoint
bounds: a `j`-uniform `L^q` bound and an `L²` bound with gain `2^{-δ|j|}`.  The `L²` gain itself is
the *Plancherel computation for the difference family*: by `l2_multiplier_sum_square_function`,

`∫⁻ x, (annulusDiffSqfun b b' j f x)² = ∫⁻ x, ∑'_n ‖(b'(j+n) - b(j+n))(x) 𝓕f(x)‖²`

and the pointwise symbol gain `∑'_n ‖b'(j+n)ξ - b(j+n)ξ‖² ≤ B² 2^{-2δ|j|}` turns this into
`B² 2^{-2δ|j|} ∫⁻ ‖f‖²`.  This module supplies exactly that (`annulusDiffSqfun_l2_gain`), the last
concrete brick of MST's `(eq:51)`.

The route: the family `D m = b' m - b m` is again smooth with compact support (though *not* an
`AnnulusSymbolSmooth` family, since its support is not confined to a single annulus), so

* `integrable_symbol`, `symbolDiff_hasCompactSupport`, `symbolDiff_contDiff`,
  `symbolDiff_memLp_top` — the structural facts about `D`;
* `annulusK_sub_apply` — `𝓕⁻` commutes with the difference (`fourierInv_sub_pt`);
* `annulusConv_sub_of_memLp` — `annulusConv` commutes with the difference on `L^p` inputs;
* `symbolDiffK_fourier`, `annulusConvDiff_ae_eq_multiplier` — the kernel `𝓕⁻ (D m)` has Fourier
  transform `D m`, so its convolution is the multiplier with symbol `D m`;
* `annulusDiffSqfun_l2_gain` — the assembly.
-/

open MeasureTheory Filter
open scoped ENNReal BigOperators FourierTransform
open Commons.Analysis.Fourier

namespace Work.BourgainPlan.Maximal

/-- **The symbol of an annulus family is integrable** (smooth, compactly supported). -/
lemma integrable_symbol (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) :
    Integrable (b m) volume :=
  (hsmooth m).continuous.integrable_of_hasCompactSupport (annulusK_hasCompactSupport b hb m)

/-- **The difference of two annulus symbols has compact support.** -/
lemma symbolDiff_hasCompactSupport (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b') (m : ℤ) :
    HasCompactSupport (fun ξ : ℝ => b' m ξ - b m ξ) :=
  (annulusK_hasCompactSupport b' hb' m).sub (annulusK_hasCompactSupport b hb m)

/-- **The difference of two annulus symbols is smooth.** -/
lemma symbolDiff_contDiff (b b' : ℤ → ℝ → ℂ)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m)) (m : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : ℝ => b' m ξ - b m ξ) :=
  (hsmooth' m).sub (hsmooth m)

/-- **The difference of two annulus symbols is essentially bounded.** -/
lemma symbolDiff_memLp_top (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m)) (m : ℤ) :
    MemLp (fun ξ : ℝ => b' m ξ - b m ξ) ⊤ volume :=
  (annulusSymbol_memLp_top b' hb' hsmooth' m).sub (annulusSymbol_memLp_top b hb hsmooth m)

/-- **`𝓕⁻` commutes with the difference** (`fourierInv_sub_pt`, with integrability of the
symbols). -/
lemma annulusK_sub_apply (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m)) (m : ℤ) (x : ℝ) :
    annulusK (fun m ξ => b' m ξ - b m ξ) m x = annulusK b' m x - annulusK b m x :=
  Commons.Analysis.Fourier.fourierInv_sub_pt (integrable_symbol b' hb' hsmooth' m)
    (integrable_symbol b hb hsmooth m) x

/-- **`annulusConv` commutes with the difference of the symbol families**, on `L^p` inputs. -/
lemma annulusConv_sub_of_memLp (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m))
    (m : ℤ) {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal p) volume) (x : ℝ) :
    annulusConv (fun m ξ => b' m ξ - b m ξ) m f x
      = annulusConv b' m f x - annulusConv b m f x := by
  have h1 := integrable_annulusK_mul b hb hsmooth m hp hf x
  have h2 := integrable_annulusK_mul b' hb' hsmooth' m hp hf x
  simp only [annulusConv]
  rw [show (fun y : ℝ => annulusK (fun m ξ => b' m ξ - b m ξ) m (x - y) * f y)
      = fun y : ℝ => annulusK b' m (x - y) * f y - annulusK b m (x - y) * f y from by
    funext y
    rw [annulusK_sub_apply b b' hb hb' hsmooth hsmooth' m (x - y)]
    ring]
  exact MeasureTheory.integral_sub h2 h1

/-- **Fourier inversion for the difference family**: `𝓕 (𝓕⁻ (b' m - b m)) = b' m - b m`. -/
lemma symbolDiffK_fourier (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m)) (m : ℤ) :
    FourierTransform.fourier (annulusK (fun m ξ => b' m ξ - b m ξ) m)
      = fun ξ => b' m ξ - b m ξ := by
  have hcs := symbolDiff_hasCompactSupport b b' hb hb' m
  have hcd := symbolDiff_contDiff b b' hsmooth hsmooth' m
  have hint : Integrable (fun ξ : ℝ => b' m ξ - b m ξ) volume :=
    hcd.continuous.integrable_of_hasCompactSupport hcs
  have hFint : Integrable (𝓕 (fun ξ : ℝ => b' m ξ - b m ξ)) volume :=
    Commons.Analysis.Fourier.integrable_fourier_of_contDiff_hasCompactSupport hcs hcd
  have hmain := Continuous.fourier_fourierInv_eq (f := fun ξ : ℝ => b' m ξ - b m ξ)
    hcd.continuous hint hFint
  simpa [annulusK] using hmain

/-- **The multiplier with symbol `𝓕 K` is, a.e., the convolution with `K`** — the difference-free
half of `multiplier_eq_convolution_ae`, in the orientation used below. -/
lemma convIntegral_ae_eq_multiplier (K : ℝ → ℂ) (hK : Integrable K)
    (hm : MemLp (fun ξ : ℝ => 𝓕 K ξ) ⊤ (volume : Measure ℝ)) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun x : ℝ => ∫ y : ℝ, K (x - y) * (g : ℝ → ℂ) y)
      =ᵐ[volume] (fun x : ℝ =>
        (BoundaryLayer.multiplier (fun ξ : ℝ => 𝓕 K ξ) hm g : ℝ → ℂ) x) := by
  have key := Commons.Analysis.Fourier.multiplier_eq_convolution_ae K hK hm g
  refine (Filter.EventuallyEq.of_eq ?_).trans key
  funext x
  exact integral_congr_ae (Filter.EventuallyEq.of_eq (funext fun y => mul_comm _ _))

/-- **The convolution with the difference kernel is the multiplier with the difference symbol.**
This is `annulusConv_ae_eq_multiplier` for the family `D m = b' m - b m`, which is *not* an
`AnnulusSymbolSmooth` family (its support is not confined to one annulus) but is smooth with compact
support, which is all the argument uses. -/
lemma annulusConvDiff_ae_eq_multiplier (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m)) (m : ℤ)
    (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun x : ℝ => annulusConv (fun m ξ => b' m ξ - b m ξ) m (g : ℝ → ℂ) x)
      =ᵐ[volume] (fun x : ℝ =>
        (BoundaryLayer.multiplier (fun ξ : ℝ => b' m ξ - b m ξ)
          (symbolDiff_memLp_top b b' hb hb' hsmooth hsmooth' m) g : ℝ → ℂ) x) := by
  have hk : Integrable (annulusK (fun m ξ => b' m ξ - b m ξ) m) volume :=
    Commons.Analysis.Fourier.integrable_fourierInv_of_contDiff_hasCompactSupport
      (symbolDiff_hasCompactSupport b b' hb hb' m) (symbolDiff_contDiff b b' hsmooth hsmooth' m)
  have hsym : (fun ξ : ℝ => 𝓕 (annulusK (fun m ξ => b' m ξ - b m ξ) m) ξ)
      = fun ξ : ℝ => b' m ξ - b m ξ := by
    funext ξ
    exact congrFun (symbolDiffK_fourier b b' hb hb' hsmooth hsmooth' m) ξ
  have hm : MemLp (fun ξ : ℝ => 𝓕 (annulusK (fun m ξ => b' m ξ - b m ξ) m) ξ) ⊤ volume := by
    rw [hsym]
    exact symbolDiff_memLp_top b b' hb hb' hsmooth hsmooth' m
  have hmain := convIntegral_ae_eq_multiplier (annulusK (fun m ξ => b' m ξ - b m ξ) m) hk hm g
  have hcongr : (fun x : ℝ =>
        (BoundaryLayer.multiplier (fun ξ : ℝ => 𝓕 (annulusK (fun m ξ => b' m ξ - b m ξ) m) ξ) hm g
          : ℝ → ℂ) x)
      = fun x : ℝ => (BoundaryLayer.multiplier (fun ξ : ℝ => b' m ξ - b m ξ)
          (symbolDiff_memLp_top b b' hb hb' hsmooth hsmooth' m) g : ℝ → ℂ) x := by
    funext x
    rw [boundaryLayer_multiplier_congr hm (symbolDiff_memLp_top b b' hb hb' hsmooth hsmooth' m)
      hsym g]
  have hfun : (fun x : ℝ => ∫ y : ℝ, annulusK (fun m ξ => b' m ξ - b m ξ) m (x - y)
        * (g : ℝ → ℂ) y)
      = fun x : ℝ => annulusConv (fun m ξ => b' m ξ - b m ξ) m (g : ℝ → ℂ) x := rfl
  rw [hfun] at hmain
  exact hmain.trans (Filter.EventuallyEq.of_eq hcongr)

/-! ## The `L²` gain -/

/-- **The `p`-th power of the `eLpNorm` at a positive real exponent, for `ℝ≥0∞`-valued
functions.**  (The `ℝ≥0∞`-valued companion of `annulusELpNorm_rpow_eq_lintegral`.) -/
lemma eLpNorm_rpow_self {p : ℝ} (hp : 0 < p) {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g volume) :
    (eLpNorm g (ENNReal.ofReal p) volume) ^ p = ∫⁻ x, g x ^ p := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hg.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le,
    ← ENNReal.rpow_mul, show (1 : ℝ) / p * p = 1 by
      rw [one_div, inv_mul_cancel₀ hp.ne'], ENNReal.rpow_one]
  refine lintegral_congr (fun x => ?_)
  rw [enorm_eq_self]

/-- **The `p`-th power of the `eLpNorm` at `p = 2`, for `ℝ≥0∞`-valued functions.** -/
lemma eLpNormTwo_rpow_self {g : ℝ → ℝ≥0∞} (hg : AEMeasurable g volume) :
    (eLpNorm g (2 : ℝ≥0∞) volume) ^ (2 : ℝ) = ∫⁻ x, g x ^ (2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [h2, MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)) ENNReal.ofReal_ne_top hg.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.rpow_mul, show (1 : ℝ) / 2 * 2 = 1 by norm_num, ENNReal.rpow_one]
  refine lintegral_congr (fun x => ?_)
  rw [enorm_eq_self]

/-- **The `p`-th power of the `eLpNorm` at `p = 2`, for `ℂ`-valued functions.** -/
lemma eLpNorm_two_rpow_eq_lintegral {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) :
    (eLpNorm g (2 : ℝ≥0∞) volume) ^ (2 : ℝ) = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [h2]
  exact annulusELpNorm_rpow_eq_lintegral (p := 2) (by norm_num) hg

/-- **The concrete `L²` gain of the difference annulus square function** (the `h2bd` hypothesis of
`annulusDiffSqfun_decay`).  If the symbols of the two families satisfy the pointwise gain

`∑'_n ‖b'(j+n)ξ - b(j+n)ξ‖² ≤ B² 2^{-2δ|j|}`,

then the difference square function is `L²`-bounded with the gain `2^{-δ|j|}`, uniformly in `j`. -/
theorem annulusDiffSqfun_l2_gain (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m))
    {δ B : ℝ} (hB : 0 ≤ B)
    (hgain : ∀ (j : ℤ) (ξ : ℝ), ∑' n : ℤ, ‖b' (j + n) ξ - b (j + n) ξ‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal (B ^ 2 * (2 : ℝ) ^ (-(2 * δ) * |(j : ℝ)|))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (f : ℝ → ℂ), MemLp f (2 : ℝ≥0∞) volume →
      eLpNorm (annulusDiffSqfun b b' j f) (2 : ℝ≥0∞) volume
        ≤ ENNReal.ofReal (C * B * (2 : ℝ) ^ (-(δ) * |(j : ℝ)|))
          * eLpNorm f (2 : ℝ≥0∞) volume := by
  refine ⟨1, one_pos, fun j f hf => ?_⟩
  let D : ℤ → ℝ → ℂ := fun m ξ => b' m ξ - b m ξ
  have hDmem : ∀ n : ℤ, MemLp (D n) ⊤ volume := fun n =>
    symbolDiff_memLp_top b b' hb hb' hsmooth hsmooth' n
  set A : ℝ := B * (2 : ℝ) ^ (-(δ) * |(j : ℝ)|) with hAdef
  have hA_nn : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg hB (Real.rpow_nonneg (by norm_num) _)
  have htwo : ((2 : ℝ) ^ (-(δ) * |(j : ℝ)|)) ^ 2 = (2 : ℝ) ^ (-(2 * δ) * |(j : ℝ)|) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(δ) * |(j : ℝ)|)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hA2 : A ^ 2 = B ^ 2 * (2 : ℝ) ^ (-(2 * δ) * |(j : ℝ)|) := by
    rw [hAdef, mul_pow, htwo]
  set g : Lp ℂ 2 (volume : Measure ℝ) := hf.toLp f with hgdef
  have hgcoe : (g : ℝ → ℂ) =ᵐ[volume] f := hf.coeFn_toLp
  have hf2 : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by
    rw [show (ENNReal.ofReal (2 : ℝ)) = (2 : ℝ≥0∞) from by norm_num]
    exact hf
  -- the difference square function is the square function of `D`
  have hdiff : annulusDiffSqfun b b' j f = annulusSqfun D j f := by
    funext x
    simp only [annulusDiffSqfun, annulusSqfun]
    congr 1
    refine tsum_congr (fun n => ?_)
    rw [annulusConv_sub_of_memLp b b' hb hb' hsmooth hsmooth' (j + n) (p := 2) (by norm_num) hf2 x]
  -- squared form of the LHS
  have hsq : (eLpNorm (annulusDiffSqfun b b' j f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ)
      = ∫⁻ x, ∑' n : ℤ, ‖annulusConv D (j + n) f x‖ₑ ^ (2 : ℝ) := by
    rw [hdiff, eLpNormTwo_rpow_self (aemeasurable_annulusSqfun D j hf.aestronglyMeasurable.aemeasurable)]
    refine lintegral_congr (fun x => ?_)
    rw [annulusSqfun, ← ENNReal.rpow_mul, show (1 : ℝ) / 2 * 2 = 1 by norm_num,
      ENNReal.rpow_one]
  -- replacing `f` by its `L²` class
  have hconvg : ∀ m : ℤ, (fun x : ℝ => annulusConv D m f x)
      = (fun x : ℝ => annulusConv D m (g : ℝ → ℂ) x) := by
    intro m
    funext x
    simp only [annulusConv]
    exact integral_congr_ae (by filter_upwards [hgcoe] with y hy; rw [hy])
  have hstep1 : ∫⁻ x, ∑' n : ℤ, ‖annulusConv D (j + n) f x‖ₑ ^ (2 : ℝ)
      = ∫⁻ x, ∑' n : ℤ, ‖annulusConv D (j + n) (g : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) := by
    refine lintegral_congr_ae (Filter.EventuallyEq.of_eq ?_)
    funext x
    exact tsum_congr (fun n => by rw [congrFun (hconvg (j + n)) x])
  -- replacing the convolutions by the multipliers
  have hstep2 : ∫⁻ x, ∑' n : ℤ, ‖annulusConv D (j + n) (g : ℝ → ℂ) x‖ₑ ^ (2 : ℝ)
      = ∫⁻ x, ∑' n : ℤ,
          ‖(BoundaryLayer.multiplier (D (j + n)) (hDmem (j + n)) g : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) := by
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ x ∂volume, ∀ n : ℤ, annulusConv D (j + n) (g : ℝ → ℂ) x
        = (BoundaryLayer.multiplier (D (j + n)) (hDmem (j + n)) g : ℝ → ℂ) x :=
      ae_all_iff.mpr (fun n => annulusConvDiff_ae_eq_multiplier b b' hb hb' hsmooth hsmooth' (j + n) g)
    filter_upwards [hae] with x hx
    exact tsum_congr (fun n => by rw [hx n])
  -- the multiplier bound
  have hstep3 : ∫⁻ x, ∑' n : ℤ,
        ‖(BoundaryLayer.multiplier (D (j + n)) (hDmem (j + n)) g : ℝ → ℂ) x‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal (A ^ 2) * ‖g‖ₑ ^ (2 : ℝ) :=
    Commons.Analysis.Fourier.l2_multiplier_sum_square_function (fun n : ℤ => D (j + n))
      (fun n => hDmem (j + n)) g A (fun ξ => by
        rw [hA2]
        exact hgain j ξ)
  -- Plancherel on the input
  have hDg : ‖g‖ₑ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
    rw [BoundaryLayer.lp_enorm_sq_eq_lintegral g]
    refine lintegral_congr_ae ?_
    filter_upwards [hgcoe] with x hx
    rw [hx]
  have hmain : (eLpNorm (annulusDiffSqfun b b' j f) (2 : ℝ≥0∞) volume) ^ (2 : ℝ)
      ≤ (ENNReal.ofReal A * eLpNorm f (2 : ℝ≥0∞) volume) ^ (2 : ℝ) := by
    rw [hsq]
    calc ∫⁻ x, ∑' n : ℤ, ‖annulusConv D (j + n) f x‖ₑ ^ (2 : ℝ)
        = ∫⁻ x, ∑' n : ℤ, ‖annulusConv D (j + n) (g : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) := hstep1
      _ = ∫⁻ x, ∑' n : ℤ,
            ‖(BoundaryLayer.multiplier (D (j + n)) (hDmem (j + n)) g : ℝ → ℂ) x‖ₑ ^ (2 : ℝ) :=
          hstep2
      _ ≤ ENNReal.ofReal (A ^ 2) * ‖g‖ₑ ^ (2 : ℝ) := hstep3
      _ = ENNReal.ofReal (A ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by rw [hDg]
      _ = (ENNReal.ofReal A * eLpNorm f (2 : ℝ≥0∞) volume) ^ (2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
          rw [show (ENNReal.ofReal A) ^ (2 : ℝ) = ENNReal.ofReal (A ^ 2) from by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
            exact (ENNReal.ofReal_pow hA_nn 2).symm]
          rw [← eLpNorm_two_rpow_eq_lintegral (g := f) hf.aestronglyMeasurable]
  have htake := ENNReal.rpow_le_rpow hmain (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.rpow_one] at htake
  refine le_trans htake (le_of_eq ?_)
  rw [one_mul, ← hAdef]

/-- The `h2bd` form of `annulusDiffSqfun_l2_gain`, with the exponent written `ENNReal.ofReal 2`
(the shape in which `annulusDiffSqfun_decay` consumes it). -/
theorem annulusDiffSqfun_l2_gain_ofReal (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m))
    {δ B : ℝ} (hB : 0 ≤ B)
    (hgain : ∀ (j : ℤ) (ξ : ℝ), ∑' n : ℤ, ‖b' (j + n) ξ - b (j + n) ξ‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal (B ^ 2 * (2 : ℝ) ^ (-(2 * δ) * |(j : ℝ)|))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (f : ℝ → ℂ), MemLp f (ENNReal.ofReal 2) volume →
      eLpNorm (annulusDiffSqfun b b' j f) (ENNReal.ofReal 2) volume
        ≤ ENNReal.ofReal (C * B * (2 : ℝ) ^ (-(δ) * |(j : ℝ)|))
          * eLpNorm f (ENNReal.ofReal 2) volume := by
  obtain ⟨C, hC, H⟩ := annulusDiffSqfun_l2_gain b b' hb hb' hsmooth hsmooth' hB hgain
  refine ⟨C, hC, fun j f hf => ?_⟩
  have h2 : (ENNReal.ofReal (2 : ℝ)) = (2 : ℝ≥0∞) := by norm_num
  rw [h2] at hf ⊢
  exact H j f hf


/-- **Monotonicity of `eLpNorm` for `ℝ≥0∞`-valued functions** (the `enorm` version
`eLpNorm_mono` is unavailable: `ℝ≥0∞` is not a `NormedAddCommGroup`). -/
lemma eLpNorm_le_of_le {p : ℝ} (hp : 0 < p) {f g : ℝ → ℝ≥0∞} (hf : AEMeasurable f volume)
    (h : ∀ x : ℝ, f x ≤ g x) :
    eLpNorm f (ENNReal.ofReal p) volume ≤ eLpNorm g (ENNReal.ofReal p) volume := by
  by_cases hg : AEMeasurable g volume
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable (fun h' => hg h'.aemeasurable)]; exact le_top
  rw [← ENNReal.rpow_le_rpow_iff hp, eLpNorm_rpow_self hp hf, eLpNorm_rpow_self hp hg]
  exact lintegral_mono (fun x => ENNReal.rpow_le_rpow (h x) hp.le)

/-- **The `sup`-in-scale form of the `L²` gain** (the scalar shape of MST's `(eq:199)`): under the
same pointwise symbol gain, the maximal function `⨆_n ‖(K'_{j+n} − K_{j+n}) * f‖` obeys the `L²`
bound with the gain `2^{-δ|j|}`.  Immediate from `annulusDiffSqfun_l2_gain_ofReal` because the
`ℓ²` sum dominates each term. -/
theorem annulusDiffSup_l2_gain (b b' : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hb' : AnnulusSymbolSmooth b')
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (hsmooth' : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b' m))
    {δ B : ℝ} (hB : 0 ≤ B)
    (hgain : ∀ (j : ℤ) (ξ : ℝ), ∑' n : ℤ, ‖b' (j + n) ξ - b (j + n) ξ‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal (B ^ 2 * (2 : ℝ) ^ (-(2 * δ) * |(j : ℝ)|))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (f : ℝ → ℂ), MemLp f (ENNReal.ofReal 2) volume →
      eLpNorm (fun x : ℝ => ⨆ n : ℤ,
          ‖annulusConv (fun m ξ => b' m ξ - b m ξ) (j + n) f x‖ₑ) (ENNReal.ofReal 2) volume
        ≤ ENNReal.ofReal (C * B * (2 : ℝ) ^ (-(δ) * |(j : ℝ)|))
          * eLpNorm f (ENNReal.ofReal 2) volume := by
  obtain ⟨C, hC, H⟩ := annulusDiffSqfun_l2_gain_ofReal b b' hb hb' hsmooth hsmooth' hB hgain
  refine ⟨C, hC, fun j f hf => ?_⟩
  have hsupm : AEMeasurable (fun x : ℝ => ⨆ n : ℤ,
      ‖annulusConv (fun m ξ => b' m ξ - b m ξ) (j + n) f x‖ₑ) volume :=
    AEMeasurable.iSup fun n => (aemeasurable_annulusConv _ _ hf.aestronglyMeasurable.aemeasurable
      (aemeasurable_annulusK _ _)).enorm
  refine le_trans (eLpNorm_le_of_le (p := 2) (by norm_num) hsupm fun x => ?_) (H j f hf)
  refine iSup_le (fun n : ℤ => ?_)
  have h : (‖annulusConv (fun m ξ => b' m ξ - b m ξ) (j + n) f x‖ₑ ^ (2 : ℝ))
      ≤ ∑' m : ℤ, ‖annulusConv (fun m ξ => b' m ξ - b m ξ) (j + m) f x‖ₑ ^ (2 : ℝ) :=
    ENNReal.le_tsum (f := fun m : ℤ =>
      ‖annulusConv (fun m ξ => b' m ξ - b m ξ) (j + m) f x‖ₑ ^ (2 : ℝ)) n
  calc ‖annulusConv (fun m ξ => b' m ξ - b m ξ) (j + n) f x‖ₑ
      = (‖annulusConv (fun m ξ => b' m ξ - b m ξ) (j + n) f x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
    _ ≤ (∑' m : ℤ, ‖annulusConv (fun m ξ => b' m ξ - b m ξ) (j + m) f x‖ₑ ^ (2 : ℝ))
          ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = annulusDiffSqfun b b' j f x := by
        rw [annulusDiffSqfun]
        congr 1
        exact tsum_congr (fun m => by
          rw [annulusConv_sub_of_memLp b b' hb hb' hsmooth hsmooth' (j + m) (p := 2)
            (by norm_num) hf x])

end Work.BourgainPlan.Maximal
