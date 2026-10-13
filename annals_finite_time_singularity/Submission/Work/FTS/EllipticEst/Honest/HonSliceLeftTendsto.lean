import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.Honest.HonFirstMoment
import Submission.Work.FTS.EllipticEst.Honest.HonSliceLimitZero
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.moment_relation
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.Endpt.slice_regularity_of_uncurry
import Submission.Work.FTS.EllipticEst.Endpt.Lzero1_slice_mul_integrable
import Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi
import Submission.Work.FTS.EllipticEst.Endpt.integrableOn_fstar_pzIter2
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.AeBasic
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-! ## Slice integrability of `g z · · sinθcos²θ` from the honesty of `g` -/

/-- **Slice integrability of `g z · · sinθcos²θ` from `HkMem α 0 g`.**  If `g` is smooth on the
open quadrant and `g ∈ ℋ⁰`, then for `z > 0` the product `g z · · sinθcos²θ` is integrable on
`Iθ`: `|g z θ · sinθcos²θ| ≤ (g z θ · w(z)/sin(2θ)^{η/2})² + 1` and the right-hand side is
integrable by `HkMem α 0 g` (its `θ`-slice integrand is precisely that square). -/
theorem hon_slice_mul_sinCos2_integrable_of_HkMem {α : ℝ} {g : ℝ → ℝ → ℝ} {z : ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 0 g) (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => g z θ * sg θ) Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hGint : MeasureTheory.IntegrableOn
      (fun θ => (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Iθ := by
    have h0 := hmem.1 z hzI
    refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp [Work.Spaces.HkIntegrand]
  have hC1 : (1 : ℝ) ≤ (z ^ 2)⁻¹ + 1 := by
    have : 0 < (z ^ 2)⁻¹ := by positivity
    linarith
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ => ((z ^ 2)⁻¹ + 1)
        * (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1)
      Iθ :=
    (hGint.const_mul _).add (MeasureTheory.integrableOn_const
      (Work.FTS.EllipticEst.remov.ws_vol_Iθ_ne_top) (by simp))
  refine MeasureTheory.Integrable.mono' hmaj
    ((Work.FTS.EllipticEst.remov.ws_aesm_slice hg hz).mul
      continuous_sinCos2.aestronglyMeasurable) ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h1 := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted (f := fun θ => g z θ) hz hθI
  rw [abs_mul] at h1
  rw [Real.norm_eq_abs, abs_mul]
  have hX : 0 ≤ (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    sq_nonneg _
  have h2 : (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ ((z ^ 2)⁻¹ + 1)
        * (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hC1 hX
  linarith [h1, h2]

/-! ## The moment identity for the source -/

/-- **The angular moment of the source in terms of the moments of `∂_zΨ`, `∂_z²Ψ` and the
slice integral of `Lzero1`.**  From `bslOp α Ψ = F` on the open quadrant, the integrand identity
`F z θ · sinθcos²θ = -(α²z²)·(∂_z²Ψ·sinθcos²θ) - (α(5+α)z)·(∂_zΨ·sinθcos²θ)
+ (Lzero1 (Ψ z ·) θ)·sinθcos²θ` holds a.e. on `Iθ`; rewriting under the integral (no
integrability of `F z · · sinθcos²θ` is needed) and splitting gives the identity. -/
theorem hon_fstar_F_moment {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hEq : ∀ θ : ℝ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (h1 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz Ψ z θ * sg θ) Iθ)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pzIter 2 Ψ z θ * sg θ) Iθ)
    (h3 : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ) Iθ) :
    Work.Elliptic.Fstar F z
      = -(α ^ 2 * z ^ 2) * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z
        - (α * (5 + α) * z) * Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z
        + ∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ := by
  have hI1 : MeasureTheory.IntegrableOn
      (fun θ => -(α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 Ψ z θ * sg θ)) Iθ := h2.const_mul _
  have hI2 : MeasureTheory.IntegrableOn
      (fun θ => -(α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * sg θ)) Iθ := h1.const_mul _
  have hcongr : (∫ θ in Iθ, F z θ * sg θ)
      = ∫ θ in Iθ, (-(α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 Ψ z θ * sg θ)
          + (-(α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * sg θ)
            + Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [← hEq θ hθ.1 hθ.2, Work.Elliptic.bslOp_apply,
      show Work.Elliptic.Lzero Ψ z θ
        = Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ from rfl]
    ring
  rw [Work.Elliptic.Fstar, hcongr]
  rw [MeasureTheory.integral_add
    (f := fun θ => -(α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 Ψ z θ * sg θ))
    (g := fun θ => -(α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * sg θ)
      + Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ) hI1 (hI2.add h3)]
  rw [MeasureTheory.integral_add
    (f := fun θ => -(α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * sg θ))
    (g := fun θ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ) hI2 h3]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  simp only [Work.Elliptic.Fstar]
  ring

/-! ## Slice integrability of the `∂_zΨ`-moment from the equation -/

/-- **The `sinθcos²θ`-moment of `∂_zΨ` is an honest slice integral.**  On the open interval the
equation reads `α(5+α)z·∂_zΨ(z,·) = Lzero1 (Ψ z ·) - α²z²·∂_z²Ψ(z,·) - F(z,·)`; multiplying by
`sinθcos²θ` exhibits `∂_zΨ · sinθcos²θ` as a nonzero constant multiple of a sum of three
integrable functions (the hypotheses `hL1`, `hF`, `hA`). -/
theorem hon_pz_slice_moment_integrable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ)
    (hL1 : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * sg θ) Iθ)
    (hF : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ => F z θ * sg θ) Iθ)
    (hA : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pzIter 2 Ψ z θ * sg θ) Iθ) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz Ψ z θ * sg θ) Iθ := by
  intro z hz
  have hcoef : α * (5 + α) * z ≠ 0 := by
    have h5 : (0 : ℝ) < 5 + α := by linarith [h.hα]
    exact mul_ne_zero (mul_ne_zero (ne_of_gt h.hα) (ne_of_gt h5)) (ne_of_gt hz)
  have hpoint : ∀ᵐ θ ∂(volume.restrict Iθ),
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * sg θ
          - (α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 Ψ z θ * sg θ)
          - (F z θ * sg θ)
        = α * (5 + α) * z * (Work.Spaces.pz Ψ z θ * sg θ) := by
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    have hb := h.eq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at hb
    have hL : Work.Elliptic.Lzero Ψ z θ
        = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
          + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ := by linarith [hb]
    rw [show Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
      = Work.Elliptic.Lzero Ψ z θ from rfl, hL]
    ring
  have hRHS : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * sg θ
        - (α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 Ψ z θ * sg θ)
        - (F z θ * sg θ)) Iθ :=
    ((hL1 z hz).sub ((hA z hz).const_mul _)).sub (hF z hz)
  have hconst : MeasureTheory.IntegrableOn
      (fun θ => α * (5 + α) * z * (Work.Spaces.pz Ψ z θ * sg θ)) Iθ :=
    hRHS.congr hpoint
  refine (hconst.const_mul ((α * (5 + α) * z)⁻¹)).congr ?_
  refine Filter.Eventually.of_forall (fun θ => ?_)
  show (α * (5 + α) * z)⁻¹ * (α * (5 + α) * z * (Work.Spaces.pz Ψ z θ * sg θ))
    = Work.Spaces.pz Ψ z θ * sg θ
  rw [← mul_assoc, inv_mul_cancel₀ hcoef, one_mul]

/-! ## The main theorem -/

/-- **The `θ = 0` endpoint limit of an honest slice vanishes almost everywhere.**  For `Hon α F Ψ` the slice `u = Ψ(z,·)` has limit `0` at `0⁺` for almost every `z > 0` (the *pointwise* statement is NOT forced by `Hon`, see `NOTES_HonSecondMoment.md` §2–4).

Route.  Let `ψ θ = sinθcos²θ` and `Λ(z) := lim_{θ→0⁺}Ψ(z,θ)` (exists for every `z > 0`).  With
`N(z) := ∫_θ ∂_zzΨ(z,θ)·ψ θ dθ` and `G(z) := ∫_θ ∂_zΨ(z,θ)·ψ θ dθ`:

* the moment identity `F_*(F)(z) = -α²z²·N(z) - α(5+α)z·G(z) + ∫_θ Lzero1(Ψ z ·)·ψ θ dθ`
  (`hon_fstar_F_moment`) combines with the slice integration by parts
  `∫_θ Lzero1(Ψ z ·)·ψ = -Λ(z)` (`sliceMoment_eq_neg_limit`) and the two solvability
  conditions (`OrthCond F`, `HonFirstMoment` for `G ≡ 0`) to give `Λ(z) = -α²z²N(z)`;
* `∫_a^b N = 0` for all `0 < a < b`: the differentiated moment relation
  (`Work.FTS.EllipticEst.moment_relation`, applied to `u = ∂_zΨ`, whose `ψ`-integrability is
  `hon_pz_slice_moment_integrable`) says `N` is the derivative of `G`, which vanishes
  identically;
* `N ∈ L¹(a,b)` is `Endpt.integrableOn_fstar_pzIter2`, so `N = 0` a.e. on `(0,∞)`
  (`H2W.PsiSlices.ae_eq_zero_of_forall_intervalIntegral_eq_zero`).

Hence `Λ = -α²z²N = 0` a.e., which — together with the existence of every slice limit — is the
statement; `HonSliceLimitZero` closes the last `z`. -/
theorem HonSliceLeftTendsto (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (h : Hon α F Ψ) :
    Filter.Eventually (fun z => Filter.Tendsto (fun θ => Ψ z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := h.sm
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  -- the slices of `Ψ` are smooth on the open angular interval
  have hslice : ∀ z : ℝ, 0 < z → ∀ n : ℕ,
      ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)) :=
    fun z hz n => Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsm hz n
  -- `F` is smooth on the open quadrant, being `bslOp α Ψ` there
  have hbsl : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hSΨ
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    hbsl.congr (fun p hp => (h.eq p.1 hp.1 p.2 hp.2.1 hp.2.2).symm)
  -- ## (1) the three slice integrands
  have hL1sl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ * sg θ) Iθ := by
    intro z hz
    obtain ⟨C, _hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB hsm h.memB hz
    exact Work.FTS.EllipticEst.Endpt.Lzero1_slice_mul_integrable hsm h.memB hz hC
  have hFsl : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => F z θ * sg θ) Iθ :=
    fun z hz => hon_slice_mul_sinCos2_integrable_of_HkMem hSF h.memF hz
  have hp2sl : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 Ψ z θ * sg θ) Iθ := by
    intro z hz
    have hSg : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      (contDiff_fst.pow 2).contDiffOn.mul (hSΨ.pzIter 2)
    have h := hon_slice_mul_sinCos2_integrable_of_HkMem (g := fun z θ =>
      z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hSg h.memA hz
    refine (h.const_mul ((z ^ 2)⁻¹)).congr ?_
    refine Filter.Eventually.of_forall (fun θ => ?_)
    show (z ^ 2)⁻¹ * ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * sg θ)
      = Work.Spaces.pzIter 2 Ψ z θ * sg θ
    rw [← mul_assoc (z ^ 2)⁻¹ (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (sg θ),
      ← mul_assoc (z ^ 2)⁻¹ (z ^ 2) (Work.Spaces.pzIter 2 Ψ z θ),
      inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hz)), one_mul]
  have hp1sl : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz Ψ z θ * sg θ) Iθ :=
    hon_pz_slice_moment_integrable h hL1sl hFsl hp2sl
  -- ## (2) the differentiated moment relation for `∂_zΨ`
  have hZbox : ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn
      (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz (Work.Spaces.pz Ψ) s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Iθ) :=
    Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi hsm h.memA
  have hmr : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar (Work.Spaces.pz Ψ) b - Work.Elliptic.Fstar (Work.Spaces.pz Ψ) a
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r := by
    intro a b ha hab
    have hrel := Work.FTS.EllipticEst.moment_relation (Work.Spaces.pz Ψ) hSΨ.pz hZbox hp1sl ha hab
    have hIcc : (∫ s in Set.Icc a b, ∫ θ in Iθ,
          Work.Spaces.pz (Work.Spaces.pz Ψ) s θ * sg θ)
        = ∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) s := rfl
    have hconv : (∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) s)
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r := by
      rw [intervalIntegral.integral_of_le hab.le]
      exact (setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))).symm
    rw [hIcc, hconv] at hrel
    linarith
  -- ## (3) the first moment vanishes identically
  have hpoint1 : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z = 0 :=
    fun z hz => by simpa only [Work.Elliptic.Fstar] using HonFirstMoment α F Ψ h z hz
  -- ## (4) the second moment has vanishing interval integrals
  have hzero2 : ∀ s t : ℝ, 0 < s → 0 < t →
      ∫ r in s..t, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r = 0 := by
    intro s t hs ht
    rcases le_total s t with hst | hts
    · rcases lt_or_eq_of_le hst with hlt | heq
      · have hh := hmr s t hs hlt
        rw [hpoint1 t (lt_trans hs hlt), hpoint1 s hs, sub_zero] at hh
        exact hh.symm
      · subst heq; simp
    · rcases lt_or_eq_of_le hts with hlt | heq
      · have hh := hmr t s ht hlt
        rw [hpoint1 s (lt_trans ht hlt), hpoint1 t ht, sub_zero] at hh
        rw [intervalIntegral.integral_symm, ← hh, neg_zero]
      · subst heq; simp
  have hInt2 : ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ)) volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact Work.FTS.EllipticEst.Endpt.integrableOn_fstar_pzIter2 hsm h.memA a b ha hab
  have hae2 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z = 0 :=
    Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_forall_intervalIntegral_eq_zero
      hzero2 hInt2
  -- ## (5) the endpoint of the slice, for a.e. `z`
  filter_upwards [hae2, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hNz hz
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB hsm h.memB hz
  have h2slice : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ := by
    have h2s := Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem (Ψ := Ψ) h.memB hz
    refine h2s.congr ?_
    refine Filter.Eventually.of_forall (fun θ => ?_)
    show Work.Spaces.pthIter 2 Ψ z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [show Work.Spaces.pthIter 2 Ψ z θ
      = deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ from rfl]
  have hmom : (∫ θ in Iθ,
      Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * sg θ) = 0 := by
    have hFmom := hon_fstar_F_moment (z := z)
      (fun θ hθ1 hθ2 => h.eq z hz θ hθ1 hθ2) (hp1sl z hz) (hp2sl z hz) (hL1sl z hz)
    rw [h.orthF z, hNz, hpoint1 z hz] at hFmom
    ring_nf at hFmom
    linarith [hFmom]
  exact HonSliceLimitZero (fun θ => Ψ z θ) (hslice z hz 2) h2slice
    ⟨C, hCpos.le, hC⟩ (hL1sl z hz) hmom

end Work.FTS.EllipticEst.Honest
