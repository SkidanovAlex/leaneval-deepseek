import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.AesmSlicesQ
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.T3Q.HardTheta
import Submission.Work.FTS.H2.T3Q.EasyTheta
import Submission.Work.FTS.H2.T3Q.GoodZPt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T3Q

open scoped Real
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The `D_θ` half of `Transport3`

`Work.FTS.H2.T3Q.HardTheta` (the order-five terms, via the angular integration by parts) and
`Work.FTS.H2.T3Q.EasyTheta` (the pointwise bound of the remainder) give the bound for the
pairing `(f ∂_θ g, g)_{ℋ⁴}` by assembling exactly as in `Work.FTS.H2.T1Q` does for the
`ℋ⁴`-coefficient: split `H4PairInt = T1Easy + T1Hard` pointwise, integrate the pointwise (in `z`)
bound, and use `abs_integral_le_integral_abs` plus `integral_mono_of_nonneg` (which needs no
measurability of the dominated function). -/

/-- **The `D_θ`-pairing of `Transport3` in the interior class.** -/
theorem T3Q_Dth : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.LocData.SmoothQuad f → Work.Spaces.WlInfMem α 4 f →
    Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem α 4 g →
    |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.WlInf α 4 f
        * Work.FTS.Nonlin.Xn α g ^ 2 := by
  obtain ⟨Ch, hCh, hHard⟩ := HardTheta
  obtain ⟨Ce, hCe, hEasy⟩ := EasyTheta
  refine ⟨Ce + 30 * Ch + 1, by positivity, ?_⟩
  intro α f g hα hα1 hsf hWf hsg hHg
  set W : ℝ := Work.Spaces.WlInf α 4 f with hWdef
  have hWnn : 0 ≤ W := by
    rw [hWdef]; exact Work.FTS.H2.WPQ.WlInf_nonneg' hWf
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγs : 0 < Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_pos.mpr hγ
  have hγle : Real.sqrt (Work.Spaces.gam α - 1) ≤ 1 := by
    rw [Real.sqrt_le_one, Work.Spaces.gam_sub_one]; linarith
  have hHkSqnn : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
  -- the pointwise `𝒲^{4,∞}`-bounds on `f` and `D_θf`
  have hf30 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ 30 * W := by
    intro z θ hz hθ0 hθ1
    have hθi : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
    have h := Work.FTS.H2.WPQ.DzIter_le_WlInf (α := α) hsf hWf (b := 0) (by norm_num) hzIz hθi
    simp only [Work.Spaces.DzIter_zero] at h
    rw [hWdef]
    linarith
  have hfd30 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dth f z θ| ≤ 30 * W := by
    intro z θ hz hθ0 hθ1
    have hθi : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
    have hzIz : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
    have h := Work.FTS.H2.WPQ.Mixed_le_WlInf (α := α) hα hsf hWf (a := 1) (b := 0)
      (by norm_num) (by norm_num) hzIz hθi
    have hs0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hθ1, Real.pi_pos])
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have h1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 (by linarith)
    have h2 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
      have : α + Real.sin (2 * θ) ≤ 2 := by linarith
      nlinarith [h1, Real.rpow_nonneg hs0 (α / 5), hs0]
    have h3 : |Work.Spaces.mixed 0 1 f z θ| ≤ 15 * (Work.Spaces.WlInf α 4 f * 2) := by
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hWnn)
        (by norm_num : (0:ℝ) ≤ 15)
    have h4 : (15 : ℝ) * (Work.Spaces.WlInf α 4 f * 2) = 30 * W := by rw [hWdef]; ring
    have hm : Work.Spaces.mixed 0 1 f = Work.Spaces.Dth f := rfl
    rw [hm] at h3
    linarith [h3, le_of_eq h4]
  -- the two ingredients
  obtain ⟨hThInt, hThBd⟩ :=
    hHard α f g (30 * W) hα hα1 hsf hsg hHg hf30 hfd30 (by positivity)
  obtain ⟨hEpt, hEsl⟩ := hEasy α f g hα hα1 hsf hWf hsg hHg
  -- the dominating function of the `z`-integration
  have hdom : Integrable (fun z => Ce * W * (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 g z θ) + |∫ θ in Work.Spaces.Iθ,
        Work.FTS.H2.T1Hard α f g z θ|) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hHg.2.const_mul (Ce * W)).add hThInt
  -- the pointwise-in-`z` bound of the pairing marginal
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ,
        Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g z θ|
        ≤ Ce * W * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
          + |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ| := by
    intro z hz
    by_cases hint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g z θ)
      Work.Spaces.Iθ
    · have hEint : MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.T1Easy α f g z θ)
          Work.Spaces.Iθ := hEsl z hz
      have hTint : MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.T1Hard α f g z θ)
          Work.Spaces.Iθ := by
        have hsub : (fun θ => Work.FTS.H2.T1Hard α f g z θ)
            = fun θ => Work.FTS.H2.H4PairInt α
                (fun z θ => f z θ * Work.Spaces.Dth g z θ) g z θ
              - Work.FTS.H2.T1Easy α f g z θ := by
          funext θ
          rw [Work.FTS.H2.H4PairInt_eq_T1Easy_add_T1Hard α f g z θ]
          ring
        rw [hsub]
        exact hint.sub hEint
      have hsplit : (∫ θ in Work.Spaces.Iθ, Work.FTS.H2.H4PairInt α
            (fun z θ => f z θ * Work.Spaces.Dth g z θ) g z θ)
          = (∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Easy α f g z θ)
            + ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ := by
        rw [show (fun θ => Work.FTS.H2.H4PairInt α
              (fun z θ => f z θ * Work.Spaces.Dth g z θ) g z θ)
            = fun θ => Work.FTS.H2.T1Easy α f g z θ + Work.FTS.H2.T1Hard α f g z θ from
          funext fun θ => Work.FTS.H2.H4PairInt_eq_T1Easy_add_T1Hard α f g z θ]
        exact MeasureTheory.integral_add hEint hTint
      have heasy : |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Easy α f g z θ|
          ≤ Ce * W * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
        refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
        have hmaj : (fun θ => |Work.FTS.H2.T1Easy α f g z θ|)
            ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
            fun θ => Ce * W * Work.Spaces.HkIntegrand α 4 g z θ :=
          MeasureTheory.ae_restrict_of_forall_mem
            (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) (fun θ hθ => by
              rw [hWdef]; exact hEpt z hz θ hθ)
        have hgint : Integrable (fun θ => Ce * W * Work.Spaces.HkIntegrand α 4 g z θ)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          (hHg.1 z hz).const_mul (Ce * W)
        calc (∫ θ in Work.Spaces.Iθ, |Work.FTS.H2.T1Easy α f g z θ|)
            ≤ ∫ θ in Work.Spaces.Iθ, Ce * W * Work.Spaces.HkIntegrand α 4 g z θ :=
              MeasureTheory.integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun θ => abs_nonneg _) hgint hmaj
          _ = Ce * W * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
              rw [MeasureTheory.integral_const_mul]
      calc |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.H4PairInt α
              (fun z θ => f z θ * Work.Spaces.Dth g z θ) g z θ|
          = |(∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Easy α f g z θ)
              + ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ| := by rw [hsplit]
        _ ≤ |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Easy α f g z θ|
              + |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ| := abs_add_le _ _
        _ ≤ Ce * W * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ)
              + |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ| :=
            add_le_add heasy le_rfl
    · rw [MeasureTheory.integral_undef hint, abs_zero]
      exact add_nonneg
        (mul_nonneg (mul_nonneg (le_of_lt hCe) hWnn)
          (MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ))
        (abs_nonneg _)
  -- assemble
  have hstep : |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ (Ce + 30 * Ch) * W * Work.Spaces.HkSq α 4 g := by
    calc |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
        = |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.H4PairInt α
            (fun z θ => f z θ * Work.Spaces.Dth g z θ) g z θ| := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.H4PairInt α
            (fun z θ => f z θ * Work.Spaces.Dth g z θ) g z θ| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ z in Work.Spaces.Iz, (Ce * W * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 g z θ)
          + |∫ θ in Work.Spaces.Iθ, Work.FTS.H2.T1Hard α f g z θ|) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z => abs_nonneg _) hdom
            (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
      _ = Ce * W * Work.Spaces.HkSq α 4 g
          + ∫ z in Work.Spaces.Iz, |∫ θ in Work.Spaces.Iθ,
              Work.FTS.H2.T1Hard α f g z θ| := by
          rw [MeasureTheory.integral_add (hHg.2.const_mul (Ce * W)) hThInt,
            MeasureTheory.integral_const_mul]
          rfl
      _ ≤ Ce * W * Work.Spaces.HkSq α 4 g + Ch * (30 * W) * Work.Spaces.HkSq α 4 g :=
          add_le_add le_rfl hThBd
      _ = (Ce + 30 * Ch) * W * Work.Spaces.HkSq α 4 g := by ring
  -- replace `HkSq` by `Xn ^ 2` and pay `1 / √(γ-1)`
  have hfinal : (Ce + 30 * Ch) * W * Work.Spaces.HkSq α 4 g
      ≤ (Ce + 30 * Ch + 1) / Real.sqrt (Work.Spaces.gam α - 1) * W
        * Work.FTS.Nonlin.Xn α g ^ 2 := by
    rw [Work.FTS.Nonlin.Xn, ← Work.FTS.H2.HkNorm_sq α g]
    have h1 : (1 : ℝ) ≤ 1 / Real.sqrt (Work.Spaces.gam α - 1) := by
      rw [one_le_div hγs]; exact hγle
    have hWS : 0 ≤ W * Work.Spaces.HkNorm α 4 g ^ 2 :=
      mul_nonneg hWnn (sq_nonneg _)
    have hcoef : (Ce + 30 * Ch)
        ≤ (Ce + 30 * Ch + 1) * (1 / Real.sqrt (Work.Spaces.gam α - 1)) := by
      calc (Ce + 30 * Ch) ≤ (Ce + 30 * Ch + 1) * 1 := by linarith
        _ ≤ (Ce + 30 * Ch + 1) * (1 / Real.sqrt (Work.Spaces.gam α - 1)) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
    calc (Ce + 30 * Ch) * W * Work.Spaces.HkNorm α 4 g ^ 2
        = (Ce + 30 * Ch) * (W * Work.Spaces.HkNorm α 4 g ^ 2) := by ring
      _ ≤ ((Ce + 30 * Ch + 1) * (1 / Real.sqrt (Work.Spaces.gam α - 1)))
            * (W * Work.Spaces.HkNorm α 4 g ^ 2) :=
          mul_le_mul_of_nonneg_right hcoef hWS
      _ = (Ce + 30 * Ch + 1) / Real.sqrt (Work.Spaces.gam α - 1) * W
            * Work.Spaces.HkNorm α 4 g ^ 2 := by ring
  linarith [hstep, hfinal]

/-! ## The `D_z` half of `Transport3`

The pairing `(f ∂_z g, g)_{ℋ⁴}` splits pointwise as `H4PairInt = GoodZ + Badz2`, where
`Badz2 = Badz + Mismatchz` is the "exceptional" part (the order-five "all derivatives on `g`"
summands together with the "mismatch" summands, in which every `D_θ`-derivative falls on `f`).
`Work.FTS.H2.T3Q.GoodZPt` bounds `GoodZ` pointwise by `C |f|_𝒲 · HkIntegrand α 4 g`, so only
`Badz2` needs an integration by parts.

**The mismatch family must not be estimated separately.**  Its individual summands are *not*
bounded with an `α`-uniform constant: for `(i,j,b) = (1,3,0)` the block `D_z^4g` has the
natural `η`-weight while the pairing weight is `sin(2θ)^{-γ}`, so the deficit
`sin(2θ)^{-(γ-η)} = sin(2θ)^{-(0.01+α/10)}` is only paid by the factor
`(α+sin2θ)sin(2θ)^{α/5}` of the `𝒲^{4,∞}`-bound on `D_θf` when `α ≥ 1/30` (this is the
`(1,3,0)`-obstruction analysed in `Transport3Aux/MismatchBad/`).  What rescues the estimate is
the cancellation with the *hard* summands of the same slot: after the two integrations by parts
(radial for `Badz`, angular for `Mismatchz`) the two `θ`-integrated pieces combine into a single
`D_θ^i(f·…)`, i.e. a total `θ`-derivative, which is bounded by the slots.  Hence `Badz2` must be
estimated as a single object — the two `Prop`s below are exactly the missing inputs. -/

/-- **The exceptional `D_z`-part of `Transport3` in the interior class** (the single missing
mathematical ingredient of `T3Q`):
`|∫_z∫_θ (Badz + Mismatchz)| ≤ C |f|_{𝒲^{4,∞}} |g|²_{ℋ⁴}`.  This is the `SmoothQuad` version of
`Work.FTS.H2.Transport3Aux.Badz2Bound`; its proof must combine the radial integration by parts
of `Badz` (`Transport3Aux.bad_z_contribution`) with the angular one of `Mismatchz`, using the
`L^∞`-in-`θ`/`L²`-in-`z` trade-off (`Transport3Aux.MzG`) or the exact cancellation just
described, so that the two boundary contributions are controlled together. -/
def Badz2BoundQ : Prop := ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → Work.FTS.LocData.SmoothQuad f → Work.Spaces.WlInfMem α 4 f →
    Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem α 4 g → Work.Spaces.DecayAll 4 g →
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Badz2 α f g z θ|
      ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.HkSq α 4 g

/-- Measurability bookkeeping for the assembly of the `D_z`-half: the radial marginal of
`Badz2` is a.e. strongly measurable (the `SmoothQuad`-analogue of the second conjunct of
`Work.FTS.H2.AesmSlicesQ`), and the `θ`-slices of the good part `H4PairInt - Badz2` are
integrable (they are dominated pointwise by `C|f|_𝒲 HkIntegrand α 4 g`, which is
`θ`-integrable by `HkMem`). -/
def AesmZ : Prop := ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α →
    Work.FTS.LocData.SmoothQuad f → Work.FTS.LocData.SmoothQuad g →
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Badz2 α f g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
        - Work.FTS.H2.Badz2 α f g z θ) Work.Spaces.Iθ)

/-- **`T3Q` from its two halves.**  The `D_θ`-half is `T3Q_Dth` (proved); the `D_z`-half is
assembled here from the pointwise bound `GoodZPt` of the good part and the two inputs
`Badz2BoundQ`, `AesmZ`. -/
theorem T3Q_of_Badz2 (hB2 : Badz2BoundQ) (hA : AesmZ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 → Work.FTS.LocData.SmoothQuad f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.LocData.SmoothQuad g → Work.Spaces.HkMem α 4 g → Work.Spaces.DecayAll 4 g →
      |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        + |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.WlInf α 4 f
        * Work.FTS.Nonlin.Xn α g ^ 2 := by
  obtain ⟨Cd, hCd, hDth⟩ := T3Q_Dth
  obtain ⟨Cb, hCb, hB2⟩ := hB2
  obtain ⟨Cg, hCg, hGood⟩ := GoodZPt
  refine ⟨Cd + (Cb + Cg) + 1, by positivity, ?_⟩
  intro α f g hα hα1 hsf hWf hsg hHg hDec
  set W : ℝ := Work.Spaces.WlInf α 4 f with hWdef
  have hWnn : 0 ≤ W := by rw [hWdef]; exact Work.FTS.H2.WPQ.WlInf_nonneg' hWf
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγs : 0 < Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_pos.mpr hγ
  have hγle : Real.sqrt (Work.Spaces.gam α - 1) ≤ 1 := by
    rw [Real.sqrt_le_one, Work.Spaces.gam_sub_one]; linarith
  have hHkSqnn : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
  obtain ⟨hAesmψ2, hGoodSlice⟩ := hA α f g hα hsf hsg
  have hGoodPt := hGood α f g hα hα1 hsf hWf hsg hHg
  set ψ2 : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Badz2 α f g z θ with hψ2
  set ψG : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
        - Work.FTS.H2.Badz2 α f g z θ) with hψG
  set Ff : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ with hFf
  set S : Set ℝ := {z | MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.H2.Badz2 α f g z θ) Work.Spaces.Iθ} with hS
  have hIθm : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact measurableSet_Ici
  have hAesmFf : MeasureTheory.AEStronglyMeasurable Ff
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := (Work.FTS.H2.AesmSlicesQ α f g hα hsf hsg).2
  -- pointwise bound of the marginal `ψG`
  have hψGbd : ∀ z ∈ Work.Spaces.Iz, |ψG z| ≤ Cg * W
      * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro z hz
    have hmaj : (fun θ => |(Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ)
          g z θ - Work.FTS.H2.Badz2 α f g z θ)|)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        fun θ => Cg * W * Work.Spaces.HkIntegrand α 4 g z θ :=
      MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => by
        rw [hWdef]; exact hGoodPt z hz θ hθ)
    have hgint : MeasureTheory.Integrable
        (fun θ => Cg * W * Work.Spaces.HkIntegrand α 4 g z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := (hHg.1 z hz).const_mul (Cg * W)
    refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
    calc (∫ θ in Work.Spaces.Iθ, |(Work.FTS.H2.H4PairInt α
            (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ - Work.FTS.H2.Badz2 α f g z θ)|)
        ≤ ∫ θ in Work.Spaces.Iθ, Cg * W * Work.Spaces.HkIntegrand α 4 g z θ :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => abs_nonneg _) hgint hmaj
      _ = Cg * W * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
          rw [MeasureTheory.integral_const_mul]
  -- the pointwise identity of the marginal
  have hident : ∀ z ∈ Work.Spaces.Iz, Ff z = ψ2 z + S.indicator ψG z := by
    intro z hz
    by_cases hzS : z ∈ S
    · have h2 : MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.Badz2 α f g z θ)
          Work.Spaces.Iθ := hzS
      have hG : MeasureTheory.IntegrableOn (fun θ => (Work.FTS.H2.H4PairInt α
            (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ - Work.FTS.H2.Badz2 α f g z θ))
          Work.Spaces.Iθ := hGoodSlice z hz
      have hsplit : Ff z = ψG z + ψ2 z := by
        have h1 : Ff z = (∫ θ in Work.Spaces.Iθ, (Work.FTS.H2.H4PairInt α
              (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ - Work.FTS.H2.Badz2 α f g z θ))
            + (∫ θ in Work.Spaces.Iθ, Work.FTS.H2.Badz2 α f g z θ) := by
          change (∫ θ in Work.Spaces.Iθ, Work.FTS.H2.H4PairInt α
              (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ) = _
          rw [show (fun θ => Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ)
                g z θ)
              = fun θ => (Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ)
                    g z θ - Work.FTS.H2.Badz2 α f g z θ)
                  + Work.FTS.H2.Badz2 α f g z θ from by funext θ; ring]
          exact MeasureTheory.integral_add hG h2
        rw [h1, hψG, hψ2]
      rw [hsplit, Set.indicator_of_mem hzS]
      ring
    · have hnotint : ¬ MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.H4PairInt α
          (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ) Work.Spaces.Iθ := by
        intro hcon
        refine hzS ?_
        have hsub : MeasureTheory.IntegrableOn (fun θ => Work.FTS.H2.H4PairInt α
              (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
              - (Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
                  - Work.FTS.H2.Badz2 α f g z θ)) Work.Spaces.Iθ :=
          hcon.sub (hGoodSlice z hz)
        refine hsub.congr ?_
        exact MeasureTheory.ae_restrict_of_forall_mem hIθm (fun θ hθ => by ring)
      have hFf0 : Ff z = 0 := by rw [hFf]; exact MeasureTheory.integral_undef hnotint
      have hψ20 : ψ2 z = 0 := by rw [hψ2]; exact MeasureTheory.integral_undef hzS
      rw [hFf0, hψ20, Set.indicator_of_notMem hzS]
      ring
  -- the indicator of `ψG` is integrable
  have hAesmInd : MeasureTheory.AEStronglyMeasurable (S.indicator ψG)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hcongr : (fun z => Ff z - ψ2 z)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz] S.indicator ψG := by
      filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
      rw [hident z hz]; ring
    exact (hAesmFf.sub hAesmψ2).congr hcongr
  have hSindInt : MeasureTheory.Integrable (S.indicator ψG)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' (hHg.2.const_mul (Cg * W)) hAesmInd ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS, Real.norm_eq_abs]; exact hψGbd z hz
    · rw [Set.indicator_of_notMem hzS, norm_zero]
      exact mul_nonneg (mul_nonneg (le_of_lt hCg) hWnn)
        (MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  -- the two marginal bounds
  have hψ2bd : |∫ z in Work.Spaces.Iz, ψ2 z| ≤ Cb * W * Work.Spaces.HkSq α 4 g := by
    have h := hB2 α f g hα hα1 hsf hWf hsg hHg hDec
    rw [hWdef]
    simpa only [hψ2] using h
  have hSindbd : (∫ z in Work.Spaces.Iz, |S.indicator ψG z|)
      ≤ Cg * W * Work.Spaces.HkSq α 4 g := by
    calc (∫ z in Work.Spaces.Iz, |S.indicator ψG z|)
        ≤ ∫ z in Work.Spaces.Iz, Cg * W
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun z => abs_nonneg _)
            (hHg.2.const_mul (Cg * W)) ?_
          filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
          by_cases hzS : z ∈ S
          · rw [Set.indicator_of_mem hzS]; exact hψGbd z hz
          · rw [Set.indicator_of_notMem hzS, abs_zero]
            exact mul_nonneg (mul_nonneg (le_of_lt hCg) hWnn)
              (MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
      _ = Cg * W * Work.Spaces.HkSq α 4 g := by
          rw [MeasureTheory.integral_const_mul]; rfl
  have hzbd : |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ (Cb + Cg) * W * Work.Spaces.HkSq α 4 g := by
    by_cases hI : MeasureTheory.Integrable ψ2 (MeasureTheory.volume.restrict Work.Spaces.Iz)
    · have hae : Ff =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          fun z => ψ2 z + S.indicator ψG z := by
        filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
        exact hident z hz
      calc |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
          = |∫ z in Work.Spaces.Iz, Ff z| := rfl
        _ = |∫ z in Work.Spaces.Iz, (ψ2 z + S.indicator ψG z)| := by
            rw [MeasureTheory.integral_congr_ae hae]
        _ = |(∫ z in Work.Spaces.Iz, ψ2 z) + (∫ z in Work.Spaces.Iz, S.indicator ψG z)| := by
            rw [MeasureTheory.integral_add hI hSindInt]
        _ ≤ |∫ z in Work.Spaces.Iz, ψ2 z|
              + |∫ z in Work.Spaces.Iz, S.indicator ψG z| := abs_add_le _ _
        _ ≤ Cb * W * Work.Spaces.HkSq α 4 g
              + (∫ z in Work.Spaces.Iz, |S.indicator ψG z|) :=
            add_le_add hψ2bd MeasureTheory.abs_integral_le_integral_abs
        _ ≤ Cb * W * Work.Spaces.HkSq α 4 g + Cg * W * Work.Spaces.HkSq α 4 g :=
            add_le_add le_rfl hSindbd
        _ = (Cb + Cg) * W * Work.Spaces.HkSq α 4 g := by ring
    · have hae : Ff =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          fun z => ψ2 z + S.indicator ψG z := by
        filter_upwards [MeasureTheory.ae_restrict_mem hIzm] with z hz
        exact hident z hz
      have hFfni : ¬ MeasureTheory.Integrable Ff
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        intro hcon
        have h2 : MeasureTheory.Integrable (fun z => ψ2 z + S.indicator ψG z)
            (MeasureTheory.volume.restrict Work.Spaces.Iz) := hcon.congr hae
        have h3 : MeasureTheory.Integrable
            (fun z => (ψ2 z + S.indicator ψG z) - S.indicator ψG z)
            (MeasureTheory.volume.restrict Work.Spaces.Iz) := h2.sub hSindInt
        exact hI (h3.congr (Filter.Eventually.of_forall fun z => by ring))
      rw [show Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g
          = ∫ z in Work.Spaces.Iz, Ff z from rfl,
        MeasureTheory.integral_undef hFfni, abs_zero]
      exact mul_nonneg (mul_nonneg (by positivity) hWnn) hHkSqnn
  -- normalise both halves to the same shape and combine with slack
  have hDthW : |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Cd / Real.sqrt (Work.Spaces.gam α - 1) * W * Work.FTS.Nonlin.Xn α g ^ 2 := by
    rw [hWdef]; exact hDth α f g hα hα1 hsf hWf hsg hHg
  have hzbdW : |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
      ≤ (Cb + Cg) * W * Work.FTS.Nonlin.Xn α g ^ 2 := by
    simpa only [Work.FTS.Nonlin.Xn, Work.FTS.H2.HkNorm_sq] using hzbd
  have h1 : (1 : ℝ) ≤ 1 / Real.sqrt (Work.Spaces.gam α - 1) := by
    rw [one_le_div hγs]; exact hγle
  have hWS : 0 ≤ W * Work.FTS.Nonlin.Xn α g ^ 2 := mul_nonneg hWnn (sq_nonneg _)
  have hstep : (Cb + Cg) * W * Work.FTS.Nonlin.Xn α g ^ 2
      ≤ (Cb + Cg) / Real.sqrt (Work.Spaces.gam α - 1) * W
        * Work.FTS.Nonlin.Xn α g ^ 2 := by
    calc (Cb + Cg) * W * Work.FTS.Nonlin.Xn α g ^ 2
        = (Cb + Cg) * 1 * (W * Work.FTS.Nonlin.Xn α g ^ 2) := by ring
      _ ≤ (Cb + Cg) * (1 / Real.sqrt (Work.Spaces.gam α - 1))
            * (W * Work.FTS.Nonlin.Xn α g ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hWS
      _ = (Cb + Cg) / Real.sqrt (Work.Spaces.gam α - 1) * W
            * Work.FTS.Nonlin.Xn α g ^ 2 := by ring
  have hcoef : (Cb + Cg) + Cd ≤ Cd + (Cb + Cg) + 1 := by linarith
  have hXn2 : 0 ≤ Work.FTS.Nonlin.Xn α g ^ 2 := sq_nonneg _
  calc |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        + |Work.FTS.H2.H4Pair α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ (Cb + Cg) * W * Work.FTS.Nonlin.Xn α g ^ 2
        + Cd / Real.sqrt (Work.Spaces.gam α - 1) * W * Work.FTS.Nonlin.Xn α g ^ 2 :=
        add_le_add hzbdW hDthW
    _ ≤ (Cb + Cg) / Real.sqrt (Work.Spaces.gam α - 1) * W
          * Work.FTS.Nonlin.Xn α g ^ 2
        + Cd / Real.sqrt (Work.Spaces.gam α - 1) * W * Work.FTS.Nonlin.Xn α g ^ 2 :=
        add_le_add hstep le_rfl
    _ = ((Cb + Cg) + Cd) / Real.sqrt (Work.Spaces.gam α - 1) * W
          * Work.FTS.Nonlin.Xn α g ^ 2 := by ring
    _ ≤ (Cd + (Cb + Cg) + 1) / Real.sqrt (Work.Spaces.gam α - 1) * W
          * Work.FTS.Nonlin.Xn α g ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoef hγs.le) hWnn) hXn2

end Work.FTS.H2.T3Q
