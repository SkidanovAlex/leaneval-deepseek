/-
# The bounded-height large-scale `(2,2,1)` estimate for the concrete `§5` columns (low case)

Target: `Work.KMTPlan.A6.MainPieceBoundedH P r C₀ ρ B` — the `ℓ¹(ℤ;V^r)`-bound for the concrete
large-scale columns

  `n ↦ mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n`

at *bounded heights* `lcL l₁ l₂ k₁ k₂ ≤ B`, in the low case `k₁ = 0 ∨ k₂ = 0`, with `0 < ρ ≤ 1` and
an arbitrary constant `K : NNReal → NNReal`.

## The decomposition used here

`mainPartTuple` is the concrete halved average of the two exact-height pieces and `modelTupleRep`
(`KMTAreas/A7/Large/Defs.lean`) is the *repaired* `§6` model (band `uRep ρ l₁ l₂ k₁ k₂`,
exact-height kernel, band condition `bandCond` in its guard) for which the functional calculus
holds.  Pointwise, with no hypothesis at all,

  `mainPartTuple = modelTupleRep + (mainPartTuple − modelTupleRep)`,

so by the subadditivity of the variational norm (`variationalNorm_add_le`) and of the `ℒ¹`-seminorm
(`eLpNorm_add_le`) the target follows from the three estimates

* `mainPieceModelBound` — the `§8` bound for the model `modelTupleRep` itself, at bounded heights
  and `0 < ρ ≤ 1`;
* `mainPieceErrorBound` — the `§6` model-approximation error `mainPartTuple − modelTupleRep` in the
  range `1 ≤ l₁ ∧ 1 ≤ l₂`, at bounded heights and `0 < ρ ≤ 1`;
* `mainPieceHeightZero` — the range `l₁ = 0 ∨ l₂ = 0`, where `Tex ρ 0 = 0`
  (`iwArithFreqsNew ρ 0 = ∅`) makes `modelTupleRep` vanish identically, so that the estimate is a
  direct estimate for the concrete columns; this is the `Lo` chapter of the A7 development
  (`Work.KMTAreas.A7.ModelApproxLoRep`) at bounded heights and `ρ ≤ 1`.

The two halves `mainPieceModelBound`, `mainPieceErrorBound` are estimates for *different* operators
(the model, resp. the model-approximation error), and `mainPieceHeightZero` is the degenerate-height
range; the assembly below is the case split and the `ENNReal` bookkeeping.

## Related proved material in this directory

* `Submission/Work/KMTPlan/A6/PieceBoundedH/badScalesBounded.lean` proves
  `badScales_bounded_of_height`: at *bounded heights* (`Lnat l₁ l₂ k₁ k₂ ≤ B₀`) the bad
  (non-`Farey`) scales of the A7 linear analysis are confined to the first `n₀` indices, with `n₀`
  depending only on `ρ, C₀, Cρc, Λ, B₀` — and, unlike `Work.KMTAreas.A7.exists_Lnat_le_of_bad`, for
  **all** `0 < ρ ≤ 1` (no `ρ * C₀ ≤ 1/2`).  This is the form of the bad-scale step that the linear
  lacunary variational estimates need in order to be stated at bounded heights for all `ρ ≤ 1`.
- `linVarBounded` is the corresponding bounded-height form of the paper's linear estimates
  `(lin-1)`, `(lin-2)` (`Work.KMTAreas.A7Hi.LinVar` is the `ρ ≤ ρ₀` version).
- `Work.KMTAreas.A7.{RepMassBound, RepOffBandCrude, RepOffBandRegime, ExceptionalBound}` are the
  proved ingredients of `mainPieceErrorBound`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowModApproxNoAliasingCase
import Submission.Work.KMTPlan.A6.PieceBoundedH.errorBound
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.modelBoundAllRho
import Submission.Work.KMTPlan.A6.PieceBoundedH.heightZeroBound
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6.LowFix

noncomputable section

open MeasureTheory Polynomial
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-! ## The three estimates the decomposition reduces the target to -/

/-- **The `§8` model estimate at bounded heights.**  The `ℓ¹(ℤ;V^r)`-norm of the repaired `§6`
model `modelTupleRep` (the twisted bilinear multiplier with band `uRep`, exact-height arithmetic
kernel and the band condition in its guard) is bounded by `K(Λ)‖f‖₂‖g‖₂`, uniformly in the
lacunary sequence `a`, in the low-case quadruples with `lcL l₁ l₂ k₁ k₂ ≤ B`, and in the functions;
the constant may depend on `ρ` and `B`.

This is the `(2,2,1)` instance of the paper's `§8` large-scale estimate (`model-est`) for the
repaired model, without the gain: the band `uRep` makes the non-aliasing automatic, the functional
calculus applies, and the estimate is the `t`-integral of the product-rule bound for the
`BtwistExact`-kernel built from the two packet families `Tle ρ l (φ_{N,t})`, `Tle ρ l (φ̃_{N,t})` —
i.e. from the *linear* lacunary variational estimates `(lin-1)`, `(lin-2)` — together with the
kernel's `ℓ¹(ℤ²)`-mass bound. -/
theorem mainPieceModelBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
  Work.KMTPlan.A6.LowModApproxBoundedH.modelPieceBoundAllRho P hd r hr C₀ hC₀ ρ hρ B

/-- **The `§6` model-approximation error at bounded heights** (range `1 ≤ l₁ ∧ 1 ≤ l₂`): the
`ℓ¹(ℤ;V^r)`-norm of `mainPartTuple − modelTupleRep` is bounded by `K(Λ)‖f‖₂‖g‖₂`.  This is the
`(2,2,1)` instance of the paper's `mod-approx` in its loss form, at bounded heights and `ρ ≤ 1`;
it is proved in `Submission/Work/KMTPlan/A6/PieceBoundedH/errorBound.lean` as
`Work.KMTPlan.A6.PieceBoundedH.errorBound` (no gain is needed: on `lcL ≤ B` the weight
`2^{Aρ·lcL}` is a constant, absorbed into `K(Λ)`). -/
theorem mainPieceErrorBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → 1 ≤ l₁ → 1 ≤ l₂ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
  Work.KMTPlan.A6.PieceBoundedH.errorBound P hd r hr C₀ hC₀ hA1 ρ hρ hρ1 B

/-- **The height-zero range `l₁ = 0 ∨ l₂ = 0`.**  There the height-`0` arithmetic frequency set
`iwArithFreqsNew ρ 0` is empty, so `Tex ρ 0 ⋯ = 0` and the repaired model `modelTupleRep`
vanishes identically; the estimate for `mainPartTuple` is therefore a direct bound for the concrete
columns, uniformly in the lacunary sequence, in the low-case quadruples with heights `≤ B` and one
vanishing height, and in the functions. -/
theorem mainPieceHeightZero (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) → (l₁ = 0 ∨ l₂ = 0) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
  Work.KMTPlan.A6.PieceBoundedH.heightZeroBound P hd r hr C₀ hC₀ hA1 ρ hρ hρ1 B

/-! ## The assembly -/

/-- **The bounded-height large-scale `(2,2,1)` estimate for the concrete columns (low case).**

`mainPartTuple = modelTupleRep + (mainPartTuple − modelTupleRep)` pointwise, so the variational norm
and the `ℒ¹`-seminorm are controlled by the sum of the two halves; the range `l₁ = 0 ∨ l₂ = 0`,
where the model vanishes, is `mainPieceHeightZero`. -/
theorem mainPiece (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (B : ℕ) : Work.KMTPlan.A6.MainPieceBoundedH P r C₀ ρ B := by
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  obtain ⟨Km, hKm⟩ := mainPieceModelBound P hd r hr C₀ hC₀ hA1 ρ hρ hρ1 B
  obtain ⟨Ke, hKe⟩ := mainPieceErrorBound P hd r hr C₀ hC₀ hA1 ρ hρ hρ1 B
  obtain ⟨Kz, hKz⟩ := mainPieceHeightZero P hd r hr C₀ hC₀ hA1 ρ hρ hρ1 B
  refine ⟨fun Λ => max 1 (max (Km Λ + Ke Λ) (Kz Λ)), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ
  have hK_m : (Km Λ : ENNReal)
      ≤ ((max 1 (max (Km Λ + Ke Λ) (Kz Λ)) : NNReal) : ENNReal) := by
    rw [ENNReal.coe_le_coe]
    exact le_trans (le_add_of_nonneg_right (show (0 : NNReal) ≤ Ke Λ from zero_le))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hK_e : (Ke Λ : ENNReal)
      ≤ ((max 1 (max (Km Λ + Ke Λ) (Kz Λ)) : NNReal) : ENNReal) := by
    rw [ENNReal.coe_le_coe]
    exact le_trans (le_add_of_nonneg_left (show (0 : NNReal) ≤ Km Λ from zero_le))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hK_z : (Kz Λ : ENNReal)
      ≤ ((max 1 (max (Km Λ + Ke Λ) (Kz Λ)) : NNReal) : ENNReal) := by
    rw [ENNReal.coe_le_coe]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  by_cases hl : l₁ = 0 ∨ l₂ = 0
  · -- height-zero range: the model vanishes there, use the direct column estimate
    exact (hKz a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ hl).trans
      (mul_le_mul' (mul_le_mul' hK_z le_rfl) le_rfl)
  · -- both heights are at least one: split into the model and the model-approximation error
    have hl1 : 1 ≤ l₁ := by omega
    have hl2 : 1 ≤ l₂ := by omega
    set Fm : ℕ → ℤ → ℂ :=
      fun n x => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x with hFm
    set Fr : ℕ → ℤ → ℂ :=
      fun n x => Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x with hFr
    have hpt : ∀ x : ℤ,
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Fm n x)
        ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Fr n x)
          + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Fm n x - Fr n x) := by
      intro x
      have hsub : (fun n : ℕ => Fm n x)
          = (fun n : ℕ => Fr n x) + (fun n : ℕ => Fm n x - Fr n x) := by
        funext n
        simp only [Pi.add_apply]
        ring
      rw [hsub]
      exact variationalNorm_add_le hr1 _ _
    have e₁ : MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Fr n x))
        1 MeasureTheory.Measure.count
        ≤ (Km Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
      simpa only [hFr] using hKm a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ
    have e₂ : MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Fm n x - Fr n x))
        1 MeasureTheory.Measure.count
        ≤ (Ke Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
      simpa only [hFm, hFr] using hKe a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hl1 hl2
    refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
      (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Fm n x))
      (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Fr n x)
        + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Fm n x - Fr n x))
      (fun x => by simpa only [enorm_eq_self] using hpt x)).trans ?_
    refine (MeasureTheory.eLpNorm_add_le le_rfl).trans ?_
    refine (add_le_add e₁ e₂).trans ?_
    -- the arithmetic of the constant
    have hmid : (Km Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
        + (Ke Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
        = (((Km Λ + Ke Λ : NNReal)) : ENNReal)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
      rw [ENNReal.coe_add]
      ring
    rw [hmid]
    refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
    rw [ENNReal.coe_le_coe]
    exact le_trans (le_max_left _ _) (le_max_right _ _)

end

end Work.KMTPlan.A6.LowFix
