/-
# The `l = 0` model approximation of Area A7 (`Work.KMTAreas.A7.ModelApproxLo`)

The target of this file is the second half of the §6 model approximation of §6--§8 of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022

in the shape needed by `Work.KMTAreas.A7.largeLoss_of_hi_lo`: the bound

`‖ V^r (mainPartTuple − modelTuple) ‖_{ℓ^p} ≤ K(Λ) · lossWeight c ρ l₁ l₂ k₁ k₂ · ‖f‖_{p₁}‖g‖_{p₂}`

restricted to the *complement* of the range `1 ≤ l₁ ∧ 1 ≤ l₂`, i.e. to the quadruples with
`l₁ = 0` or `l₂ = 0`.

## The reduction

The exact-height objects of `Large/Defs.lean` are built on
`iwArithFreqsNew ρ l = iwArithFreqs ρ l \ iwArithFreqs ρ (l-1)`, which is **empty** at `l = 0`
(`Nat` truncated subtraction): `Tex ρ 0 φ f = 0`, hence `modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ = 0`
for the whole range of the target (`LoDefs.modelTuple_eq_zero_of_lo`).  The paper's model at
arithmetic height `0` is instead the §6 twisted bilinear multiplier with the single arithmetic
fibre `(0,0)` (`m_Ẑ(0,0) = 1`), whose `bn-ident` form is the *t*-average of the products of the
modulated height-`0` pieces: this is `LoDefs.loModelTuple`.

The target is therefore the bound for `V^r (mainPartTuple)`, split as

  `mainPartTuple − modelTuple = (mainPartTuple − loModelTuple) + loModelTuple`,

* the **model part** `loModelTuple` is bounded by `LoModelStatement` (§8 of the paper, proved in
  `Work.KMTAreas.A7.LoModelLargeScale`);
* the **approximation error** `mainPartTuple − loModelTuple` has the single-scale size
  `2^{cL}⌊N⌋^{-1}‖f‖_{p₁}‖g‖_{p₂}` (the paper's Proposition `mod-approx` at `l = 0`, proved in
  `Work.KMTAreas.A7.LoErrSingleScale00` as `LoErrStatement`); summed over the lacunary scales with
  `VarNormTsumLp` and the doubly-exponential smallness `∑_{N ∈ I} N^{-1} ≲ 2^{-2^{L/C₀}+2}`
  (`invFloorSum_le`) it is absorbed by the weight `lossWeight c ρ …`
  (`exists_rpow_mul_two_rpow_neg_bound` below is the elementary arithmetic of that step).

The assembly of the two pieces into the target is `modelApproxLo_of_inputs`; the target
`ModelApproxLo` is its instance at the two inputs above.
-/



/-
## Status (and the two traps found in this chapter)

* The exact-height model tuple of `Large/Defs.lean` **vanishes** on the whole range
  `l₁ = 0 ∨ l₂ = 0` (`LoDefs.modelTuple_eq_zero_of_lo`), so the target is an estimate for the
  concrete columns themselves.  The proof splits the range into three cases
  (`ModelApproxLo` via `loCase_combine`):
  `(0,0)` (proved here from `LoErrStatement` + `LoModelStatement`), `(0,l₂)`, `l₂ ≥ 1`
  (`LoMixedLeftStatement`) and `(l₁,0)`, `l₁ ≥ 1` (`LoMixedRightStatement`).
* **Trap 1.** `loModelTuple` — the `bn-ident` form `∫_{1/2}^1 (T^0_{φ_{N,t}}f)(T^0_{φ̃_{N,t}}g)dt`
  of the §6 model at arithmetic height `0`, with the height-`0` multiplier `Tle ρ 0` on both
  factors — is the correct model of the column **only at `(l₁,l₂) = (0,0)`**.  At `(0,l₂)` with
  `l₂ ≥ 1` the concrete second factor is the *exact-height* piece `Tm ρ l₂ (varphitildeN …)`,
  whose arithmetic support is the exact-height set `(ℚ/ℤ)_{l₂}` and which has *no* `α = 0` fibre:
  the two sides then live on disjoint pieces of frequency space, and the naive statement
  (`LoErrStatement` without the `l₁ = l₂ = 0` hypothesis) is **false** (a counterexample was
  produced by the prover of the first version of `KMTAreas/A7/LoErrSingleScale`).
* **Trap 2.** At `(0,l₂)`, `l₂ ≥ 1` the correct §6 model is *not* a product: its arithmetic symbol
  on the fibre `(0,α₂)` is `m_Ẑ(0,α₂)` (the Weyl average `E_n e(α₂P(n))`, not `1`).  The mixed
  cases are therefore at full §5--§8 strength: after the tensor factorisation `form-1` the model is
  an *average of products*, so the §8 triangle inequality reduces the bound to the product of the
  two *linear* lacunary families, one of which is the exact-height family — i.e. the open chapter
  `Work.KMTAreas.A7.lacunaryIWProjLowpassVar` (the `ℓ^p` square-function/variational estimate for
  lacunary exact-height families, needed at arbitrary `1 < p < ∞`).  This is the honest reason the
  target is *not* reducible to the `(0,0)` case.

## What is proved in this file (complete, apart from the imported inputs)

`iwArithFreqsNew_zero`, `Tex_zero`, `BtwistExact_zero_left/right`,
`modelTuple_apply_eq_zero_of_lo`, `modelTuple_eq_zero_of_lo` (`LoDefs.lean`);
`exists_rpow_mul_two_rpow_neg_bound` (the arithmetic `2^{cL}2^{-2^{L/C₀}} ≤ const` of the error
summation), `loCase_combine` (the three-range combination), and the assembly
`modelApproxLo_zeroZero`.  The imported inputs are `LoErrSingleScale00` (§6 `mod-approx` at
`(0,0)`), `LoModelLargeScale` (§8 for the level-`0` model tuple, via `LoLinVar`), `LoMixedLeft` and
`LoMixedRight` (the two mixed cases).
-/ 
import Mathlib
import Submission.Work.KMTAreas.A7.LoErrSingleScale00
import Submission.Work.KMTAreas.A7.LoMixedLeft
import Submission.Work.KMTAreas.A7.LoMixedRight
import Submission.Work.KMTAreas.A7.LoModelLargeScaleHolds
import Submission.Work.KMTAreas.A7.LoMixedSingleScaleHolds
import Submission.Work.KMTAreas.A7.LoMixedOffBandHolds
import Submission.Work.KMTAreas.A7.MixedFSideHolds
import Submission.Work.KMTAreas.A7.MixedGSideLoRoute
import Submission.Work.KMTAreas.A7.FibreMassHolds
import Submission.Work.KMTAreas.A7.AbsorbHolds
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- For `C₀ ≥ 1` and `c ≥ 0`, eventually `(c+2) * y ≤ 2^{y/C₀}`. -/
lemma exists_exp_ge_linear (c : ℝ) (hc : 0 ≤ c) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → (c + 2) * y ≤ (2 : ℝ) ^ (y / (C₀ : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
  have hpos : (0 : ℝ) < Real.log 2 / (C₀ : ℝ) := div_pos hlog2 hC0
  have hz : Tendsto (fun z : ℝ => Real.exp z / z) atTop atTop := by
    simpa using Real.tendsto_exp_div_pow_atTop 1
  have hlin : Tendsto (fun y : ℝ => y * (Real.log 2 / (C₀ : ℝ))) atTop atTop :=
    Tendsto.atTop_mul_const hpos tendsto_id
  have hcomp : Tendsto (fun y : ℝ => Real.exp (y * (Real.log 2 / (C₀ : ℝ)))
      / (y * (Real.log 2 / (C₀ : ℝ)))) atTop atTop := hz.comp hlin
  have hcomp2 : Tendsto (fun y : ℝ => (Real.exp (y * (Real.log 2 / (C₀ : ℝ)))
      / (y * (Real.log 2 / (C₀ : ℝ)))) * (Real.log 2 / (C₀ : ℝ))) atTop atTop :=
    hcomp.atTop_mul_const hpos
  have heq : ∀ y : ℝ, y ≠ 0 →
      (Real.exp (y * (Real.log 2 / (C₀ : ℝ))) / (y * (Real.log 2 / (C₀ : ℝ))))
        * (Real.log 2 / (C₀ : ℝ)) = (2 : ℝ) ^ (y / (C₀ : ℝ)) / y := by
    intro y hy
    have ha : Real.log 2 / (C₀ : ℝ) ≠ 0 := ne_of_gt hpos
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have harg : Real.log 2 * (y / (C₀ : ℝ)) = y * (Real.log 2 / (C₀ : ℝ)) := by ring
    rw [harg]
    field_simp
  have hevent : (fun y : ℝ => (Real.exp (y * (Real.log 2 / (C₀ : ℝ)))
      / (y * (Real.log 2 / (C₀ : ℝ)))) * (Real.log 2 / (C₀ : ℝ)))
      =ᶠ[atTop] fun y : ℝ => (2 : ℝ) ^ (y / (C₀ : ℝ)) / y := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact heq y (ne_of_gt hy)
  have hkey : Tendsto (fun y : ℝ => (2 : ℝ) ^ (y / (C₀ : ℝ)) / y) atTop atTop :=
    Tendsto.congr' hevent hcomp2
  have hev := hkey.eventually_ge_atTop (c + 2)
  rw [eventually_atTop] at hev
  obtain ⟨Y, hY⟩ := hev
  refine ⟨max Y 1, fun y hy => ?_⟩
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hy)
  have h := hY y (le_trans (le_max_left _ _) hy)
  rw [le_div_iff₀ hy0] at h
  linarith


/-- **Combining a range split.**  If the target-shaped estimate holds on three sub-ranges
`Φ₁, Φ₂, Φ₃` of the quadruples (with the same exponents), then it holds on their union. -/
lemma loCase_combine (P : Polynomial ℤ) (p₁ p₂ : ENNReal) {Φ₁ Φ₂ Φ₃ : ℕ → ℕ → Prop}
    (h1 : LoCase Φ₁ P p₁ p₂) (h2 : LoCase Φ₂ P p₁ p₂) (h3 : LoCase Φ₃ P p₁ p₂) :
    LoCase (fun l₁ l₂ => Φ₁ l₁ l₂ ∨ Φ₂ l₁ l₂ ∨ Φ₃ l₁ l₂) P p₁ p₂ := by
  intro C₀ r hC₀ hr
  obtain ⟨c₁, hc₁, ρ₁, hρ₁, hK₁⟩ := h1 C₀ r hC₀ hr
  obtain ⟨c₂, hc₂, ρ₂, hρ₂, hK₂⟩ := h2 C₀ r hC₀ hr
  obtain ⟨c₃, hc₃, ρ₃, hρ₃, hK₃⟩ := h3 C₀ r hC₀ hr
  refine ⟨max (max c₁ c₂) c₃, by positivity, min (min ρ₁ ρ₂) ρ₃,
    lt_min (lt_min hρ₁ hρ₂) hρ₃, ?_⟩
  intro ρ hρ hρle
  have hρ₁' : ρ ≤ ρ₁ := le_trans hρle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρ₂' : ρ ≤ ρ₂ := le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρ₃' : ρ ≤ ρ₃ := le_trans hρle (min_le_right _ _)
  obtain ⟨K₁, hK₁'⟩ := hK₁ ρ hρ hρ₁'
  obtain ⟨K₂, hK₂'⟩ := hK₂ ρ hρ hρ₂'
  obtain ⟨K₃, hK₃'⟩ := hK₃ ρ hρ hρ₃'
  have hρnn : (0 : ℝ) ≤ ρ := le_of_lt hρ
  refine ⟨fun Λ => K₁ Λ + K₂ Λ + K₃ Λ, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hΦ
  -- the constant and weight upgrade
  have hup : ∀ (c : ℝ) (K : NNReal), c ≤ max (max c₁ c₂) c₃ →
      K ≤ K₁ Λ + K₂ Λ + K₃ Λ →
      (K : ENNReal) * ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      ≤ ((K₁ Λ + K₂ Λ + K₃ Λ : NNReal) : ENNReal)
        * ENNReal.ofReal (lossWeight (max (max c₁ c₂) c₃) ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    intro c K hc hKle
    have hw : ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂)
        ≤ ENNReal.ofReal (lossWeight (max (max c₁ c₂) c₃) ρ l₁ l₂ k₁ k₂) :=
      ofReal_lossWeight_mono_L hρnn hc l₁ l₂ k₁ k₂
    have hK : (K : ENNReal) ≤ ((K₁ Λ + K₂ Λ + K₃ Λ : NNReal) : ENNReal) :=
      ENNReal.coe_le_coe.mpr hKle
    have hstep : (K : ENNReal) * ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂)
        ≤ ((K₁ Λ + K₂ Λ + K₃ Λ : NNReal) : ENNReal)
          * ENNReal.ofReal (lossWeight (max (max c₁ c₂) c₃) ρ l₁ l₂ k₁ k₂) :=
      (mul_le_mul_of_le_left hK _).trans (mul_le_mul_of_le_right hw _)
    exact mul_le_mul_of_le_left (mul_le_mul_of_le_left hstep
      (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count))
      (MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
  have hK₁le : K₁ Λ ≤ K₁ Λ + K₂ Λ + K₃ Λ :=
    le_trans (le_add_of_nonneg_right (a := K₁ Λ) (bot_le : (0 : NNReal) ≤ K₂ Λ))
      (le_add_of_nonneg_right (a := K₁ Λ + K₂ Λ) (bot_le : (0 : NNReal) ≤ K₃ Λ))
  have hK₂le : K₂ Λ ≤ K₁ Λ + K₂ Λ + K₃ Λ :=
    le_trans (le_add_of_nonneg_left (a := K₂ Λ) (bot_le : (0 : NNReal) ≤ K₁ Λ))
      (le_add_of_nonneg_right (a := K₁ Λ + K₂ Λ) (bot_le : (0 : NNReal) ≤ K₃ Λ))
  have hK₃le : K₃ Λ ≤ K₁ Λ + K₂ Λ + K₃ Λ :=
    le_add_of_nonneg_left (a := K₃ Λ) (b := K₁ Λ + K₂ Λ) (bot_le : (0 : NNReal) ≤ K₁ Λ + K₂ Λ)
  rcases hΦ with h | h | h
  · exact (hK₁' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 h).trans
      (hup c₁ (K₁ Λ) (le_trans (le_max_left _ _) (le_max_left _ _)) hK₁le)
  · exact (hK₂' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 h).trans
      (hup c₂ (K₂ Λ) (le_trans (le_max_right _ _) (le_max_left _ _)) hK₂le)
  · exact (hK₃' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 h).trans
      (hup c₃ (K₃ Λ) (le_max_right _ _) hK₃le)

/-- The doubly-exponential weight is bounded. -/
lemma exists_rpow_mul_two_rpow_neg_bound (c : ℝ) (hc : 0 ≤ c) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (D : ℝ) (hD : 0 ≤ D) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ L : ℕ, D * (2:ℝ) ^ (c * (L:ℝ)) *
        (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2) ≤ E := by
  obtain ⟨Y, hY⟩ := exists_exp_ge_linear c hc C₀ hC₀
  have hC0 : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
  set X : ℝ := max Y 1 with hX
  set N₀ : ℕ := ⌈X⌉₊ with hN₀
  have hXN₀ : X ≤ (N₀ : ℝ) := Nat.le_ceil X
  refine ⟨max D (D * (2:ℝ) ^ (c * (N₀:ℝ)) * 4), ?_, fun L => ?_⟩
  · refine le_trans hD (le_max_left _ _)
  by_cases hL : L ≤ N₀
  · have h1 : (2:ℝ) ^ (c * (L:ℝ)) ≤ (2:ℝ) ^ (c * (N₀:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (L:ℝ) ≤ (N₀:ℝ) := by exact_mod_cast hL
      nlinarith
    have h2 : (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2) ≤ 4 := by
      have h3 : (1:ℝ) ≤ (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
      have h4 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by linarith : -((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2 ≤ 2)
      rw [show (2:ℝ)^(2:ℝ) = 4 from by rw [Real.rpow_two]; norm_num] at h4
      exact h4
    have hD4 : (0:ℝ) ≤ D * (2:ℝ) ^ (c * (N₀:ℝ)) := by positivity
    have hDnn : (0:ℝ) ≤ D := hD
    calc D * (2:ℝ) ^ (c * (L:ℝ)) * (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2)
        ≤ D * (2:ℝ) ^ (c * (N₀:ℝ)) * (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hD) (by positivity)
      _ ≤ D * (2:ℝ) ^ (c * (N₀:ℝ)) * 4 := mul_le_mul_of_nonneg_left h2 hD4
      _ ≤ max D (D * (2:ℝ) ^ (c * (N₀:ℝ)) * 4) := le_max_right _ _
  · push Not at hL
    have hLX : X ≤ (L:ℝ) := le_trans hXN₀ (by exact_mod_cast (le_of_lt hL))
    have hL1 : (1:ℝ) ≤ (L:ℝ) := le_trans (le_max_right _ 1) hLX
    have hLY : Y ≤ (L:ℝ) := le_trans (le_max_left Y 1) hLX
    have hle := hY (L:ℝ) hLY
    have hkey : c * (L:ℝ) + 2 ≤ (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ)) := by
      have h2 : c * (L:ℝ) + 2 ≤ (c+2) * (L:ℝ) := by nlinarith
      linarith
    have hfin : c * (L:ℝ) - (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ)) + 2 ≤ 0 := by linarith
    have hsplit : D * (2:ℝ) ^ (c * (L:ℝ)) * (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2)
        = D * (2:ℝ) ^ (c * (L:ℝ) - (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ)) + 2) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      ring_nf
    rw [hsplit]
    calc D * (2:ℝ) ^ (c * (L:ℝ) - (2:ℝ) ^ ((L:ℝ)/(C₀:ℝ)) + 2)
        ≤ D * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hD
          exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hfin
      _ = D := mul_one D
      _ ≤ max D (D * (2:ℝ) ^ (c * (N₀:ℝ)) * 4) := le_max_left _ _



/-- The nonnegative constant of the assembly (a structure-literal `NNReal`). -/
def loKc (a : ℝ) (h : 0 ≤ a) : NNReal := ⟨a, h⟩

/-- **The assembly of the `l = 0` model approximation** from its two analytic inputs
(`LoErrStatement`, the single-scale §6 comparison, and `LoModelStatement`, the §8 bound for the
level-`0` model tuple). -/
theorem modelApproxLo_zeroZero (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hErr : LoErrStatement P p₁ p₂) (hModel : LoModelStatement P p₁ p₂) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            l₁ = 0 ∧ l₂ = 0 →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - Work.KMTAreas.A7.modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  intro C₀ r hC₀ hr
  classical
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := by
    have : (1 : ℕ) ≤ C₀ := hC₀
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hp : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  obtain ⟨cE, hcE, ρE, hρE, hE⟩ := hErr C₀ hC₀
  obtain ⟨cM, hcM, ρM, hρM, hM⟩ := hModel C₀ r hC₀ hr
  -- the summability constant `D(Λ)` of `invFloorSum_le`
  set Dfun : NNReal → ℝ :=
    fun Λ => if h : 1 < Λ then Classical.choose (invFloorSum_le C₀ hC₀ Λ h) else 0 with hDfun
  have hDfun0 : ∀ Λ : NNReal, 0 ≤ Dfun Λ := by
    intro Λ
    by_cases h : 1 < Λ
    · rw [hDfun]; simp only [dif_pos h]
      exact (Classical.choose_spec (invFloorSum_le C₀ hC₀ Λ h)).1
    · rw [hDfun]; simp [h]
  have hDfunb : ∀ (Λ : NNReal), 1 < Λ → ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∑' n : ℕ, (if L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
        ≤ Dfun Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) := by
    intro Λ hΛ L hL a ha ha1
    rw [hDfun]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (invFloorSum_le C₀ hC₀ Λ hΛ)).2 L hL a ha ha1
  refine ⟨max cE cM + 2, by positivity, min ρE (min ρM (1 / (4 * (C₀ : ℝ)))), ?_, ?_⟩
  · exact lt_min hρE (lt_min hρM (by positivity))
  intro ρ hρ hρle
  have hρnn : (0 : ℝ) ≤ ρ := le_of_lt hρ
  have hρE' : ρ ≤ ρE := le_trans hρle (min_le_left _ _)
  have hρM' : ρ ≤ ρM := le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
  obtain ⟨KE, hE'⟩ := hE ρ hρ hρE'
  obtain ⟨KM, hM'⟩ := hM ρ hρ hρM'
  -- the two exponential constants
  set Emax : NNReal → ℝ := fun Λ => max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (Dfun Λ) with hEmax
  have hEmax0 : ∀ Λ : NNReal, 0 ≤ Emax Λ := by
    intro Λ
    have : 0 ≤ Dfun Λ := hDfun0 Λ
    rw [hEmax]
    exact le_trans this (le_max_right _ _)
  have hEmax1 : ∀ (Λ : NNReal), 1 < Λ →
      max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (Dfun Λ) ≤ Emax Λ := fun Λ _ => le_of_eq rfl
  have hsup : ∀ Λ : NNReal, ∃ E : ℝ, 0 ≤ E ∧ ∀ L : ℕ,
      4 * (KE Λ : ℝ) * Emax Λ * (2 : ℝ) ^ (cE * (L : ℝ)) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) ≤ E := by
    intro Λ
    have hD : 0 ≤ 4 * (KE Λ : ℝ) * Emax Λ := by
      have := hEmax0 Λ; positivity
    exact exists_rpow_mul_two_rpow_neg_bound cE hcE C₀ hC₀ (4 * (KE Λ : ℝ) * Emax Λ) hD
  set Efun : NNReal → ℝ := fun Λ => Classical.choose (hsup Λ) with hEfun
  have hEfun0 : ∀ Λ : NNReal, 0 ≤ Efun Λ := fun Λ => (Classical.choose_spec (hsup Λ)).1
  have hEfunb : ∀ (Λ : NNReal) (L : ℕ),
      4 * (KE Λ : ℝ) * Emax Λ * (2 : ℝ) ^ (cE * (L : ℝ)) *
        (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) ≤ Efun Λ :=
    fun Λ L => (Classical.choose_spec (hsup Λ)).2 L
  refine ⟨fun Λ => loKc (Efun Λ + (KM Λ : ℝ)) (add_nonneg (hEfun0 Λ) (by positivity)), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 h00
  have hl₁ : l₁ = 0 := h00.1
  have hl₂ : l₂ = 0 := h00.2
  have hlo : ¬ (1 ≤ l₁ ∧ 1 ≤ l₂) := by omega
  -- (0) the exact-height model vanishes in this range
  have hMT : ∀ n x, modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 :=
    fun n x => modelTuple_apply_eq_zero_of_lo ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hlo
  -- (1) the pointwise split
  have hpt : ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
    intro x
    have hfun : (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = fun n : ℕ => (mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x := by
      funext n
      rw [hMT n x]
      ring
    rw [hfun]
    exact Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr1 _ _
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
    (g := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
    (fun x => by simpa only [enorm_eq_self] using hpt x)).trans ?_
  refine (MeasureTheory.eLpNorm_add_le hp).trans ?_
  -- (2) the model part
  have hmod : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ (KM Λ : ENNReal) * ENNReal.ofReal (lossWeight cM ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
    hM' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hlo
  -- (3) the error part
  set Xe : ENNReal := (KE Λ : ENNReal)
      * ENNReal.ofReal ((2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂))
      * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
      * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hXe
  have hper : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by
    intro n
    have h := hE' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hl₁ hl₂ n
    rw [hXe]
    exact h.trans (le_of_eq (by ac_rfl))
  have hzero : ∀ n : ℕ, ¬ loGuard ρ C₀ a l₁ l₂ k₁ k₂ n →
      (fun x : ℤ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
    intro n hn
    funext x
    rw [mainPartTuple_apply, loModelTuple]
    rw [if_neg hn, if_neg hn]
    simp
  have hper' : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
        then Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0 := by
    intro n
    by_cases hn : loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
    · rw [if_pos hn]; exact hper n
    · rw [if_neg hn, hzero n hn]; simp
  have hvar := VarNormTsumLp hr1 hp (fun n x => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
  have hstep : (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count)
      ≤ 4 * Xe * (∑' n : ℕ, (if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
          then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) := by
    calc (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ =>
          mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count)
        ≤ ∑' n : ℕ, 4 * (if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
            then Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0) :=
          ENNReal.tsum_le_tsum (fun n => mul_le_mul' le_rfl (hper' n))
      _ = 4 * Xe * (∑' n : ℕ, (if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
            then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr (fun n => ?_)
          by_cases hn : loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
          · rw [if_pos hn, if_pos hn]; ring
          · rw [if_neg hn, if_neg hn]; ring
  -- the guard implies the height condition
  have hcond : ∀ n : ℕ, loGuard ρ C₀ a l₁ l₂ k₁ k₂ n →
      max (max l₁ l₂) (max k₁ k₂) ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) := by
    intro n hg
    have h1 : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) := hg.1
    rw [inIndexSet] at h1
    obtain ⟨ha1', hk1', hk2'⟩ := h1
    have h2 : max (l₁ : ℤ) (l₂ : ℤ) ≤
        ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := ha1'
    have h3 : (k₁ : ℤ) ≤
        ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := hk1'
    have h4 : (k₂ : ℤ) ≤
        ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := hk2'
    omega
  have hLcast : (((max (max l₁ l₂) (max k₁ k₂) : ℕ)) : ℝ) = lmaxR l₁ l₂ k₁ k₂ := by
    rw [lmaxR, Work.Analysis.EndVar.lmax, Nat.cast_max, Nat.cast_max]
    push_cast
    rfl
  have hsum4 : (∑' n : ℕ, (if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n
        then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ ENNReal.ofReal (Emax Λ
          * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2)) := by
    have hmain := tsum_ite_floor_le_indexSet C₀ hC₀ Λ hΛ (Dfun Λ) (hDfun0 Λ)
      (fun L hL a ha ha1 => hDfunb Λ hΛ L hL a ha ha1)
      (max (max l₁ l₂) (max k₁ k₂)) (Emax Λ) (hEmax1 Λ hΛ) a ha ha1
      (fun n => loGuard ρ C₀ a l₁ l₂ k₁ k₂ n) hcond
    rwa [hLcast] at hmain
  -- the real weight arithmetic
  have hreal : 4 * (KE Λ : ℝ) * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
        * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2))
      ≤ Efun Λ := by
    have hb := hEfunb Λ (max (max l₁ l₂) (max k₁ k₂))
    rw [hLcast] at hb
    calc 4 * (KE Λ : ℝ) * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
          * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2))
        = 4 * (KE Λ : ℝ) * Emax Λ * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
          * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2) := by ring
      _ ≤ Efun Λ := hb
  have hofReal : ENNReal.ofReal (4 * (KE Λ : ℝ) * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
        * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2)))
      = (4 : ENNReal) * (KE Λ : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂))
        * ENNReal.ofReal (Emax Λ
            * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2)) := by
    have harg : 4 * (KE Λ : ℝ) * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
          * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2))
        = ((4 : ℝ) * (KE Λ : ℝ)) * ((2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
          * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2))) := by
      ring
    rw [harg, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity),
      show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) from by norm_num]
    rw [ENNReal.ofReal_coe_nnreal]
    ring
  -- the error bound
  have herr : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Efun Λ)
          * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    refine hvar.trans ?_
    refine hstep.trans ?_
    refine (mul_le_mul' le_rfl hsum4).trans ?_
    have hZ1 : (1 : ENNReal) ≤
        ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂) :=
      ENNReal.one_le_ofReal.mpr (one_le_lossWeight_L (by positivity) hρnn l₁ l₂ k₁ k₂)
    calc 4 * Xe * ENNReal.ofReal (Emax Λ
            * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2))
        = ((4 : ENNReal) * (KE Λ : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂))
            * ENNReal.ofReal (Emax Λ
                * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2)))
          * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
          rw [hXe]; ring
      _ = ENNReal.ofReal (4 * (KE Λ : ℝ) * (2 : ℝ) ^ (cE * lmaxR l₁ l₂ k₁ k₂)
            * (Emax Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (lmaxR l₁ l₂ k₁ k₂ / (C₀ : ℝ))) + 2)))
          * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by rw [hofReal]
      _ ≤ ENNReal.ofReal (Efun Λ)
            * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :=
          mul_le_mul_of_le_left (ENNReal.ofReal_le_ofReal hreal) _
      _ = ENNReal.ofReal (Efun Λ)
            * (1 * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
                * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)) := by rw [one_mul]
      _ ≤ ENNReal.ofReal (Efun Λ)
            * (ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
              * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
                * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)) :=
          mul_le_mul_of_le_right (mul_le_mul_of_le_left hZ1 _) _
      _ = ENNReal.ofReal (Efun Λ)
            * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
            * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring
  -- the model part with the final weight
  have hmod' : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ (KM Λ : ENNReal)
          * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    refine hmod.trans ?_
    have hw : ENNReal.ofReal (lossWeight cM ρ l₁ l₂ k₁ k₂)
        ≤ ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂) :=
      ofReal_lossWeight_mono_L hρnn (le_trans (le_max_right cE cM) (by linarith)) l₁ l₂ k₁ k₂
    exact mul_le_mul_of_le_left (mul_le_mul_of_le_left
      (mul_le_mul_of_le_right hw (KM Λ : ENNReal)) _) _
  -- combining the two parts
  refine (add_le_add herr hmod').trans ?_
  have hKfun : ENNReal.ofReal (Efun Λ) + (KM Λ : ENNReal)
      ≤ (loKc (Efun Λ + (KM Λ : ℝ)) (add_nonneg (hEfun0 Λ) (by positivity)) : ENNReal) := by
    conv_rhs => rw [← ENNReal.ofReal_coe_nnreal]
    show ENNReal.ofReal (Efun Λ) + (KM Λ : ENNReal) ≤ ENNReal.ofReal (Efun Λ + (KM Λ : ℝ))
    rw [ENNReal.ofReal_add (hEfun0 Λ) (by positivity), ENNReal.ofReal_coe_nnreal]
  calc ENNReal.ofReal (Efun Λ)
        * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      + (KM Λ : ENNReal) * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
      = (ENNReal.ofReal (Efun Λ) + (KM Λ : ENNReal))
        * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by ring
    _ ≤ (loKc (Efun Λ + (KM Λ : ℝ)) (add_nonneg (hEfun0 Λ) (by positivity)) : ENNReal)
        * ENNReal.ofReal (lossWeight (max cE cM + 2) ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
        mul_le_mul_of_le_left (mul_le_mul_of_le_left (mul_le_mul_of_le_left hKfun _) _) _



/-- **The mixed case `l₁ = 0`, `l₂ ≥ 1`, assembled from its four analytic inputs**:
the band-restricted §6 error, the off-band §6 error and the two §8 factor estimates. -/
theorem loMixedLeft_of_statements (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁)
    (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hSS : LoMixedSingleScaleStatement P p₁ p₂) (hOff : LoMixedOffBandStatement P p₁ p₂)
    (hF : MixedFSideEstimate P p₁) (hG : MixedGSideEstimate P p₂) :
    LoMixedLeftStatement P p₁ p₂ :=
  loMixedLeft_of_inputs P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum
    (loMixedErr_of_inputs P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum
      (loMixedBandErr_of_singleScale P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum hSS) hOff)
    (loMixedModel_of_inputs P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum hF hG)

/-- **The mixed case `l₁ ≥ 1`, `l₂ = 0`, assembled from the single-scale `ℓ¹(ℤ²)` mass bound
of §6.** -/
theorem loMixedRight_of_massStatement (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁)
    (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hmass : LoMixedRMassStatement P) : LoMixedRightStatement P p₁ p₂ :=
  loMixedRight_of_singleScale P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum
    (LoMixedRSingleScaleOfMass P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum hmass)

/-- **The target of this file.**  The `l = 0` half of the §6 model approximation of §6--§8: on the
range `¬ (1 ≤ l₁ ∧ 1 ≤ l₂)` the concrete columns `mainPartTuple` are bounded by the weight
`lossWeight c ρ l₁ l₂ k₁ k₂`.  The range is split into `(l₁,l₂) = (0,0)`, `(0,l₂)` with `l₂ ≥ 1`
and `(l₁,0)` with `l₁ ≥ 1`; the first case is the assembly `modelApproxLo_zeroZero` (the level-`0`
model tuple `loModelTuple` is the correct §6 model there), the two mixed cases are the two
statements `LoMixedLeftStatement`, `LoMixedRightStatement` (in which the exact-height tower of the
other factor is present, so that the paper's §5--§8 analysis is at full strength). -/
theorem modelApproxLo_of_pieces (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hModel : LoModelStatement P p₁ p₂) (hLo : LoMixedLeftStatement P p₁ p₂)
    (hHi : LoMixedRightStatement P p₁ p₂) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            ¬ (1 ≤ l₁ ∧ 1 ≤ l₂) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - Work.KMTAreas.A7.modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  have hAll : LoCase (fun l₁ l₂ => l₁ = 0 ∧ l₂ = 0 ∨ (l₁ = 0 ∧ 1 ≤ l₂) ∨ (1 ≤ l₁ ∧ l₂ = 0))
      P p₁ p₂ :=
    loCase_combine P p₁ p₂
      (modelApproxLo_zeroZero P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum
        (LoErrSingleScale00 P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)
        hModel)
      hLo
      hHi
  intro C₀ r hC₀ hr
  obtain ⟨c, hc, ρ₀, hρ₀, hK⟩ := hAll C₀ r hC₀ hr
  refine ⟨c, hc, ρ₀, hρ₀, ?_⟩
  intro ρ hρ hρle
  obtain ⟨K, hK'⟩ := hK ρ hρ hρle
  refine ⟨K, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hlo
  exact hK' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 (by omega)

end


/-- **The target of this file.**  The `l = 0` half of the §6 model approximation of §6--§8:
on the range `¬ (1 ≤ l₁ ∧ 1 ≤ l₂)` the concrete columns `mainPartTuple` are bounded by the weight
`lossWeight c ρ l₁ l₂ k₁ k₂`, assembled from the `(0,0)` case (`modelApproxLo_zeroZero` with the
§6 error `LoErrSingleScale00` and the level-`0` model bound `LoModelLargeScaleHolds`) and the two
mixed cases (`loMixedLeft_of_statements`, `loMixedRight_of_massStatement`). -/
theorem ModelApproxLo (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            ¬ (1 ≤ l₁ ∧ 1 ≤ l₂) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - Work.KMTAreas.A7.modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
  modelApproxLo_of_pieces P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum
    (LoModelLargeScaleHolds P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)
    (loMixedLeft_of_statements P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum
      (LoMixedSingleScaleHolds P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)
      (LoMixedOffBandHolds P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)
      (MixedFSideHolds P p₁ hdeg hp₁ htp₁)
      (MixedGSideEstimate_lo P p₂ hdeg hp₂ htp₂))
    (loMixedRight_of_massStatement P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum
      (loMixedRMass_of P (FibreMassHolds P) (AbsorbHolds P)))

end Work.KMTAreas.A7
