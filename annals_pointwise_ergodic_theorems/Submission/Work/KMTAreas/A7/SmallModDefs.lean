import Mathlib
import Submission.Work.KMTAreas.A7.SmallDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar Work.Analysis.IWMultiplier Work.Analysis.IonescuWainger

/-!
# The interface of the §6 model approximation for the small-scale estimate (Area A7)

This module collects **only the definitions** (and the elementary degenerate-case lemmas) that the
single-scale model approximation `Work.KMTAreas.A7.SmallSingleScaleB` and its two inputs
(`Work.KMTAreas.A7.smallDiff_eq_bilinOp`, `Work.KMTAreas.A7.smallKernelMass_le`) refer to:

* `smallScaleWeight C ρ l₁ l₂ k₁ k₂ = 2^{C·max(2^{ρL}, L)}`, the (summable) per-scale weight of the
  unsharp §6 estimate;
* `SmallSingleScaleB P p₁ p₂`, the per-scale model approximation;
* `tmKernel`, `smallKconc`, `smallKmod`, `smKernMass`, the two explicit kernels of the
  approximation (concrete column and §6 model operator) and the `ℓ¹(ℤ²)` mass;
* the four zero-function lemmas (`iwConv_zero_right`, `smallMainPart_zero_left/right`,
  `smallModelTuple_zero_left/right`), which make the degenerate cases of the summation
  `SmallSingleScaleB → SmallModApprox` trivial.

**Why this module exists.**  `Submission/Work/KMTAreas/A7/SmallModApprox.lean` (the target file)
must *import* the two inputs in order to assemble `SmallModApprox` from them.  Because the inputs
mention these definitions, any file proving them has to import the module that holds them; if that
module were `SmallModApprox.lean` itself, importing them back would create an import cycle.  Hence
the definitions live here, in a module that imports nothing from the two inputs.
-/

def smallScaleWeight (C ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : ℝ :=
  (2 : ℝ) ^ (C * max ((2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) (lmaxR l₁ l₂ k₁ k₂))

theorem smallScaleWeight_nonneg (C ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    0 ≤ smallScaleWeight C ρ l₁ l₂ k₁ k₂ := by
  rw [smallScaleWeight]; positivity

def SmallSingleScaleB (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → ∀ n : ℕ,
          MeasureTheory.eLpNorm (fun x : ℤ =>
              smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (smallScaleWeight C ρ l₁ l₂ k₁ k₂) *
              ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) *
              MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

/-! ## The explicit kernels of the two sides of the §6 approximation

The single-scale estimate `SmallSingleScaleB` is the paper's Proposition `mod-approx` composed
with the functional calculus `bn-ident`.  Its content is the `ℓ¹(ℤ²)` mass bound for the
difference of the kernels of the two bilinear convolutions:

* the *concrete* column `varpPiece` is `bilinOp (smallKconc ρ P l₁ l₂ k₁ k₂ N) f g`, the
  composition (`kernComp`) of the halved-average kernel `khalf N P` with the kernels
  `tmKernel ρ l (varphiN N k)` of the two exact-height IW multipliers `Tm ρ l (·)`;
* the *model* operator `smallModelOp` is `bilinOp (smallKmod ρ P l₁ l₂ k₁ k₂ N) f g`, where the
  `t`-integral of the twisted bilinear multiplier `B^{l₁,l₂,m_Ẑ}_{m_*}` (`smallArithKernel` times
  the two coefficient kernels `cw m_*`) is composed with the kernels of the *modulated* pieces.
-/

/-- The kernel of the exact-height Ionescu--Wainger multiplier `Tm ρ l φ`: the Fourier
coefficients of the symbol `∑_{α ∈ (ℚ/ℤ)_l} (periodize φ)(· - α)`. -/
noncomputable def tmKernel (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) : ℤ → ℂ :=
  Work.Analysis.IWMultiplier.iwKernel
    (Work.Analysis.IonescuWainger.iwSymbolSet (diffFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize φ))

/-- **The kernel of the concrete column**: the halved-average kernel `khalf N P` composed with
the kernels of the two exact-height §5 pieces `φ_N = varphiN N k₁`, `φ̃_N = varphitildeN d N k₂`. -/
noncomputable def smallKconc (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ k₁ k₂ N : ℕ) : ℤ → ℤ → ℂ :=
  kernComp (khalf N P) (tmKernel ρ l₁ (varphiN N k₁))
    (tmKernel ρ l₂ (varphitildeN P.natDegree N k₂))

/-- **The kernel of the §6 model operator**: the `t`-integral of the kernel of the twisted
bilinear multiplier `B^{l₁,l₂,m_Ẑ}_{m_*}` (arithmetic kernel times the coefficient kernels of
`m_* = η_{≤-2u} ⊗ η_{≤-2du}`) composed with the kernels of the two *modulated* pieces. -/
noncomputable def smallKmod (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ k₁ k₂ N : ℕ) : ℤ → ℤ → ℂ :=
  fun a b => ∫ t in (1/2 : ℝ)..1,
    kernComp (fun a b => smallArithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ a b
        * cw (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂))) a
        * cw (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂))) b)
      (tmKernel ρ l₁ (varphiNt N k₁ t))
      (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) a b

/-- The `ℓ¹(ℤ²)` mass of a bilinear kernel, as an extended nonnegative real. -/
noncomputable def smKernMass (K : ℤ → ℤ → ℂ) : ℝ≥0∞ :=
  ∑' p : ℤ × ℤ, ‖K p.1 p.2‖ₑ



/-! ## Degenerate cases of the model approximation

The two sides of the §6 model approximation are bilinear in their two arguments, so if one of
`f`, `g` vanishes then so does the difference.  These four lemmas record the (elementary)
unfoldings; they are what makes the `eLpNorm f p₁ = 0` / `eLpNorm g p₂ = 0` cases of the
summation `SmallSingleScaleB → SmallModApprox` trivial. -/

/-- `iwConv` of the zero function. -/
theorem iwConv_zero_right (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) :
    Work.Analysis.IWMultiplier.iwConv A Φ (0 : ℤ → ℂ) = 0 := by
  funext n
  simp [Work.Analysis.IWMultiplier.iwConv]

/-- With `f = 0` the concrete column vanishes. -/
theorem smallMainPart_zero_left (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    smallMainPart ρ P C₀ a 0 g l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  simp only [smallMainPart]
  split_ifs with h
  · simp only [varpPiece, AhalfR, Ahalf, Ablock, Fpiece, Gpiece, piece, piExact, kmtProj, kmtPj]
    simp [iwConv_zero_right]
  · rfl

/-- With `g = 0` the concrete column vanishes. -/
theorem smallMainPart_zero_right (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    smallMainPart ρ P C₀ a f 0 l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  simp only [smallMainPart]
  split_ifs with h
  · simp only [varpPiece, AhalfR, Ahalf, Ablock, Fpiece, Gpiece, piece, piExact, kmtProj, kmtPj]
    simp [iwConv_zero_right]
  · rfl

/-- With `f = 0` the model operator vanishes. -/
theorem smallModelTuple_zero_left (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    smallModelTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  simp only [smallModelTuple]
  split_ifs with h
  · simp only [smallModelOp, smallBtwist, Tm]
    simp [iwConv_zero_right]
  · rfl

/-- With `g = 0` the model operator vanishes. -/
theorem smallModelTuple_zero_right (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    smallModelTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  simp only [smallModelTuple]
  split_ifs with h
  · simp only [smallModelOp, smallBtwist, Tm]
    simp [iwConv_zero_right]
  · rfl

end

end Work.KMTAreas.A7
