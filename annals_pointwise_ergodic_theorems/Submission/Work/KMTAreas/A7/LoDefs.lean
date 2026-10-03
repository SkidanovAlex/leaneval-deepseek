/-
# The `l = 0` vocabulary of Area A7: the guard, the level-`0` model tuple, and the two inputs

This module fixes the objects of the `l = 0` half of the §6--§8 analysis of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022

that the target `Work.KMTAreas.A7.ModelApproxLo` needs, and states its two analytic inputs as the
`Prop`s `LoErrStatement` and `LoModelStatement`.  See the module `ModelApproxLo` for the reduction.

The exact-height objects of `Large/Defs.lean` are built on
`iwArithFreqsNew ρ l = iwArithFreqs ρ l \ iwArithFreqs ρ (l-1)`, which is **empty** at `l = 0`
(`Nat` truncated subtraction): hence `Tex ρ 0 φ f = 0` and the exact-height model tuple vanishes
on the whole range `¬ (1 ≤ l₁ ∧ 1 ≤ l₂)` of the target (`modelTuple_eq_zero_of_lo`).  The paper's
model at arithmetic height `0` is instead the twisted bilinear multiplier of §6 with the single
arithmetic fibre `(0,0)` (`m_Ẑ(0,0) = 1`), whose `bn-ident` form is the *t*-average of the
products of the modulated height-`0` pieces: this is `loModelTuple`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.AssemblyLo

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract

/-! ## The guard of the large-scale tuples -/

/-- **The guard of the two tuples of the large-scale analysis.**  It is the `if`-test of both
`mainPartTuple` and `modelTuple`: the scale `N = ⌊a n⌋` lies in the index set
`I^{max l₁ l₂, k₁, k₂}`, is large (`N > splitCut ρ L`, `L = max (max l₁ l₂) (max k₁ k₂)`) and lies
in the main regime `k + 2u ≤ Log N`. -/
def loGuard (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) : Prop :=
  inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
    splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) ∧
    mainRegime ρ k₁ k₂ (Nat.floor (a n))

instance (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) :
    Decidable (loGuard ρ C₀ a l₁ l₂ k₁ k₂ n) := by unfold loGuard; infer_instance

/-- Unfolding of `mainPartTuple` at the guard. -/
theorem mainPartTuple_apply (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) (x : ℤ) :
    mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x =
      if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n then
        varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x else 0 := rfl

/-! ## The `l = 0` model tuple -/

/-- **The level-`0` model tuple of §6/§8.**  It is the paper's `bn-ident` form of the model at
arithmetic height `0`,

  `n ↦ ∫_{1/2}^1 (T^0_{φ_{N,t}}f)(x) (T^0_{φ̃_{N,t}}g)(x) dt`,  `N = ⌊a n⌋`,

on the scales of the guard, and `0` off it.  Here `T^0_φ = Tle ρ 0 φ` is the height-`0`
Ionescu--Wainger multiplier (`iwConv {0} (periodize φ)`, since `iwArithFreqs ρ 0 = {0}`). -/
noncomputable def loModelTuple (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if loGuard ρ C₀ a l₁ l₂ k₁ k₂ n then
      ∫ t in (1/2 : ℝ)..1,
        (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
          * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x)
    else 0

/-! ## The exact-height model vanishes at arithmetic height `0` -/

/-- The exact-height arithmetic frequency set at `l = 0` is empty
(`iwArithFreqsNew ρ 0 = iwArithFreqs ρ 0 \ iwArithFreqs ρ 0`). -/
theorem iwArithFreqsNew_zero (ρ : ℝ) : iwArithFreqsNew ρ 0 = ∅ := by
  simp [iwArithFreqsNew]

/-- The Ionescu--Wainger symbol attached to the empty set vanishes. -/
theorem iwSymbolSet_empty (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) :
    iwSymbolSet (∅ : Finset Work.Analysis.IonescuWainger.Circle) Φ = 0 := by
  funext ξ
  simp [iwSymbolSet]

/-- The Ionescu--Wainger kernel of the zero symbol vanishes. -/
theorem iwKernel_zero : iwKernel (0 : Work.Analysis.IonescuWainger.Circle → ℂ) = 0 := by
  funext j
  simp [iwKernel, fourierCoeff]

/-- The height-`0` Ionescu--Wainger multiplier vanishes. -/
theorem Tex_zero (ρ : ℝ) (φ : ℝ → ℂ) (f : ℤ → ℂ) : Tex ρ 0 φ f = 0 := by
  funext n
  rw [Tex, iwArithFreqsNew_zero]
  simp only [iwConv]
  rw [iwSymbolSet_empty (periodize φ), iwKernel_zero]
  simp

/-- `BtwistExact` vanishes when either input function vanishes. -/
theorem BtwistExact_zero_left (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (k : ℤ → ℂ) : BtwistExact ρ P l₁ l₂ m₁ m₂ 0 k = 0 := by
  funext x
  simp [BtwistExact]

theorem BtwistExact_zero_right (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h : ℤ → ℂ) : BtwistExact ρ P l₁ l₂ m₁ m₂ h 0 = 0 := by
  funext x
  simp [BtwistExact]

/-- **The exact-height model tuple vanishes at arithmetic height `0`** (pointwise form). -/
theorem modelTuple_apply_eq_zero_of_lo (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) (hlo : ¬ (1 ≤ l₁ ∧ 1 ≤ l₂)) :
    modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  have h0 : l₁ = 0 ∨ l₂ = 0 := by omega
  rcases h0 with h | h
  · rw [h]
    rw [modelTuple]
    split_ifs with hg
    · have hfe : ∀ t : ℝ, BtwistExact ρ P 0 l₂
          (mStarF (uScale ρ (max (max 0 l₂) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max 0 l₂) (max k₁ k₂))))
          (Tex ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f)
          (Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x = 0 :=
        fun t => by rw [Tex_zero, BtwistExact_zero_left]; rfl
      rw [intervalIntegral.integral_congr (fun t _ => hfe t)]
      simp
    · rfl
  · rw [h]
    rw [modelTuple]
    split_ifs with hg
    · have hfe : ∀ t : ℝ, BtwistExact ρ P l₁ 0
          (mStarF (uScale ρ (max (max l₁ 0) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ 0) (max k₁ k₂))))
          (Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
          (Tex ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x = 0 :=
        fun t => by rw [Tex_zero, BtwistExact_zero_right]; rfl
      rw [intervalIntegral.integral_congr (fun t _ => hfe t)]
      simp
    · rfl

/-- **The exact-height model tuple vanishes at arithmetic height `0`.**  Consequently
`modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ = 0` whenever `l₁ = 0` or `l₂ = 0` (i.e. always in the range
`¬ (1 ≤ l₁ ∧ 1 ≤ l₂)` of the target). -/
theorem modelTuple_eq_zero_of_lo (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (hlo : ¬ (1 ≤ l₁ ∧ 1 ≤ l₂)) :
    modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  exact modelTuple_apply_eq_zero_of_lo ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hlo


/-! ## The two analytic inputs of the `l = 0` assembly -/

/-- **The single-scale approximation error of the level-`0` model** (paper §6, Proposition
`mod-approx` at arithmetic height `0`), in the form the assembly consumes: for every `C₀ ≥ 1` there
are an exponent `c' ≥ 0` (independent of `ρ`) and `ρ₀ > 0` such that for every `ρ ∈ (0,ρ₀]` there
is a constant `K(Λ)` with

`‖mainPartTuple − loModelTuple‖_{ℓ^p} ≤ K(Λ) · 2^{c' L} · ⌊a n⌋^{-1} · ‖f‖_{p₁}‖g‖_{p₂}`,
`L = max (max l₁ l₂) (max k₁ k₂)`,

for every `Λ`-lacunary scale sequence with `a n ≥ 1`, every quadruple with `l₁ = l₂ = 0`, and
every `n`.  Both tuples vanish off the guard, so the estimate carries no further restriction.

**The hypothesis `l₁ = l₂ = 0` is essential.**  `loModelTuple` evaluates *both* inputs with the
height-`0` multiplier `Tle ρ 0` (`iwArithFreqs ρ 0 = {0}`), while the concrete columns use the
exact-height pieces `Tm ρ lᵢ`; at `(l₁,l₂) = (0,l₂)`, `l₂ ≥ 1`, the two sides live on different
arithmetic fibres (the exact-height piece has no `α = 0` fibre), so the comparison — and the
statement — is false for the *mixed* cases.  Those are covered separately
(`LoMixedLeftStatement`, `LoMixedRightStatement`).

The paper's Proposition `mod-approx` gives the single-scale bound `2^{O(max(2^{ρ·0},s))}⌊N⌋^{-1}`
with `s = max(k₁,k₂) ≤ L`, whence the weight `2^{c'L}`; at `l = 0` the `2^{O(2^{ρl})}` factor is
absent, so `c'` may be taken independent of `ρ`. -/
def LoErrStatement (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ), 1 ≤ C₀ → ∃ c' : ℝ, 0 ≤ c' ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        l₁ = 0 → l₂ = 0 → ∀ n : ℕ,
        MeasureTheory.eLpNorm (fun x : ℤ =>
            mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              - loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal)
            * ENNReal.ofReal ((2 : ℝ) ^ (c' * lmaxR l₁ l₂ k₁ k₂))
            * ENNReal.ofReal ((((Nat.floor (a n) : ℕ) : ℝ))⁻¹)
            * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

/-- **The §8 large-scale estimate for the level-`0` model tuple.**  For every `C₀ ≥ 1` and `r > 2`
there are an exponent `c ≥ 0` (independent of `ρ`) and `ρ₀ > 0` such that for every `ρ ∈ (0,ρ₀]`
there is a constant `K(Λ)` with

`‖V^r (loModelTuple)‖_{ℓ^p} ≤ K(Λ) · lossWeight c ρ l₁ l₂ k₁ k₂ · ‖f‖_{p₁}‖g‖_{p₂}`

for every `Λ`-lacunary scale sequence with `a n ≥ 1`, every quadruple with
`¬ (1 ≤ l₁ ∧ 1 ≤ l₂)` and all `f, g : ℤ → ℂ`. -/
def LoModelStatement (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          ¬ (1 ≤ l₁ ∧ 1 ≤ l₂) →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count


/-! ## The `l = 0` range split, and the two mixed cases -/

/-- **The shape of the target's conclusion, with the range of quadruples restricted by `Φ`.**  This
is the assertion of `Work.KMTAreas.A7.ModelApproxLo` (i.e. of the estimate
`‖V^r (mainPartTuple − modelTuple)‖_{ℓ^p} ≤ K(Λ) lossWeight c ρ l₁ l₂ k₁ k₂ ‖f‖_{p₁}‖g‖_{p₂}`) for
the quadruples satisfying `Φ l₁ l₂`. -/
def LoCase (Φ : ℕ → ℕ → Prop) (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → Φ l₁ l₂ →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                  - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
            (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

/-- **The mixed case `l₁ = 0`, `l₂ ≥ 1`.**  Here the concrete column is
`Ã_N(Π_{≤0,≤s₁}f, Π_{l₂,≤s₂}g)`: the first factor is the plain height-`0` low-pass while the
second is the *exact-height*`l₂` piece, whose arithmetic support is the exact-height set
`(ℚ/ℤ)_{l₂}` (it has **no** `α = 0` fibre), so that the analysis of the paper's §5--§8 is *not*
simpler than in the case `l₁,l₂ ≥ 1`: the column is estimated by first applying the §6
`mod-approx` at the arithmetic heights `(0,l₂)` — whose model is the twisted bilinear multiplier
with the arithmetic symbol `m_Ẑ(0,α₂)` on the fibre `(0,α₂)` — and then §8, in which the model is
bounded, via the tensor factorisation `form-1` and the triangle inequality (no arithmetic
cancellation is used at the exponents `(p₁,p₂) ≠ (2,2)`), by the product of the two *linear*
lacunary families: that step needs the linear variational estimates `(lin-1)`/`(lin-2)` for the
modulated *exact-height*`l₂` pieces `n ↦ Tm ρ l₂ (varphitildeNt ⌊a n⌋ k₂ t) g`, i.e. the
`ℓ^p`-square-function/variational estimate for the height-`l₂` lacunary family (the target
`Work.KMTAreas.A7.lacunaryIWProjLowpassVar` of the `A7` area), together with its height-`0`
counterpart `Work.KMTAreas.A7.LoLinVar`. -/
def LoMixedLeftStatement (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  LoCase (fun l₁ l₂ => l₁ = 0 ∧ 1 ≤ l₂) P p₁ p₂

/-- **The mixed case `l₁ ≥ 1`, `l₂ = 0`** (the mirror image of `LoMixedLeftStatement`). -/
def LoMixedRightStatement (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  LoCase (fun l₁ l₂ => 1 ≤ l₁ ∧ l₂ = 0) P p₁ p₂

/-- **The case `l₁ = l₂ = 0`**: the range in which `LoErrStatement` and `LoModelStatement` apply. -/
def LoZeroZeroStatement (P : ℤ[X]) (p₁ p₂ : ENNReal) : Prop :=
  LoCase (fun l₁ l₂ => l₁ = 0 ∧ l₂ = 0) P p₁ p₂

end

end Work.KMTAreas.A7
