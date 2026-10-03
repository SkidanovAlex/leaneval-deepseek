/-
# The vocabulary of the `(2,2,1)` large-scale model estimate (area A6, §8)

This module fixes the vocabulary in which the target of
`Submission/Work/KMTPlan/A6/LowModelGainEstimate.lean`,

  `Work.KMTPlan.A6.LowModelGain P r C₀`
  (`LowBound P r C₀ (fun ρ a l₁ l₂ k₁ k₂ f g => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂)`),

is decomposed.

## What the target is

`mdlPart` (`lowLargeScaled.lean`) is the §6 model tuple of Krause--Mirek--Tao on the *large*
scales `N > splitCut ρ L` in the *main regime* `k + 2u ≤ Log N`:

  `mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
     = ∫_{1/2}^1 Btwist_{m_*}(T^{l₁}_{φ_{N,t}} F, T^{l₂}_{φ̃_{N,t}} G)(x) dt`,
  `N = ⌊a n⌋`, `F = piExact (kmtPj ρ) l₁ 0 f`, `G = piExact (kmtPj ρ) l₂ 0 g`,
  `m_* = mStarF u ⊗ mStargF d u`, `u = uScale ρ L`, `L = lcL l₁ l₂ k₁ k₂`.

The target asserts, for every `k₁ = 0 ∨ k₂ = 0` and every `(l₁,l₂)`, the bound

  `‖ (mdlPart_{…} n)_n ‖_{ℓ¹(ℤ; V^r)} ≤ K(Λ) · 2^{-c·L} · ‖f‖₂ ‖g‖₂`.

## The two halves of the proof

Following the paper's §8 (large scales, `all-all-large-2`) and §6 (`integ-ident`), the estimate
splits into two independent estimates and one reduction:

* **the gain in `l = max(l₁,l₂)`** — the arithmetic content (Theorem `bile`, i.e. the
  minor-arc/equidistribution of `(y,P(y))`).  It is available for the model tuple with *any*
  modified bumps `φ_{N,t,j}`, `j ∈ {-1,0,1}` (paper (pntj), (tpntj)), because those share the
  arithmetic height of the inputs; this is `MdlCoreGain` below.  Its exponent is the *polynomial
  loss* `lossWeight A ρ l₁ l₂ k₁ k₂ = ⟨L⟩^A 2^{A·ρL}` of area A7.
* **the gain in `k = max(k₁,k₂)` when `k > l`** — the `integ-ident` content of §6: the
  `t`-integral of the modulated tensor `φ_{N,t} ⊗ φ̃_{N,t}` acquires the factor `2^{-dk₂}`
  (identity (ii), used when `k₁ = 0`) or `2^{-s₁}` (identity (i), used when `k₂ = 0`), because
  the *other* parameter is at the bottom scale `-u = 0`.  This is exactly why the target is
  restricted to `k₁ = 0 ∨ k₂ = 0`.
* **the assembly** — the two cases `max k ≤ max l` (only the `l`-gain is needed) and
  `max k > max l` (the `k`-decay, then the `l`-gain), plus the absorption of the loss
  `lossWeight A ρ …` into the gain `2^{-c·L}` for `ρ` small.

Everything in this module is definitional (no proof is postulated).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowLargeDefs
import Submission.Work.KMTPlan.A6.IntegIdent

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract
open Work.KMTAreas.A7

/-! ## The core condition of the model tuple -/

/-- The condition under which `mdlPart` is non-zero: admissibility (`inIndexSet`), the large-scale
cut (`splitCut ρ L < N`) and the main regime of the §6 functional calculus (`mainRegime`).  It is
written with the same expression as in `mdlPart`, so that `mdlPart` unfolds to it definitionally. -/
def mdlCore (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ n : ℕ) : Prop :=
  inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
    Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) ∧
    Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n))

instance mdlCoreDecidable (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ n : ℕ) :
    Decidable (mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) := by unfold mdlCore; infer_instance

/-- `mdlCore` unfolds to the condition of `mdlPart`. -/
theorem mdlCore_iff (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ n : ℕ) :
    mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n ↔
      inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
        Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) ∧
        Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)) := by
  simp only [mdlCore, lcL]

/-- **Unfolding of `mdlPart` as an interval integral.** -/
theorem mdlPart_eq (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) (x : ℤ) :
    mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x =
      (if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
        ∫ t in (1 / 2 : ℝ)..1,
          Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
            (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
            (Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
            (Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x
      else 0) := rfl

/-- Off the core condition the model tuple vanishes. -/
theorem mdlPart_eq_zero_of_not_core (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (h : ¬ mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) :
    mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  rw [mdlPart_eq, if_neg h]

/-! ## The modified bumps `φ_{N,t,j}`, `φ̃_{N,t,j}` of the integration-by-parts identity -/

/-- The paper's modified bump `φ_{N,t,j}(ξ) = (2^{-k}Nξ)^j φ_{N,t}(ξ)` of (pntj).  For `j = 0`
this is `varphiNt`; the case `(k,j) = (0,-1)` is the one excluded by the paper's hypothesis
`(s,j) ≠ (-u,-1)` (there the factor `(Nξ)^{-1}` is singular at the frequency origin). -/
noncomputable def varphiNtj (N k : ℕ) (j : ℤ) (t : ℝ) : ℝ → ℂ :=
  fun ξ => ((((2 : ℝ) ^ (-(k : ℝ)) * (N : ℝ) * ξ : ℝ)) : ℂ) ^ j * varphiNt N k t ξ

/-- The paper's modified bump `φ̃_{N,t,j}(ξ) = (2^{-dk}N^dξ)^j φ̃_{N,t}(ξ)` of (tpntj). -/
noncomputable def varphitildeNtj (P : ℤ[X]) (N k : ℕ) (j : ℤ) (t : ℝ) : ℝ → ℂ :=
  fun ξ => ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * ξ : ℝ))
      : ℂ) ^ j * varphitildeNt P P.natDegree N k t ξ

/-- At `j = 0` the modified bump is the original bump. -/
theorem varphiNtj_zero (N k : ℕ) (t : ℝ) : varphiNtj N k 0 t = varphiNt N k t := by
  funext ξ
  simp [varphiNtj]

/-- At `j = 0` the modified bump is the original bump. -/
theorem varphitildeNtj_zero (P : ℤ[X]) (N k : ℕ) (t : ℝ) :
    varphitildeNtj P N k 0 t = varphitildeNt P P.natDegree N k t := by
  funext ξ
  simp [varphitildeNtj]

/-! ## The model tuple with modified bumps -/

/-- **The model tuple of §6/§8 with the modified bumps** `φ_{N,t,j₁}`, `φ̃_{N,t,j₂}`: on the core
condition it is

  `∫_{1/2}^1 Btwist_{m_*}(T^{l₁}_{φ_{N,t,j₁}} F, T^{l₂}_{φ̃_{N,t,j₂}} G) dt`,

`N = ⌊a n⌋`, `F = mdlF ρ l₁ f`, `G = mdlF ρ l₂ g`, and it vanishes off the core.  At
`(j₁,j₂) = (0,0)` it is `mdlPart` (`mdlPartJ_zero_zero`). -/
noncomputable def mdlPartJ (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
      ∫ t in (1 / 2 : ℝ)..1,
        Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t) (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
          (Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x
    else 0

/-- At `(j₁,j₂) = (0,0)` the modified model tuple is `mdlPart`. -/
theorem mdlPartJ_zero_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 = mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ := by
  funext n x
  rw [mdlPartJ, mdlPart_eq]
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · rw [if_pos h, if_pos h]
    simp only [varphiNtj_zero, varphitildeNtj_zero]
  · rw [if_neg h, if_neg h]

/-- Off the core the modified model tuple vanishes. -/
theorem mdlPartJ_eq_zero_of_not_core (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (n : ℕ) (x : ℤ)
    (h : ¬ mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) :
    mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n x = 0 := by
  rw [mdlPartJ, if_neg h]

/-! ## The constants and weights of the integration-by-parts identity -/

/-- The constant `(2πi)^{-1}` of the integration-by-parts identities. -/
noncomputable def mdlIota : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹

/-- The scale factor `2^{-d·k}` of the integration-by-parts identity (ii) on the `g`-side. -/
noncomputable def mdlScale (P : ℤ[X]) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ)))

/-- The scale factor `2^{k₁-d·k₂}` of the middle term of the identity (ii). -/
noncomputable def mdlScaleFe (P : ℤ[X]) (k₁ k₂ : ℕ) : ℝ :=
  (2 : ℝ) ^ ((k₁ : ℝ) - (P.natDegree : ℝ) * (k₂ : ℝ))

/-- The weight `N^{d-1}/P'(Nt)` of the integration-by-parts identity (ii). -/
noncomputable def mdlW1 (P : ℤ[X]) (N : ℕ) (t : ℝ) : ℂ :=
  (((N : ℝ) ^ (P.natDegree - 1) / PderivR P ((N : ℝ) * t) : ℝ) : ℂ)

/-- The weight `N^d P''(Nt)/P'(Nt)^2` of the last term of the identity (ii). -/
noncomputable def mdlW2 (P : ℤ[X]) (N : ℕ) (t : ℝ) : ℂ :=
  ((((N : ℝ) ^ P.natDegree * Pderiv2R P ((N : ℝ) * t))
      / (PderivR P ((N : ℝ) * t)) ^ 2 : ℝ) : ℂ)

/-- The scale factor `2^{-k}` of the boundary term of the identity (i). -/
noncomputable def mdlScaleF (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℝ))

/-- The scale factor `2^{d·k₂-k₁}` of the middle term of the identity (i). -/
noncomputable def mdlScaleFG (P : ℤ[X]) (k₁ k₂ : ℕ) : ℝ :=
  (2 : ℝ) ^ ((P.natDegree : ℝ) * (k₂ : ℝ) - (k₁ : ℝ))

/-- The scale factor `2^{k₁-d·k₂}` of the middle term of the identity (ii) (the reciprocal of
`mdlScaleFG`). -/
noncomputable def mdlScaleGe (P : ℤ[X]) (k₁ k₂ : ℕ) : ℝ :=
  (2 : ℝ) ^ ((k₁ : ℝ) - (P.natDegree : ℝ) * (k₂ : ℝ))

/-- The weight `P'(Nt)/N^{d-1}` of the middle term of the identity (i). -/
noncomputable def mdlW3 (P : ℤ[X]) (N : ℕ) (t : ℝ) : ℂ :=
  ((PderivR P ((N : ℝ) * t) / ((N : ℝ) ^ (P.natDegree - 1)) : ℝ) : ℂ)

/-! ## The frozen-`t` slices, and their core estimate -/

/-- **The frozen-`t` slice of the modified model tuple**: the family in `n` of
`Btwist_{m_*}(T^{l₁}_{φ_{N,t,j₁}}F, T^{l₂}_{φ̃_{N,t,j₂}}G)`, zero off the core condition. -/
noncomputable def mdlSliceJ (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
      Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t) (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
        (Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x
    else 0

theorem mdlSliceJ_apply (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) (n : ℕ) (x : ℤ) :
    mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x =
      if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
        Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t) (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
          (Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x
      else 0 := rfl

/-- **The model tuple is the `t`-integral of its frozen-`t` slices.** -/
theorem mdlPartJ_eq_intervalIntegral (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (n : ℕ) (x : ℤ) :
    mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n x =
      ∫ t in (1 / 2 : ℝ)..1,
        mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x := by
  rw [mdlPartJ]
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · simp only [if_pos h, mdlSliceJ_apply]
  · simp only [if_neg h, mdlSliceJ_apply]
    simp

/-- **The frozen-`t` core estimate of the large-scale model tuple** (paper Theorem
`model-est-2`, estimate `all-all-large-2` at `(p₁,p₂,p) = (2,2,1)`, *for each fixed*
`t ∈ [1/2,1]`): there are `c > 0`, `A ≥ 0`, `ρ₀ > 0` such that for every `ρ ∈ (0, ρ₀]` there is
`K : ℝ≥0 → ℝ≥0` with

  `‖ (mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n)_n ‖_{ℓ¹(ℤ; V^r)}
     ≤ K(Λ) · ⟨L⟩^A 2^{AρL} · 2^{-c·max(l₁,l₂)} · ‖f‖₂ ‖g‖₂`

for all `t ∈ [1/2,1]`, all `Λ`-lacunary `a` with `a n ≥ 1`, all quadruples `(l₁,l₂,k₁,k₂)` and all
`f g : ℤ → ℂ` satisfying the paper's non-singularity condition `(k_i,j_i) ≠ (0,-1)`.  The uniform
dependence on `t` is part of the paper's statement of `model-est-2`. -/
def MdlSliceCoreGain (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) (j₁ j₂ : ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
        eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
          1 Measure.count
          ≤ (K Λ : ℝ≥0∞) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(c * (max (l₁ : ℝ) (l₂ : ℝ))))) *
            eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

/-! ## The weighted slice families of the integration-by-parts reduction -/

/-- **The weighted frozen-`t` slice family** of the modified model tuple: the frozen-`t` slice
multiplied by a weight `w : ℕ → ℝ → ℂ` (the weights of `integ-ident` are
`w = mdlW1 P ⌊a n⌋ ·`, `mdlW2`, `mdlW3`), zero off the core condition. -/
noncomputable def mdlSliceW (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (w : ℕ → ℝ → ℂ) (t : ℝ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
      w n t * Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t) (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
        (Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x
    else 0

/-- **The `t`-integral of the weighted frozen slices**: the family
`n ↦ ∫_{1/2}^1 w n t · Btwist_{m_*}(T^{l₁}_{φ_{N,t,j₁}}F, T^{l₂}_{φ̃_{N,t,j₂}}G)(x) dt`, zero off
the core. -/
noncomputable def mdlWInt (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (w : ℕ → ℝ → ℂ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
      ∫ t in (1 / 2 : ℝ)..1,
        w n t * Btwist ρ P l₁ l₂ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t) (mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
          (Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) (mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x
    else 0

/-- With the constant weight `1`, `mdlWInt` is `mdlPartJ`. -/
theorem mdlWInt_one_eq_mdlPartJ (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) :
    mdlWInt ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ (fun _ _ => 1)
      = mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ := by
  funext n x
  rw [mdlWInt, mdlPartJ]
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · simp only [if_pos h]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp
  · simp only [if_neg h]

/-! ## The estimate into which the target is decomposed -/

/-- **The `l`-gain core of the large-scale model estimate** (paper Theorem `model-est-2`,
estimate `all-all-large-2`, at `(p₁,p₂,p) = (2,2,1)`, for the modified bumps
`(φ_{N,t,j₁}, φ̃_{N,t,j₂})`): there are `c > 0`, `A ≥ 0`, `ρ₀ > 0` such that for every
`ρ ∈ (0, ρ₀]` there is `K : ℝ≥0 → ℝ≥0` with

  `‖ (mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n)_n ‖_{ℓ¹(ℤ; V^r)}
     ≤ K(Λ) · ⟨L⟩^A 2^{AρL} · 2^{-c·max(l₁,l₂)} · ‖f‖₂ ‖g‖₂`

for all `Λ`-lacunary `a` with `a n ≥ 1`, all quadruples `(l₁,l₂,k₁,k₂)` and all `f g : ℤ → ℂ`
satisfying the paper's non-singularity condition `(k_i,j_i) ≠ (0,-1)`.

The gain `2^{-c·max(l₁,l₂)}` is the arithmetic content of §8 (Theorem `bile`): the inputs
`mdlF ρ l_i f = Π_{l_i,≤0} f` have exact arithmetic height `l_i`, so the arithmetic symbol
vanishes on the frequencies of lower height; the *extra* gain in `k` (when `max k > max l`) is
**not** part of this statement — it comes from the integration-by-parts identity applied in the
assembly. -/
def MdlCoreGain (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) (j₁ j₂ : ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
        eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ n x))
          1 Measure.count
          ≤ (K Λ : ℝ≥0∞) * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(c * (max (l₁ : ℝ) (l₂ : ℝ))))) *
            eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

end

end Work.KMTPlan.A6
