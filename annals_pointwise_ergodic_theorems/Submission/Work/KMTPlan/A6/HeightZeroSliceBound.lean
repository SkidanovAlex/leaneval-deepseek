import Mathlib
import Submission.Work.KMTAreas.A7.LoModelLargeScaleHolds
import Submission.Work.KMTAreas.A7Hi.LowpassDefs

/-!
# The height-`0` slice bound of the `g`-side model estimate (area A6, §8)

The target is the `(k₂,j₂) = (0,0)` instance of the paper's linear lacunary variational estimate
`(lin-2)` for the `g`-side of the §6 model: the masked family

  `n ↦ 1_{mdlCore ρ C₀ a l₁ l₂ k₁ 0 n} · Tle ρ 0 (φ̃_{⌊a n⌋,0,0,t}) h`

of the modulated `d`-fold bump `φ̃_{N,t} = varphitildeNtj P N 0 0 t = varphitildeNt P d N 0 t` is
bounded in `ℓ²(ℤ; V^R)` by `C · lossWeight A ρ l₁ l₂ k₁ 0 · ‖h‖_{ℓ²}`, uniformly in the `Λ`-lacunary
family `a`, in `t ∈ [1/2,1]`, in the parameters `l₁ l₂ k₁` and in `h`.

## Proof

`mdlCore` is the §5 index predicate `Work.KMTAreas.A7.core` (`mdlCore_iff_core`), and at `j = 0`
the modified bump is the plain modulated bump (`varphitildeNtj_zero`).  Hence the target is exactly
the statement `Work.KMTAreas.A7.LoGLinVarClipped` (`LoModelLargeScaleHolds.lean`) at `k₂ = 0`,
`p₂ = 2`, `r = R`: that lemma is the §8 `g`-side linear variational estimate, assembled there from

* the narrow strata `LoGFareyPartBound` (`k₂ ≥ 1`) and `LoGFareyDiffPartBound` (`k₂ = 0`, the
  low-frequency difference `φ̃_{N,t} - φ̃_N`),
* the unmodulated low-pass `LoGLowpassClipped` (from the proved `A7G.plainBumpVarG`),
* the non-narrow scales `LoGBadPartVar`,

with the loss exponent `4`.  All that is left here is the translation of the vocabulary
(`mdlCore ↦ core`, `varphitildeNtj ↦ varphitildeNt`) and the arithmetic of the `ℝ≥0∞` factor
`ofReal (C · lossWeight) = ofReal C · ofReal (lossWeight)`.
-/

set_option autoImplicit false

namespace Work.KMTPlan.A6

/-- The model index predicate `mdlCore` of the `(2,2,1)` model tuple is the §5 index predicate
`Work.KMTAreas.A7.core` (they differ only in the spelling of the height `L = max (max l₁ l₂)
(max k₁ k₂)`, via `lcL`). -/
lemma mdlCore_iff_core (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) :
    mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n ↔ Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n := by
  rw [mdlCore_iff, Work.KMTAreas.A7.core, lcL]

theorem HeightZeroSliceBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (Λ : NNReal) (hΛ : 1 < Λ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))),
        ∃ C : ℝ, 0 < C ∧
          ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ : ℕ) (t : ℝ) (h : ℤ → ℂ),
            PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            t ∈ Set.Icc (1 / 2 : ℝ) 1 →
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
                (fun n : ℕ =>
                  if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then
                    Work.KMTAreas.A7.Tle ρ 0
                      (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t) h x
                  else 0)) 2 MeasureTheory.Measure.count
              ≤ ENNReal.ofReal C * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ 0) *
                  MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count := by
  -- The §8 `g`-side linear variational estimate at the exponent `2` and the loss exponent `4`.
  refine ⟨4, by norm_num, ?_⟩
  intro Λ hΛ ρ hρ hρ1 hρC
  obtain ⟨C, hCpos, hC⟩ :=
    Work.KMTAreas.A7.LoGLinVarClipped P hd C₀ hC₀ ρ hρ hρ1 hρC 2 (by norm_num) (by norm_num)
      R hR Λ hΛ
  refine ⟨C, hCpos, ?_⟩
  intro a l₁ l₂ k₁ t h ha ha1 ht
  have hmain := hC a ha ha1 l₁ l₂ k₁ 0 t ht h
  -- Translate the vocabulary: `mdlCore ↦ core` and `varphitildeNtj P N 0 0 t ↦ varphitildeNt`.
  have hfam : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then
            Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t) h x
          else 0))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ =>
          if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ 0 a n then
            Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) h x
          else 0)) := by
    funext x
    congr 1
    funext n
    have hiff := mdlCore_iff_core ρ C₀ a l₁ l₂ k₁ 0 n
    by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n
    · rw [if_pos hc, if_pos (hiff.mp hc), varphitildeNtj_zero]
    · rw [if_neg hc, if_neg (fun hh => hc (hiff.mpr hh))]
  rw [hfam]
  refine hmain.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hCpos.le]

end Work.KMTPlan.A6
