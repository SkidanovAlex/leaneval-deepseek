/-
# Ionescu--Wainger facts about the modulated KMT bump `φ_{N,t}`

This module records the three Ionescu--Wainger facts about the modulated bump
`varphiNt N k t` (`Large/Defs.lean`) that the §6--§8 chapters need at a *fixed* parameter
`(N,k,t)`:

* the symbol `ξ ↦ ∑_{α ∈ (ℚ/ℤ)_{≤l}} (periodize φ_{N,t})(ξ - α)` is integrable on the circle
  (it is in `L^∞`, because `φ_{N,t}` is a compactly supported bounded function, so its
  periodisation is a finite sum of its translates);
* the kernel `iwKernel` of that symbol decays like `j^{-2}`: `φ_{N,t}` is `C²` with compact
  support, so the same holds for its translates, and the Poisson-summation form of the kernel
  (`iwKernel_periodize_fourier`) plus the two integrations by parts
  (`FourierDecayExplicit`, exposed as `iwKernel_decay_of_bump`) give the quadratic decay;
* the translates `j ↦ φ_{N,t}(x + j)` are summable for fixed `x`, since only the (finitely many)
  integers `j` with `|x + j| ≤ 2^{k - Log N}` contribute.

The analytic input is `Work.KMTAreas.A7.varphiNt_bounds` (smoothness, compact support, support
radius) together with `Work.KMTAreas.A7.iwKernel_decay_of_bump`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FpieceEqTm
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## Pointwise bounds for the bump -/

/-- The unmodulated KMT bump is bounded by `2` (a difference of two cutoffs bounded by `1`). -/
private lemma norm_varphiN_le_two (N k : ℕ) (ξ : ℝ) : ‖varphiN N k ξ‖ ≤ 2 := by
  by_cases hk : k = 0
  · simp only [varphiN, if_pos hk]
    exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · simp only [varphiN, if_neg hk]
    calc ‖Work.KMTContract.kmtEta (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)
            - Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ)‖
        ≤ ‖Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)‖
          + ‖Work.KMTContract.kmtEta
              (((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ)‖ :=
          norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (Work.KMTContract.norm_kmtEta_le _)
          (Work.KMTContract.norm_kmtEta_le _)
      _ = 2 := by norm_num

/-- The modulated bump is bounded by `2` (the modulation `e(Ntξ)` is unimodular). -/
private lemma norm_varphiNt_le_two (N k : ℕ) (t : ℝ) (ξ : ℝ) : ‖varphiNt N k t ξ‖ ≤ 2 := by
  rw [varphiNt, norm_mul, norm_ee, mul_one]
  exact norm_varphiN_le_two N k ξ

/-! ## Summability of the translates -/

/-- For fixed `x`, only finitely many translates `φ_{N,t}(x + j)`, `j ∈ ℤ`, are nonzero (those
with `|x + j| ≤ 2^{k - Log N}`), so the family is summable. -/
private lemma summable_varphiNt_shift (N k : ℕ) (t x : ℝ) :
    Summable (fun j : ℤ => varphiNt N k t (x + j)) := by
  set K : ℕ := Nat.ceil (|x| + (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
    with hKdef
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(K : ℤ)) (K : ℤ)) (fun j hj => ?_)
  by_contra hne
  have hmem : |x + (j : ℝ)| ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
    varphiNt_support N k t _ hne
  have hKle : |x| + (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤ (K : ℝ) := by
    rw [hKdef]; exact Nat.le_ceil _
  have hj' : |(j : ℝ)| ≤ (K : ℝ) := by
    calc |(j : ℝ)| = |(x + (j : ℝ)) + (-x)| := by ring_nf
      _ ≤ |x + (j : ℝ)| + |-x| := abs_add_le _ _
      _ = |x + (j : ℝ)| + |x| := by rw [abs_neg]
      _ ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) + |x| := by linarith
      _ = |x| + (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by ring
      _ ≤ (K : ℝ) := hKle
  have habs : (|j| : ℤ) ≤ (K : ℤ) := by
    rw [← Int.cast_le (R := ℝ), Int.cast_abs]
    exact_mod_cast hj'
  exact absurd (abs_le.mp habs) (by simpa [Finset.mem_Icc] using hj)

/-! ## The target -/

theorem varphiNt_IW_facts (ρ : ℝ) (l N k : ℕ) (t : ℝ) :
    MeasureTheory.Integrable
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k t)))
        Work.Analysis.IonescuWainger.circleMeasure ∧
      (∃ C : ℝ, 0 < C ∧ ∀ j : ℤ,
        ‖Work.Analysis.IWMultiplier.iwKernel
            (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
              (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt N k t))) j‖
          ≤ C / (1 + |(j : ℝ)|) ^ 2) ∧
      (∀ x : ℝ, Summable (fun j : ℤ => Work.KMTAreas.A7.varphiNt N k t (x + j))) := by
  have hRpos : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hFsupp : ∀ x : ℝ, (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < |x| →
      varphiNt N k t x = 0 := by
    intro x hx
    by_contra hne
    exact absurd (varphiNt_support N k t x hne) (not_le.mpr hx)
  have hFbdd : ∀ x : ℝ, ‖varphiNt N k t x‖ ≤ 2 := fun x => norm_varphiNt_le_two N k t x
  have hFmeas : Measurable (varphiNt N k t) := (contDiff_varphiNt N k t).continuous.measurable
  set S : ℝ := max (∫ y, ‖varphiNt N k t y‖)
    (∫ y, ‖iteratedDeriv 2 (fun ξ => varphiNt N k t ξ) y‖) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact le_max_of_le_left (integral_nonneg (fun y => norm_nonneg _))
  have hS1 : (∫ y, ‖varphiNt N k t y‖) ≤ S := by
    rw [hSdef]; exact le_max_left _ _
  have hS2 : (∫ y, ‖iteratedDeriv 2 (fun ξ => varphiNt N k t ξ) y‖) ≤ S := by
    rw [hSdef]; exact le_max_right _ _
  -- Integrability of the IW symbol on the circle.
  have hInt : MeasureTheory.Integrable
      (iwSymbolSet (iwArithFreqs ρ l) (periodize (varphiNt N k t))) circleMeasure :=
    (memLp_iwSymbolSet (iwArithFreqs ρ l)
      (memLp_periodize hFmeas hRpos.le hFsupp hFbdd)).integrable le_top
  -- Quaratic decay of the kernel of that symbol.
  have hdec : ∀ j : ℤ,
      ‖iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (varphiNt N k t))) j‖
        ≤ (4 * (((iwArithFreqs ρ l).card : ℝ) * S) + 1) / (1 + |(j : ℝ)|) ^ 2 := by
    intro j
    have h := iwKernel_decay_of_bump (iwArithFreqs ρ l) (contDiff_varphiNt N k t)
      (hasCompactSupport_varphiNt N k t) hSnn hS1 hS2 j
    rw [norm_kmtKernWeight j, mul_one_div] at h
    exact h
  refine ⟨hInt, ⟨4 * (((iwArithFreqs ρ l).card : ℝ) * S) + 1, ?_, ?_⟩, ?_⟩
  · have hcard : (0 : ℝ) ≤ ((iwArithFreqs ρ l).card : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ ((iwArithFreqs ρ l).card : ℝ) * S := mul_nonneg hcard hSnn
    linarith
  · intro j
    exact hdec j
  · intro x
    exact summable_varphiNt_shift N k t x

end Work.KMTAreas.A7
