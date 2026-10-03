/-
# The wiring of the frozen-`t` core estimate `MdlSliceCoreGain` (area A6), KMTPlan-side

`Work.KMTPlan.A6.MdlSliceCoreGainBig` (`Submission/Work/KMTPlan/A6/MdlSliceCoreGainBig.lean`)
is the target of the area's §8 assembly: the paper's Theorem `model-est-2`, estimate
`all-all-large-2` at `(p₁,p₂,p) = (2,2,1)`, for the frozen slice `mdlSliceJ`.

This module carries the *proof* of that statement.  The statement itself stays in
`MdlSliceCoreGainBig` (it is the name the rest of the tree uses); the file calls
`Work.KMTPlan.A6Lead.MdlSliceCoreGainWired` below.

## The two inputs

The assembly below is the one of `Work.KMTPlan.A6Clean.MdlSliceCoreGainMemLp_of_pieces_split`
(`KMTPlan/A6/MdlSliceGatedSelf.lean`), which reduces the `ℓ²`-case to two inputs:

* **the gated §8 adelic form** `AdelicFormPropRangePosB P hd hA1 hI B`, supplied by
  `Work.KMTPlan.A6Lead.adelicFormPropRangePosBLead` (`A6Lead/adelicFormGatedLead.lean`) — the
  *corrected* producer, whose degenerate branch (`l₁ = 0 ∨ l₂ = 0`) is split into its three
  sub-cases, each supplied with the regime hypothesis that the gate `B ρ ≤ lcL l₁ l₂ k₁ k₂`
  yields;
* **the loss-form (no-gain) slice bound** `MdlSliceNoGainAt P hd hA1 C₀ r j₁ j₂`, supplied by the
  PROVED `Work.KMTPlan.A6LH.MdlSliceNoGainAtProved` (`KMTPlan/A6LH/MdlSliceNoGainAtProved.lean`,
  axiom-clean).  This is the bound used on the data *below* the gate, where the arithmetic gain is
  a `ρ`-constant; on the data above the gate the adelic form supplies it.

Everything else used here is proved and axiom-clean: the `ZMod Q` variational chain
`ZModVariationalChainProb`, the finitely many bad scales `MdlSliceBadPart`, the loss absorption
`lossAbsorbTwo`, the case-splitting consumer `MdlSliceCoreGainMemLp_of_pieces_split`, the
`C₀ = 0` reduction `MdlSliceCoreGainMemLp_c₀_zero` and the `ℓ²`-reduction
`MdlSliceCoreGain_of_memLp` (all in the cycle-free definitions module
`Submission/Work/A6Big/Defs.lean` / `KMTPlan/A6/MdlSliceGatedSelf.lean`).

## The exponent reduction

The arithmetic inputs hold only on the paper's range `2 < r < 2d/(d-1) = adelicRTop P`; the target
is stated for `2 < r` with the same right-hand side (the constants absorb the change of exponent),
and `variationalNorm` is antitone in the exponent, so it suffices to prove the `ℓ²`-case at some
`2 < r' ≤ r` with `r' < adelicRTop P` — `exists_range_le_vrLead` below.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlSliceGatedSelf
import Submission.Work.KMTPlan.A6LH.MdlSliceNoGainAtProved
import Submission.Work.KMTPlan.A6Lead.adelicFormGatedLead

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6Lead

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

noncomputable section

/-- **The variation part of `variationalNorm` is antitone in the variation exponent.** -/
lemma variationalNorm_antitone_vrLead {p s : ℝ≥0} (hp : 1 ≤ p) (hps : p ≤ s) (a : ℕ → ℂ) :
    variationalNorm s a ≤ variationalNorm p a := by
  rw [variationalNorm_eq_add, variationalNorm_eq_add]
  exact add_le_add le_rfl (Work.Analysis.Variation.varPart_antitone hp hps a)

/-- **Monotonicity of the `ℓ²`-case of the target in the variation exponent.** -/
lemma MdlSliceCoreGainMemLp_of_le_vrLead {P : Polynomial ℤ} {r r' : ℝ≥0} {C₀ : ℕ} {j₁ j₂ : ℤ}
    (h1 : 1 ≤ r') (hle : r' ≤ r)
    (h : Work.KMTPlan.A6.MdlSliceCoreGainMemLp P r' C₀ j₁ j₂) :
    Work.KMTPlan.A6.MdlSliceCoreGainMemLp P r C₀ j₁ j₂ := by
  obtain ⟨c, hc, A, hA, ρ₀, hρ₀, h'⟩ := h
  refine ⟨c, hc, A, hA, ρ₀, hρ₀, ?_⟩
  intro ρ hρ hρle
  obtain ⟨K, hK⟩ := h' ρ hρ hρle
  refine ⟨K, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg
  have hmono : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 Measure.count
      ≤ eLpNorm (fun x : ℤ => variationalNorm r'
        (fun n : ℕ => Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 Measure.count := by
    rw [Work.KMTPlan.A6.eLpNorm_one_count_variationalNorm r,
      Work.KMTPlan.A6.eLpNorm_one_count_variationalNorm r']
    exact ENNReal.tsum_le_tsum fun x => variationalNorm_antitone_vrLead h1 hle _
  exact hmono.trans (hK a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg)

/-- **There is always an exponent in the paper's range `(2, 2d/(d-1))` below a given `r > 2`.** -/
lemma exists_range_le_vrLead (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : ℝ≥0) (hr : 2 < r) :
    ∃ r' : ℝ≥0, 2 < r' ∧ r' ≤ r ∧ (r' : ℝ) < Work.KMTPlan.A6.adelicRTop P := by
  have hT : 2 < Work.KMTPlan.A6.adelicRTop P := Work.KMTPlan.A6.two_lt_adelicRTop hd
  set r₀ : ℝ := min (r : ℝ) ((2 + Work.KMTPlan.A6.adelicRTop P) / 2) with hr₀
  have hr₀nn : 0 ≤ r₀ := by
    rw [hr₀]
    exact le_min (NNReal.coe_nonneg r) (by linarith)
  have h2r₀ : 2 < r₀ := by
    rw [hr₀]
    exact lt_min (by exact_mod_cast hr) (by linarith)
  have hr₀le : r₀ ≤ (r : ℝ) := by rw [hr₀]; exact min_le_left _ _
  have hr₀T : r₀ < Work.KMTPlan.A6.adelicRTop P := by
    rw [hr₀]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  exact ⟨⟨r₀, hr₀nn⟩, h2r₀, hr₀le, hr₀T⟩

/-- **The assembly of the `ℓ²`-case of the frozen-slice estimate from the two inputs.** -/
theorem MdlSliceCoreGainMemLpWired (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1)
    (hI : Work.KMTContract.ImprovKMT P)
    (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) :
    Work.KMTPlan.A6.MdlSliceCoreGainMemLp P r C₀ j₁ j₂ := by
  -- the paper's exponent range `2 < r' < 2d/(d-1)` (where the arithmetic estimates hold)
  obtain ⟨r', hr'2, hr'le, hr'T⟩ := exists_range_le_vrLead P hd r hr
  have hr'1 : (1 : NNReal) ≤ r' := le_trans (by norm_num) hr'2.le
  refine MdlSliceCoreGainMemLp_of_le_vrLead hr'1 hr'le ?_
  -- the gated §8 adelic form (a `ρ`-only threshold `B`) and the loss-form bound
  obtain ⟨B, hB⟩ := adelicFormPropRangePosBLead P hd hA1 hI
  have hNoGain : ∀ (C₀' : ℕ), 1 ≤ C₀' → ∀ (r'' : NNReal), 2 < r'' → ∀ (j₁' j₂' : ℤ),
      j₁' ∈ ({-1, 0, 1} : Finset ℤ) → j₂' ∈ ({-1, 0, 1} : Finset ℤ) →
      Work.KMTPlan.A6Clean.MdlSliceNoGainAt P hd hA1 C₀' r'' j₁' j₂' :=
    fun C₀' hC₀' r'' hr'' j₁' j₂' hj₁' hj₂' =>
      Work.KMTPlan.A6LH.MdlSliceNoGainAtProved P hd hA1 C₀' hC₀' r'' hr'' j₁' j₂' hj₁' hj₂'
  rcases Nat.eq_zero_or_pos C₀ with hC0 | hCpos
  · subst hC0
    refine Work.KMTPlan.A6Clean.MdlSliceCoreGainMemLp_c₀_zero P hr'1 ?_
    exact Work.KMTPlan.A6Clean.MdlSliceCoreGainMemLp_of_pieces_split P hd hA1 hI B hB hNoGain
      Work.KMTPlan.A6.ZModVariationalChainProb (Work.KMTPlan.A6.MdlSliceBadPart P hd hA1 hI)
      Work.KMTPlan.A6.lossAbsorbTwo r' hr'2 hr'T j₁ j₂ hj₁ hj₂ 1 le_rfl
  · exact Work.KMTPlan.A6Clean.MdlSliceCoreGainMemLp_of_pieces_split P hd hA1 hI B hB hNoGain
      Work.KMTPlan.A6.ZModVariationalChainProb (Work.KMTPlan.A6.MdlSliceBadPart P hd hA1 hI)
      Work.KMTPlan.A6.lossAbsorbTwo r' hr'2 hr'T j₁ j₂ hj₁ hj₂ C₀ hCpos

/-- **The frozen-`t` core estimate** (the paper's Theorem `model-est-2`, estimate
`all-all-large-2` at `(2,2,1)`), from the two inputs above. -/
theorem MdlSliceCoreGainWired (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1)
    (hI : Work.KMTContract.ImprovKMT P)
    (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) :
    Work.KMTPlan.A6.MdlSliceCoreGain P r C₀ j₁ j₂ :=
  Work.KMTPlan.A6.MdlSliceCoreGain_of_memLp P r (le_trans (by norm_num) hr.le) C₀ j₁ j₂
    (MdlSliceCoreGainMemLpWired P hd r hr C₀ hC₀ hA1 hI j₁ j₂ hj₁ hj₂)

end

end Work.KMTPlan.A6Lead
