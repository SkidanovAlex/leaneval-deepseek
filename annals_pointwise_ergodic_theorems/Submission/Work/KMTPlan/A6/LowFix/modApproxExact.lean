import Mathlib
import Submission.Work.KMTPlan.A6.modelWeightInvLeGain
import Submission.Work.KMTPlan.A6.ModApproxErrCoreNonAliasingU
import Submission.Work.KMTPlan.A6.LowFix.noAliasingCaseU

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.LowFix

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract Work.KMTAreas Work.KMTAreas.A7
open Work.Analysis.IWMultiplier Work.Analysis.IonescuWainger

/-!
# ⚠ READ `NOTES_A6_LowModApproxExactEstimate_DEFECT.md` FIRST

**The single-scale core `ModApproxErrCoreExact` / `KernelMassBoundA6`, to which this file wires the
target, is FALSE.** `mdlPart` pins the paper's free auxiliary-scale constant (`u = uScale ρ L`) and
uses the height-`≤ l` arithmetic kernel `arithKernel`; in the core regime (`splitCut ρ L < N`, and
`N` *unbounded* when `L` is bounded) the model's symbol then acquires, at each concrete spike
`γ ∈ diffFreqs × diffFreqs`, the aliasing terms `Σ_{α ≠ γ, |α-γ| ≤ 2^{-2u}} mZ(α)·Φ₁Φ₂·m̃`, which
have no counterpart in the concrete column and whose kernel mass is `N`-independent (hence the
asserted `N⁻¹` gain fails).  Explicit configuration: `ρ = 1/6`, `P = X²`, `l₁ = l₂ = 3`,
`k₁ = k₂ = 0`: `u = 2`, window radius `1/16`, while `2/5, 3/7 ∈ diffFreqs ρ 3` are `1/35` apart and
`mZ X² 840 (3/7) (3/7) ≠ 0`; `vpcCore` holds for every `N > 16`.  This is the same defect the A7
area declared FALSE for the sibling `Work.KMTAreas.A7.HiMassBound`
(`NOTES_A7_HiMassBoundHolds_VERDICT.md`), repaired there by the free constant
`uRep = max (uScale ρ L) (max l₁ l₂ + 3)`, the exact-height kernel `BtwistExact` and a `bandCond`
guard.

**The variational target `LowModApprox` is very probably TRUE** (the aliasing term is asymptotically
constant in the scale index, so only its transient reaches the `r`-variation), but **not by this
route**.  The corrected decomposition (`NOTES_..._DEFECT.md` §3) is: (A)
`Work.KMTPlan.A6.ModApproxErrCoreNonAliasing` — the single-scale `N⁻¹` bound under
`NonAliasing (-(2·uScale ρ L)) (A_{l₁} ∪ A_{l₂})` plus the *strict* plateau
`max k₁ k₂ + 2·uScale ρ L + 1 ≤ logN N` (delegated, PROVABLE from the proved collapses +
`symD_deriv_bound`); (B) `Work.KMTPlan.A6.LowModApproxNoAliasingCase` — the variational bound in the
complement of (A)'s hypotheses, where `lcL ≤ B(ρ)` and the defect is absorbed by `K(Λ)` (delegated);
(C) the dichotomy + constant-merging assembly, still to be written in this file.  The proof below is
valid as an implication but its hypothesis is unprovable.

# The low-case model approximation with the exact-height model

This file reduces the target `Work.KMTPlan.A6.LowModApprox P r C₀` — the model-approximation
estimate `mod-approx` of Krause--Mirek--Tao §6 at `(2,2,1)`, in the low case `k₁ = 0 ∨ k₂ = 0`,
summed over the large lacunary scales with the exponential gain `2^{-c L}` — to the *single-scale*
core `ModApproxErrCore`: the paper's single-scale estimate at the exact-height model `mdlPart`.
**(WARNING: that core is FALSE — see the box above.)**

The passage to the summed estimate is the §5 bookkeeping:

* `modApproxErr = mainPartTuple − mdlPart` vanishes identically off the core condition
  `CoreCond`, so the sum over the scales may be restricted to the index set;
* on the index set `L = max (max l₁ l₂) (max k₁ k₂) ≤ l_{(N)}`, so the reciprocal sum
  `∑_n ⌊a n⌋⁻¹` is bounded by `D(Λ)·2^{-2^{L/C₀}+2}` (`A7.invFloorSum_le`);
* the doubly exponential decay of that sum beats the weight `modelWeight A ρ L L L L` of the
  single-scale estimate and leaves the exponential gain `2^{-cL}` (`lmae_modelWeight_gain`).
-/

/-- **The single-scale model approximation of the exact-height model.**  There are `ρ₀ > 0` and,
for every `ρ ∈ (0,ρ₀]`, an exponent `A ≥ 0` and a constant `C : ℝ≥0 → ℝ≥0` such that at every
lacunary scale `N = ⌊a n⌋`

  `‖ modApproxErr_n ‖_{ℓ¹(ℤ)} ≤ C(Λ) · ⟨L⟩^A 2^{A·2^{ρL}} · N⁻¹ · ‖f‖₂ ‖g‖₂`,

with `L = max (max l₁ l₂) (max k₁ k₂)`.  Both tuples vanish identically off the core condition,
so the estimate has no content there.  This is the paper's Proposition `mod-approx` at `(2,2)`
(composed with the functional calculus `bn-ident`), in the regime in which the paper applies it. -/
def ModApproxErrCore (P : ℤ[X]) (C₀ : ℕ) : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ A : ℝ, 0 ≤ A ∧ ∃ C : ℝ≥0 → ℝ≥0,
    ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
      MemLp f 2 Measure.count → MemLp g 2 Measure.count → ∀ n : ℕ,
      eLpNorm (modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n) 1 Measure.count
        ≤ (C Λ : ℝ≥0∞) * ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂)
            * ENNReal.ofReal (((Nat.floor (a n) : ℕ) : ℝ)⁻¹)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

/-- **The single-scale model approximation in the non-aliasing case.**  Same shape as
`ModApproxErrCore`, but the estimate is required only under the two extra hypotheses that make the
model's arithmetic kernel collapse onto the exact-height fibres of the concrete column:

* `NonAliasing (-(uScale ρ L)) (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ l₂)` — the arithmetic
  frequencies of the two sides are separated at the *window* radius `2^{-uScale ρ L}` of `m_*`.
  **This is the scale at which `Work.KMTPlan.A6.mdlPart_eq_bilinOp_maeKmod` (PROVED) and the fibre
  collapse need non-aliasing; the weaker `-2·uScale ρ L` does not imply it**
  (`NOTES_A6_ModApproxErrCoreNonAliasing_VERDICT.md` §1--§3);
* the *strict* plateau `max k₁ k₂ + 2·uScale ρ L + 1 ≤ (logN ⌊a n⌋).toNat` at the scale `n`.

This is the `GOOD` case of the corrected decomposition
(`NOTES_A6_LowModApproxExactEstimate_DEFECT.md` §3); it is proved by
`Work.KMTPlan.A6.ModApproxErrCoreNonAliasingU`. -/
def ModApproxErrCoreNAU (P : ℤ[X]) (C₀ : ℕ) : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ A : ℝ, 0 ≤ A ∧ ∃ C : ℝ≥0 → ℝ≥0,
    ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
      MemLp f 2 Measure.count → MemLp g 2 Measure.count → ∀ n,
      NonAliasing (-(uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))
        (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ l₂) →
      max k₁ k₂ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1 ≤ (logN (Nat.floor (a n))).toNat →
      eLpNorm (modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n) 1 Measure.count
        ≤ (C Λ : ℝ≥0∞) * ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂)
            * ENNReal.ofReal (((Nat.floor (a n) : ℕ) : ℝ)⁻¹)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

/-! ## The core condition (reproduced locally)

The `A7` model-approximation chapter has been restructured and its `CoreCond` no longer exists;
the condition under which the two tuples `mainPartTuple` and `mdlPart` can be non-zero is
reproduced here, with exactly the body of the `A7` definition. -/

/-- The condition under which the two tuples of the model approximation are non-zero. -/
def CoreCondA6 (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) : Prop :=
  inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
    Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) ∧
    Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n))

instance (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ n : ℕ) :
    Decidable (CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n) := by
  unfold CoreCondA6
  infer_instance

/-- **The case (A) predicate** of the corrected decomposition: the arithmetic frequencies are
separated at the *window* scale `-(uScale ρ L)` (`GOOD`), and the strict plateau holds at every
core scale.

**The scale is `-uScale ρ L`, not `-2 · uScale ρ L`.**  This is the correction found by the
delegated analysis of `Work.KMTPlan.A6.ModApproxErrCoreNonAliasing`
(`NOTES_A6_ModApproxErrCoreNonAliasing_VERDICT.md` §3): the functional calculus `bn-ident`
(`Work.KMTPlan.A6.mdlPart_eq_bilinOp_maeKmod`, PROVED) needs non-aliasing at the window scale
`-uScale ρ L`; the weaker `-2 · uScale` hypothesis does not imply it, and `NonAliasing` is
monotone from a larger scale to a smaller one only.

Its complement (`¬NonAliasing (-uScale ρ L)` at a core scale, or the plateau failing there) is
*exactly* the defect hypothesis of `Work.KMTPlan.A6.LowModApproxNoAliasingCaseU`, so the two cases
exhaust the possibilities and cover the whole low-case quadruple. -/
def MaeCaseA (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) : Prop :=
  NonAliasing (-(uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))
      (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ l₂) ∧
    ∀ n, CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n →
      max k₁ k₂ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1 ≤ (logN (Nat.floor (a n))).toNat

/-! ## The vanishing of the two tuples on degenerate inputs -/

/-- `Btwist` vanishes on a zero first argument. -/
lemma lmae_Btwist_zero_left (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (v : ℤ → ℂ) :
    Btwist ρ P l₁ l₂ m₁ m₂ 0 v = 0 := by
  funext x
  simp [Btwist, tsum_zero]

/-- `Btwist` vanishes on a zero second argument. -/
lemma lmae_Btwist_zero_right (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (u : ℤ → ℂ) :
    Btwist ρ P l₁ l₂ m₁ m₂ u 0 = 0 := by
  funext x
  simp [Btwist, tsum_zero]

/-- A height-`≤ l` Ionescu--Wainger multiplier kills the zero function. -/
lemma lmae_Tle_zero (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) : Tle ρ l φ (0 : ℤ → ℂ) = 0 := by
  funext n
  simp [Tle, iwConv, tsum_zero]

/-- The height-`l` projection of the zero function is zero. -/
lemma lmae_kmtProj_zero (ρ : ℝ) (l : ℕ) (k : ℤ) : kmtProj ρ l k (0 : ℤ → ℂ) = 0 := by
  funext n
  simp [kmtProj, iwConv, tsum_zero]

/-- The exact-height shell of the zero function is zero. -/
lemma lmae_piExact_kmtPj_zero (ρ : ℝ) (l : ℕ) (k : ℤ) :
    piExact (kmtPj ρ) l k (0 : ℤ → ℂ) = 0 := by
  unfold piExact
  split <;> simp [lmae_kmtProj_zero]

/-- `mdlF ρ u l 0 = 0`. -/
lemma lmae_mdlF_zero (ρ : ℝ) (u l : ℕ) : mdlF ρ u l (0 : ℤ → ℂ) = 0 :=
  lmae_piExact_kmtPj_zero ρ l _

/-- `mdlG ρ P u l 0 = 0`. -/
lemma lmae_mdlG_zero (ρ : ℝ) (P : ℤ[X]) (u l : ℕ) : mdlG ρ P u l (0 : ℤ → ℂ) = 0 :=
  lmae_piExact_kmtPj_zero ρ l _

/-- The continuous-frequency piece of the zero function is zero. -/
lemma lmae_piece_kmtPj_zero (ρ : ℝ) (l : ℕ) (κ : ℤ → ℤ) (a s : ℤ) :
    piece (kmtPj ρ) l κ a s (0 : ℤ → ℂ) = 0 := by
  unfold piece
  split
  · exact lmae_piExact_kmtPj_zero ρ l _
  · simp [lmae_piExact_kmtPj_zero]

/-- **The model part vanishes on a zero second argument.** -/
lemma lmae_mdlPart_eq_zero_of_right_eq_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) (hg : g = 0) :
    mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  subst hg
  unfold mdlPart
  split
  · refine (intervalIntegral.integral_congr (fun t _ => ?_)).trans
      intervalIntegral.integral_zero
    simp only [lmae_mdlG_zero, lmae_Tle_zero, lmae_Btwist_zero_right, Pi.zero_apply]
  · rfl

/-- **The main part vanishes on a zero second argument.** -/
lemma lmae_mainPartTuple_eq_zero_of_right_eq_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) (hg : g = 0) :
    mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  subst hg
  unfold mainPartTuple
  split
  · rw [varpPiece]
    have hG : Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n))
        (0 : ℤ → ℂ) = 0 := by
      rw [Gpiece]
      exact lmae_piece_kmtPj_zero ρ l₂ _ _ _
    rw [hG]
    unfold AhalfR Ahalf Ablock
    simp
  · rfl

/-- **The model-approximation error vanishes on a zero second argument.** -/
lemma lmae_modApproxErr_eq_zero_of_right_eq_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) (hg : g = 0) :
    modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  simp only [modApproxErr,
    lmae_mainPartTuple_eq_zero_of_right_eq_zero ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hg,
    lmae_mdlPart_eq_zero_of_right_eq_zero ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hg, sub_self]

/-- **The model part vanishes on a zero first argument.** -/
lemma lmae_mdlPart_eq_zero_of_left_eq_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) (hf : f = 0) :
    mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  subst hf
  unfold mdlPart
  split
  · refine (intervalIntegral.integral_congr (fun t _ => ?_)).trans
      intervalIntegral.integral_zero
    simp only [lmae_mdlF_zero, lmae_Tle_zero, lmae_Btwist_zero_left, Pi.zero_apply]
  · rfl

/-- **The main part vanishes on a zero first argument.** -/
lemma lmae_mainPartTuple_eq_zero_of_left_eq_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) (hf : f = 0) :
    mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  subst hf
  unfold mainPartTuple
  split
  · rw [varpPiece]
    have hF : Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) (0 : ℤ → ℂ) = 0 := by
      rw [Fpiece]
      exact lmae_piece_kmtPj_zero ρ l₁ _ _ _
    rw [hF]
    unfold AhalfR Ahalf Ablock
    simp
  · rfl

/-- **The model-approximation error vanishes on a zero first argument.** -/
lemma lmae_modApproxErr_eq_zero_of_left_eq_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) (hf : f = 0) :
    modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  simp only [modApproxErr,
    lmae_mainPartTuple_eq_zero_of_left_eq_zero ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hf,
    lmae_mdlPart_eq_zero_of_left_eq_zero ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hf, sub_self]

/-- A function with vanishing `ℓ²` norm is zero (for the counting measure on `ℤ`). -/
lemma lmae_eq_zero_of_eLpNorm_eq_zero {f : ℤ → ℂ} (h : eLpNorm f 2 Measure.count = 0) :
    f = 0 := by
  have h1 : f =ᵐ[Measure.count] 0 :=
    (eLpNorm_eq_zero_iff
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp h
  have h2 : Measure.count {y : ℤ | f y ≠ 0} = 0 := ae_iff.mp h1
  funext x
  by_contra hx
  have h3 : Measure.count ({x} : Set ℤ) ≤ Measure.count {y : ℤ | f y ≠ 0} :=
    measure_mono (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      exact hy ▸ hx)
  have hsingle : Measure.count ({x} : Set ℤ) = (1 : ℝ≥0∞) := by
    rw [← Finset.coe_singleton, Measure.count_apply_finset ({x} : Finset ℤ)]
    simp
  have h4 : (1 : ℝ≥0∞) ≤ 0 := by
    rw [← hsingle]
    exact le_trans h3 (le_of_eq h2)
  exact absurd h4 (not_le.mpr zero_lt_one)

/-! ## The bookkeeping of the weights -/

/-- The core condition forces `L = lcL l₁ l₂ k₁ k₂ ≤ l_{(N)}`. -/
lemma lmae_lcL_le_heightScale_of_core {ρ : ℝ} {C₀ : ℕ} {a : ℕ → ℝ≥0} {l₁ l₂ k₁ k₂ n : ℕ}
    (h : CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n) :
    lcL l₁ l₂ k₁ k₂ ≤ heightScale C₀ (Nat.floor (a n)) := by
  have h' : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) := h.1
  rw [inIndexSet_iff_le] at h'
  obtain ⟨h1, h2, h3, h4⟩ := h'
  simp only [lcL]
  exact max_le (max_le h1 h2) (max_le h3 h4)

/-- The core condition forces the model-approximation error to vanish off it. -/
lemma lmae_modApproxErr_eq_zero_of_not_core (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (h : ¬ CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n) :
    modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  have h1 : mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
    unfold Work.KMTAreas.A7.mainPartTuple
    split
    · rename_i hc
      exact absurd (show CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n from hc) h
    · rfl
  have h2 : mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
    unfold mdlPart
    split
    · rename_i hc
      exact absurd (show CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n from hc) h
    · rfl
  simp only [modApproxErr, h1, h2, sub_self]

/-- `lmaxR l₁ l₂ k₁ k₂` is the `ℝ`-valued `lcL`. -/
lemma lmae_lmaxR_eq_lcL (l₁ l₂ k₁ k₂ : ℕ) :
    lmaxR l₁ l₂ k₁ k₂ = (lcL l₁ l₂ k₁ k₂ : ℝ) := by
  rw [lmaxR, ← lcL_eq]
  norm_cast

/-- `lmaxR L L L L = L`. -/
lemma lmae_lmaxR_diag (L : ℕ) : lmaxR L L L L = (L : ℝ) := by
  rw [lmae_lmaxR_eq_lcL]
  simp [lcL]

/-- `modelWeight` depends on the quadruple only through `lcL`. -/
lemma lmae_modelWeight_eq_lcL (A ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    modelWeight A ρ l₁ l₂ k₁ k₂
      = modelWeight A ρ (lcL l₁ l₂ k₁ k₂) (lcL l₁ l₂ k₁ k₂) (lcL l₁ l₂ k₁ k₂)
          (lcL l₁ l₂ k₁ k₂) := by
  simp only [modelWeight, lmae_lmaxR_eq_lcL, lcL, max_self]

/-- `lcWeight` depends on the quadruple only through `lcL`. -/
lemma lmae_lcWeight_eq_lcL (c : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lcWeight c l₁ l₂ k₁ k₂ = (2 : ℝ) ^ (-(c * (lcL l₁ l₂ k₁ k₂ : ℝ))) := by
  rw [lcWeight, ← lcL_eq]
  norm_cast

/-- `modelWeight A ρ L L L L` is monotone in `L` for `A ≥ 0`, `ρ ≥ 0`. -/
lemma lmae_modelWeight_diag_mono (A ρ : ℝ) (hA : 0 ≤ A) (hρ : 0 ≤ ρ) :
    Monotone (fun L : ℕ => modelWeight A ρ L L L L) := by
  intro L M hLM
  have h1 : (L : ℝ) ≤ (M : ℝ) := by exact_mod_cast hLM
  simp only [modelWeight, lmae_lmaxR_diag]
  have hbase : (1 + (L : ℝ)) ≤ (1 + (M : ℝ)) := by linarith
  refine mul_le_mul (Real.rpow_le_rpow (by linarith) hbase hA) ?_
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) A)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  refine mul_le_mul_of_nonneg_left ?_ hA
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

/-- **The doubly exponential decay of the reciprocal sum beats the weight.**  There is `K ≥ 0`
with `modelWeight A ρ L L L L · (E · 2^{-2^{L/C₀}+2}) ≤ K · 2^{-cL}` for every `L`. -/
lemma lmae_modelWeight_gain (A c ρ : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (hρ : 0 < ρ)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hρC : 2 * ρ * (C₀ : ℝ) ≤ 1 / 4) (E : ℝ) (hE : 0 ≤ E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℕ,
      modelWeight A ρ L L L L * (E * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2))
        ≤ K * (2 : ℝ) ^ (-(c * (L : ℝ))) := by
  obtain ⟨B₁, hB₁⟩ := modelWeightInvLeGain (A + 2) c ρ (by linarith) hc hρ (C₀ : ℝ)
    (by exact_mod_cast hC₀) hρC
  obtain ⟨B₂, hB₂⟩ := exists_nat_ge (max 1 (Real.sqrt (4 * E)))
  refine ⟨max 1 (modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂)
    * (E * 4) * (2 : ℝ) ^ (c * ((max B₁ B₂ : ℕ) : ℝ))),
    le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro L
  by_cases hL : L ≤ max B₁ B₂
  · -- small scales: absorb into the constant
    have hmw : modelWeight A ρ L L L L
        ≤ modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) :=
      lmae_modelWeight_diag_mono A ρ hA hρ.le hL
    have hE4 : (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2) ≤ 4 := by
      have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) := Real.rpow_nonneg (by norm_num) _
      have h1 : -(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2 ≤ (2 : ℝ) := by linarith
      calc (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
        _ = 4 := by norm_num
    have hE4' : 0 ≤ E * 4 := by linarith
    have hgain : (2 : ℝ) ^ (-(c * ((max B₁ B₂ : ℕ) : ℝ))) ≤ (2 : ℝ) ^ (-(c * (L : ℝ))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hle : (L : ℝ) ≤ ((max B₁ B₂ : ℕ) : ℝ) := by exact_mod_cast hL
      nlinarith [mul_le_mul_of_nonneg_left hle hc.le]
    have hmul : modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) * (E * 4)
        ≤ max 1 (modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) * (E * 4)
            * (2 : ℝ) ^ (c * ((max B₁ B₂ : ℕ) : ℝ))) * (2 : ℝ) ^ (-(c * (L : ℝ))) := by
      have hK : modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) * (E * 4)
          * (2 : ℝ) ^ (c * ((max B₁ B₂ : ℕ) : ℝ))
          ≤ max 1 (modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) * (E * 4)
              * (2 : ℝ) ^ (c * ((max B₁ B₂ : ℕ) : ℝ))) := le_max_right _ _
      have h3 : (2 : ℝ) ^ (-(c * ((max B₁ B₂ : ℕ) : ℝ)))
            * (2 : ℝ) ^ (c * ((max B₁ B₂ : ℕ) : ℝ)) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          show -(c * ((max B₁ B₂ : ℕ) : ℝ)) + c * ((max B₁ B₂ : ℕ) : ℝ) = 0 by ring,
          Real.rpow_zero]
      calc modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) * (E * 4)
          = modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) * (E * 4)
              * ((2 : ℝ) ^ (-(c * ((max B₁ B₂ : ℕ) : ℝ)))
                * (2 : ℝ) ^ (c * ((max B₁ B₂ : ℕ) : ℝ))) := by rw [h3, mul_one]
        _ = (modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) * (E * 4)
              * (2 : ℝ) ^ (c * ((max B₁ B₂ : ℕ) : ℝ)))
              * (2 : ℝ) ^ (-(c * ((max B₁ B₂ : ℕ) : ℝ))) := by ring
        _ ≤ max 1 (modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) * (E * 4)
              * (2 : ℝ) ^ (c * ((max B₁ B₂ : ℕ) : ℝ))) * (2 : ℝ) ^ (-(c * (L : ℝ))) :=
            mul_le_mul hK hgain (by positivity) (le_trans (by norm_num) (le_max_left _ _))
    calc modelWeight A ρ L L L L * (E * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2))
        ≤ modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) * (E * 4) := by
          refine mul_le_mul hmw (mul_le_mul_of_nonneg_left hE4 hE) (by positivity)
            (modelWeight_nonneg A ρ hA _ _ _ _)
      _ ≤ _ := hmul
  · -- large scales: the doubly exponential factor beats the weight
    have hBL : max B₁ B₂ < L := not_le.mp hL
    have hLB₁ : B₁ ≤ L := le_trans (le_max_left _ _) (le_of_lt hBL)
    have hLB₂ : B₂ ≤ L := le_trans (le_max_right _ _) (le_of_lt hBL)
    have hcore := hB₁ L hLB₁
    have hs : Real.sqrt (4 * E) ≤ (L : ℝ) := by
      have h1 : Real.sqrt (4 * E) ≤ (B₂ : ℝ) := le_trans (le_max_right _ _) hB₂
      have h2 : (B₂ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLB₂
      linarith
    have hsq : 4 * E ≤ (1 + (L : ℝ)) ^ (2 : ℝ) := by
      have h1 : Real.sqrt (4 * E) ≤ 1 + (L : ℝ) := by linarith
      have h2 : (Real.sqrt (4 * E)) ^ 2 ≤ (1 + (L : ℝ)) ^ 2 := by
        have h2' : (0 : ℝ) ≤ 1 + (L : ℝ) := by positivity
        nlinarith [mul_le_mul h1 h1 (Real.sqrt_nonneg _) h2']
      have h3 : (Real.sqrt (4 * E)) ^ 2 = 4 * E := Real.sq_sqrt (by linarith)
      have h4 : (1 + (L : ℝ)) ^ 2 = (1 + (L : ℝ)) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc 4 * E = (Real.sqrt (4 * E)) ^ 2 := h3.symm
        _ ≤ (1 + (L : ℝ)) ^ 2 := h2
        _ = (1 + (L : ℝ)) ^ (2 : ℝ) := h4
    have hbase1 : (0 : ℝ) < 1 + (L : ℝ) := by
      have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      linarith
    have hmw : modelWeight A ρ L L L L * (4 * E) ≤ modelWeight (A + 2) ρ L L L L := by
      simp only [modelWeight, lmae_lmaxR_diag]
      have h1 : (1 + (L : ℝ)) ^ A * (4 * E) ≤ (1 + (L : ℝ)) ^ (A + 2) := by
        calc (1 + (L : ℝ)) ^ A * (4 * E)
            ≤ (1 + (L : ℝ)) ^ A * (1 + (L : ℝ)) ^ (2 : ℝ) :=
              mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg (by linarith) A)
          _ = (1 + (L : ℝ)) ^ (A + 2) := by
              rw [← Real.rpow_add hbase1]
      have h4 : (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * (L : ℝ)))
          ≤ (2 : ℝ) ^ ((A + 2) * (2 : ℝ) ^ (ρ * (L : ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have h5 : 0 ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := Real.rpow_nonneg (by norm_num) _
        nlinarith
      calc (1 + (L : ℝ)) ^ A * (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * (L : ℝ))) * (4 * E)
          = ((1 + (L : ℝ)) ^ A * (4 * E)) * (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * (L : ℝ))) := by ring
        _ ≤ (1 + (L : ℝ)) ^ (A + 2) * (2 : ℝ) ^ ((A + 2) * (2 : ℝ) ^ (ρ * (L : ℝ))) :=
            mul_le_mul h1 h4 (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _)
    have hE2 : (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2)
        ≤ 4 * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) := by
      have hmono : (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)))
          ≤ (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have h3 : (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2) ≤ (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        linarith
      have h4 : (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2)
          = 4 * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) := by
        rw [show -(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2
            = (2 : ℝ) + (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [h4]
      nlinarith [hmono]
    have hstep : modelWeight A ρ L L L L * (E * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2))
        ≤ modelWeight (A + 2) ρ L L L L * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) := by
      have h1 : E * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2)
          ≤ (4 * E) * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) := by
        nlinarith [mul_le_mul_of_nonneg_left hE2 hE]
      calc modelWeight A ρ L L L L * (E * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2))
          ≤ modelWeight A ρ L L L L
              * ((4 * E) * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2))) :=
            mul_le_mul_of_nonneg_left h1 (modelWeight_nonneg A ρ hA _ _ _ _)
        _ = (modelWeight A ρ L L L L * (4 * E))
              * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) := by ring
        _ ≤ modelWeight (A + 2) ρ L L L L
              * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) :=
            mul_le_mul_of_nonneg_right hmw (by positivity)
    have hK1 : (1 : ℝ) ≤ max 1 (modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂)
        * (E * 4) * (2 : ℝ) ^ (c * ((max B₁ B₂ : ℕ) : ℝ))) := le_max_left _ _
    calc modelWeight A ρ L L L L * (E * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ)) + 2))
        ≤ modelWeight (A + 2) ρ L L L L * (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) := hstep
      _ = (2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) * modelWeight (A + 2) ρ L L L L := by ring
      _ ≤ (2 : ℝ) ^ (-(c * (L : ℝ))) := hcore
      _ ≤ max 1 (modelWeight A ρ (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) (max B₁ B₂) * (E * 4)
            * (2 : ℝ) ^ (c * ((max B₁ B₂ : ℕ) : ℝ))) * (2 : ℝ) ^ (-(c * (L : ℝ))) := by
          have h1 : (0 : ℝ) < (2 : ℝ) ^ (-(c * (L : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
          nlinarith [hK1, h1]

/-! ## The variational norm of a vanishing family -/

/-- The `ℓ¹(ℤ)` norm of the variational norm of a family vanishing pointwise is zero. -/
lemma lmae_eLpNorm_variationalNorm_eq_zero {r : ℝ≥0} (hr : 1 ≤ r) {u : ℕ → ℤ → ℂ} (h : u = 0) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x)) 1 Measure.count = 0 := by
  have hz : ∀ n : ℕ, eLpNorm (fun x : ℤ => u n x) 1 Measure.count = 0 := by
    intro n
    rw [show (fun x : ℤ => u n x) = 0 from funext (fun x => by simp [h]), eLpNorm_zero]
  have hV := eLpNorm_variationalNorm_one_le_tsum (r := r) hr u
  have hsum : (∑' n : ℕ, eLpNorm (fun x : ℤ => u n x) 1 Measure.count) = 0 := by
    simp [hz]
  rw [hsum, mul_zero] at hV
  exact le_antisymm hV (zero_le : (0 : ℝ≥0∞) ≤ _)

/-- Auxiliary `ENNReal` computation: the right-hand side is infinite as soon as one of the two
norms is infinite and the weight is non-zero. -/
lemma lmae_rhs_eq_top {K w F G : ℝ≥0∞} (hK : K ≠ 0) (hw : w ≠ 0) (hF0 : F ≠ 0) (hG0 : G ≠ 0)
    (h : F = ⊤ ∨ G = ⊤) : K * w * F * G = ⊤ := by
  rcases h with hF | hG
  · rw [hF]
    rw [ENNReal.mul_top (ne_of_gt (ENNReal.mul_pos hK hw))]
    exact ENNReal.top_mul hG0
  · rw [hG]
    rw [ENNReal.mul_top (ne_of_gt (ENNReal.mul_pos (ne_of_gt (ENNReal.mul_pos hK hw)) hF0))]

/-- Auxiliary `ENNReal` monotonicity. -/
lemma lmae_mul_le_mul_of_le_of_le {A B C D : ℝ≥0∞} (h1 : A ≤ B) (h2 : C ≤ D) :
    A * C ≤ B * D :=
  mul_le_mul h1 h2 (zero_le : (0 : ℝ≥0∞) ≤ C) (zero_le : (0 : ℝ≥0∞) ≤ B)

/-! ## The reduction of the target to the single-scale core -/

/-- **The §5 bookkeeping, from a conditioned single-scale bound.**

Given the single-scale estimate

  `‖ modApproxErr_n ‖_{ℓ¹} ≤ C(Λ)·modelWeight A ρ l₁ l₂ k₁ k₂ · ⌊a n⌋⁻¹ · ‖f‖₂‖g‖₂`  (at core `n`)

for a fixed `ρ`, this produces the constant `K` of the summed (variational) estimate with the
exponential gain `2^{-L}`.  The proof is the §5 bookkeeping: the error vanishes off `CoreCond`,
the height condition `L ≤ l_{(N)}` bounds `∑_{n} ⌊a n⌋⁻¹` by `D(Λ)·2^{-2^{L/C₀}+2}`
(`A7.invFloorSum_le`), and the double exponential decay beats the weight
`modelWeight A ρ L L L L`, leaving the exponential gain `2^{-L}` (`lmae_modelWeight_gain`).

The per-scale hypothesis is indexed by the core condition, and is allowed to depend on an extra
predicate `Q` of the quadruple (and of `a`), so that it can be instantiated either
unconditionally (`ModApproxErrCore`, with `Q := True`) or under the case-(A) side conditions
(`ModApproxErrCoreNAU`, with `Q := MaeCaseA`: the non-aliasing and strict-plateau hypotheses). -/
theorem lowModApprox_assembly (P : ℤ[X]) (r : ℝ≥0) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (ρ : ℝ) (hρ : 0 < ρ) (hρC : 2 * ρ * (C₀ : ℝ) ≤ 1 / 4) (A : ℝ) (hA : 0 ≤ A)
    (C : ℝ≥0 → ℝ≥0)
    (Q : (ℕ → ℝ≥0) → ℝ≥0 → ℕ → ℕ → ℕ → ℕ → Prop)
    (hb : ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
      Q a Λ l₁ l₂ k₁ k₂ →
      MemLp f 2 Measure.count → MemLp g 2 Measure.count → ∀ n,
      CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n →
      eLpNorm (fun x : ℤ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count
        ≤ (C Λ : ℝ≥0∞) * ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂)
            * ENNReal.ofReal (((Nat.floor (a n) : ℕ) : ℝ)⁻¹)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) :
    ∃ K : ℝ≥0 → ℝ≥0, ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
      Q a Λ l₁ l₂ k₁ k₂ →
      eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
        ≤ (K Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
  -- the constant of the reciprocal-sum bound, depending on `Λ`
  set D : ℝ≥0 → ℝ := fun Λ => if h : 1 < Λ then Classical.choose (invFloorSum_le C₀ hC₀ Λ h)
    else 0 with hDdef
  have hD0 : ∀ Λ : ℝ≥0, 0 ≤ D Λ := by
    intro Λ
    rw [hDdef]
    by_cases h : 1 < Λ
    · simp only [dif_pos h]
      exact (Classical.choose_spec (invFloorSum_le C₀ hC₀ Λ h)).1
    · simp only [dif_neg h]
      exact le_rfl
  have hDb : ∀ (Λ : ℝ≥0), 1 < Λ → ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → ℝ≥0),
      Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∑' n : ℕ, (if L ≤ heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
        ≤ D Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) := by
    intro Λ hΛ L hL a ha ha1
    rw [hDdef]
    simp only [dif_pos hΛ]
    exact (Classical.choose_spec (invFloorSum_le C₀ hC₀ Λ hΛ)).2 L hL a ha ha1
  -- the constant of the index-set restriction
  set E : ℝ≥0 → ℝ := fun Λ => max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (D Λ) with hEdef
  have hE0 : ∀ Λ : ℝ≥0, 0 ≤ E Λ := by
    intro Λ
    rw [hEdef]
    exact le_trans (hD0 Λ) (le_max_right _ _)
  -- the arithmetic constant
  set Kc : ℝ≥0 → ℝ := fun Λ =>
    Classical.choose (lmae_modelWeight_gain A 1 ρ hA one_pos hρ C₀ hC₀ hρC (E Λ) (hE0 Λ))
    with hKcdef
  have hKc0 : ∀ Λ : ℝ≥0, 0 ≤ Kc Λ := by
    intro Λ
    rw [hKcdef]
    exact (Classical.choose_spec
      (lmae_modelWeight_gain A 1 ρ hA one_pos hρ C₀ hC₀ hρC (E Λ) (hE0 Λ))).1
  have hKcb : ∀ Λ : ℝ≥0, ∀ L : ℕ,
      modelWeight A ρ L L L L * (E Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2))
        ≤ Kc Λ * (2 : ℝ) ^ (-(1 * (L : ℝ))) := by
    intro Λ L
    rw [hKcdef]
    exact (Classical.choose_spec
      (lmae_modelWeight_gain A 1 ρ hA one_pos hρ C₀ hC₀ hρC (E Λ) (hE0 Λ))).2 L
  -- the weighted constant
  set Kfun : ℝ≥0 → ℝ≥0 := fun Λ => ⟨3 * (C Λ : ℝ) * Kc Λ + 1, by
    have h1 := hKc0 Λ
    have h2 : (0 : ℝ) ≤ (C Λ : ℝ) := NNReal.coe_nonneg (C Λ)
    nlinarith⟩ with hKfundef
  have hKfun_val : ∀ Λ : ℝ≥0, ((Kfun Λ : ℝ≥0) : ℝ≥0∞)
      = ENNReal.ofReal (3 * (C Λ : ℝ) * Kc Λ + 1) := by
    intro Λ
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  have hKfun_ne : ∀ Λ : ℝ≥0, ((Kfun Λ : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    intro Λ
    rw [hKfun_val Λ]
    refine ENNReal.ofReal_ne_zero_iff.mpr ?_
    have h1 := hKc0 Λ
    have h2 : (0 : ℝ) ≤ (C Λ : ℝ) := NNReal.coe_nonneg (C Λ)
    nlinarith
  have hKc_eq : ∀ Λ : ℝ≥0, ENNReal.ofReal (3 * (C Λ : ℝ) * Kc Λ)
      = (3 : ℝ≥0∞) * (C Λ : ℝ≥0∞) * ENNReal.ofReal (Kc Λ) := by
    intro Λ
    have key1 : ENNReal.ofReal (3 * (C Λ : ℝ) * Kc Λ)
        = ENNReal.ofReal (3 * (C Λ : ℝ)) * ENNReal.ofReal (Kc Λ) :=
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 * (C Λ : ℝ))
    have key2 : ENNReal.ofReal (3 * (C Λ : ℝ)) = (3 : ℝ≥0∞) * (C Λ : ℝ≥0∞) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ← ENNReal.coe_nnreal_eq (C Λ),
        ENNReal.ofReal_ofNat]
    calc ENNReal.ofReal (3 * (C Λ : ℝ) * Kc Λ)
        = ENNReal.ofReal (3 * (C Λ : ℝ)) * ENNReal.ofReal (Kc Λ) := key1
      _ = ((3 : ℝ≥0∞) * (C Λ : ℝ≥0∞)) * ENNReal.ofReal (Kc Λ) := by rw [key2]
      _ = (3 : ℝ≥0∞) * (C Λ : ℝ≥0∞) * ENNReal.ofReal (Kc Λ) := rfl
  have hKc_le : ∀ Λ : ℝ≥0, (3 : ℝ≥0∞) * (C Λ : ℝ≥0∞) * ENNReal.ofReal (Kc Λ)
      ≤ ((Kfun Λ : ℝ≥0) : ℝ≥0∞) := by
    intro Λ
    rw [hKfun_val Λ, ← hKc_eq Λ]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨Kfun, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ hQc
  have hr1 : (1 : ℝ≥0) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  set F : ℝ≥0∞ := eLpNorm f 2 Measure.count with hFdef
  set G : ℝ≥0∞ := eLpNorm g 2 Measure.count with hGdef
  set L : ℕ := lcL l₁ l₂ k₁ k₂ with hLdef
  set X : ℝ≥0∞ := (C Λ : ℝ≥0∞) * ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂) * F * G
    with hXdef
  have hwne : ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (by rw [lcWeight]; exact Real.rpow_pos_of_pos (by norm_num) _)
  by_cases hF0 : F = 0
  · have hf : f = 0 := by
      refine lmae_eq_zero_of_eLpNorm_eq_zero ?_
      rw [← hFdef]; exact hF0
    have hzero : (fun n : ℕ => fun x : ℤ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
      funext n x
      exact lmae_modApproxErr_eq_zero_of_left_eq_zero ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hf
    rw [lmae_eLpNorm_variationalNorm_eq_zero hr1 hzero]
    exact bot_le
  by_cases hG0 : G = 0
  · have hg : g = 0 := by
      refine lmae_eq_zero_of_eLpNorm_eq_zero ?_
      rw [← hGdef]; exact hG0
    have hzero : (fun n : ℕ => fun x : ℤ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
      funext n x
      exact lmae_modApproxErr_eq_zero_of_right_eq_zero ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hg
    rw [lmae_eLpNorm_variationalNorm_eq_zero hr1 hzero]
    exact bot_le
  by_cases hFtop : F = ⊤
  · have hRHS : ((Kfun Λ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) * F * G = ⊤ :=
      lmae_rhs_eq_top (hKfun_ne Λ) hwne hF0 hG0 (Or.inl hFtop)
    rw [hRHS]; exact le_top
  by_cases hGtop : G = ⊤
  · have hRHS : ((Kfun Λ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) * F * G = ⊤ :=
      lmae_rhs_eq_top (hKfun_ne Λ) hwne hF0 hG0 (Or.inr hGtop)
    rw [hRHS]; exact le_top
  -- the main case: both norms are finite and non-zero
  have hf : MemLp f 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr (by rw [← hFdef]; exact hFtop))
  have hg : MemLp g 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr (by rw [← hGdef]; exact hGtop))
  have hLbound : ∀ n : ℕ, CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n → L ≤ heightScale C₀ (Nat.floor (a n)) := by
    intro n hn
    rw [hLdef]
    exact lmae_lcL_le_heightScale_of_core hn
  -- the summability of the truncated reciprocal sum
  have hS : (∑' n : ℕ, ENNReal.ofReal (if CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n
        then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
      ≤ ENNReal.ofReal (E Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)) := by
    have h1 : (∑' n : ℕ, ENNReal.ofReal (if CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n
          then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
        = (∑' n : ℕ, if CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n
            then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0) := by
      refine tsum_congr (fun n => ?_)
      by_cases hc : CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, ENNReal.ofReal_zero]
    rw [h1]
    refine tsum_ite_floor_le_indexSet C₀ hC₀ Λ hΛ (D Λ) (hD0 Λ) (hDb Λ hΛ) L (E Λ) ?_ a ha ha1
      (fun n => CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n) hLbound
    rw [hEdef]
  -- the per-scale core bound, truncated to the core condition
  have htsum : (∑' n : ℕ,
        eLpNorm (fun x : ℤ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count)
      ≤ X * (∑' n : ℕ, ENNReal.ofReal (if CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n
            then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0)) := by
    have h1 : ∀ n : ℕ,
        eLpNorm (fun x : ℤ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count
          ≤ ENNReal.ofReal (if CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n
              then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0) * X := by
      intro n
      by_cases hc : CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n
      · rw [if_pos hc]
        have hbound := hb a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ hQc hf hg n hc
        calc eLpNorm (fun x : ℤ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count
            ≤ (C Λ : ℝ≥0∞) * ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂)
                * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) * F * G := by
              rw [hFdef, hGdef]; exact hbound
          _ = ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) * X := by
              rw [hXdef]; ac_rfl
      · rw [if_neg hc]
        have hz : (fun x : ℤ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 :=
          funext (fun x => lmae_modApproxErr_eq_zero_of_not_core ρ P C₀ a f g l₁ l₂ k₁ k₂ n x hc)
        rw [hz, eLpNorm_zero]
        exact bot_le
    calc (∑' n : ℕ, eLpNorm (fun x : ℤ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            1 Measure.count)
        ≤ ∑' n : ℕ, (ENNReal.ofReal (if CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n
              then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0) * X) := ENNReal.tsum_le_tsum h1
      _ = X * (∑' n : ℕ, ENNReal.ofReal (if CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n
              then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0)) := by
            rw [ENNReal.tsum_mul_right, mul_comm]
  -- the weight arithmetic, in `ℝ`
  have harith : modelWeight A ρ l₁ l₂ k₁ k₂
      * (E Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2))
        ≤ Kc Λ * lcWeight 1 l₁ l₂ k₁ k₂ := by
    have h := hKcb Λ L
    have h2 : modelWeight A ρ L L L L = modelWeight A ρ l₁ l₂ k₁ k₂ := by
      rw [hLdef]
      exact (lmae_modelWeight_eq_lcL A ρ l₁ l₂ k₁ k₂).symm
    have h3 : (2 : ℝ) ^ (-(1 * (L : ℝ))) = lcWeight 1 l₁ l₂ k₁ k₂ := by
      rw [hLdef, lmae_lcWeight_eq_lcL]
    rw [h2, h3] at h
    exact h
  -- the weight arithmetic, in `ℝ≥0∞`
  have h1 : ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂)
      * ENNReal.ofReal (E Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2))
      ≤ ENNReal.ofReal (Kc Λ) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) := by
    calc ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂)
          * ENNReal.ofReal (E Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2))
        = ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂
            * (E Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2))) := by
          rw [ENNReal.ofReal_mul (modelWeight_nonneg A ρ hA _ _ _ _)]
      _ ≤ ENNReal.ofReal (Kc Λ * lcWeight 1 l₁ l₂ k₁ k₂) := ENNReal.ofReal_le_ofReal harith
      _ = ENNReal.ofReal (Kc Λ) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) := by
          rw [ENNReal.ofReal_mul (hKc0 Λ)]
  have hV := eLpNorm_variationalNorm_one_le_tsum (r := r) (le_trans (by norm_num) (le_of_lt hr))
    (fun n : ℕ => fun x : ℤ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
  calc eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
      ≤ 3 * (∑' n : ℕ, eLpNorm (fun x : ℤ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          1 Measure.count) := hV
    _ ≤ 3 * (X * (∑' n : ℕ, ENNReal.ofReal (if CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n
            then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))) :=
          lmae_mul_le_mul_of_le_of_le (le_refl _) htsum
    _ ≤ 3 * (X * ENNReal.ofReal (E Λ
          * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2))) :=
          lmae_mul_le_mul_of_le_of_le (le_refl _) (lmae_mul_le_mul_of_le_of_le (le_refl _) hS)
    _ ≤ ((Kfun Λ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) * F * G := by
          calc 3 * (X * ENNReal.ofReal (E Λ
                * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)))
              = ((3 : ℝ≥0∞) * (C Λ : ℝ≥0∞)
                  * (ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂)
                    * ENNReal.ofReal (E Λ
                      * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2)))) * (F * G) := by
                rw [hXdef]; ac_rfl
            _ ≤ ((3 : ℝ≥0∞) * (C Λ : ℝ≥0∞)
                  * (ENNReal.ofReal (Kc Λ)
                    * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂))) * (F * G) :=
                lmae_mul_le_mul_of_le_of_le
                  (lmae_mul_le_mul_of_le_of_le (le_refl _) h1) (le_refl _)
            _ = ((((3 : ℝ≥0∞) * (C Λ : ℝ≥0∞)) * ENNReal.ofReal (Kc Λ))
                  * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂)) * (F * G) := by
                ac_rfl
            _ ≤ (((Kfun Λ : ℝ≥0) : ℝ≥0∞)
                  * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂)) * (F * G) :=
                lmae_mul_le_mul_of_le_of_le
                  (lmae_mul_le_mul_of_le_of_le (hKc_le Λ) (le_refl _)) (le_refl _)
            _ = ((Kfun Λ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) * F * G := by
                ac_rfl

/-- **`LowModApprox`, case (A)**: the non-aliasing case.  On the `GOOD` side (arithmetic
frequencies separated at the plateau radius, and the strict plateau at every core scale) the
single-scale bound `ModApproxErrCoreNA` holds, and the §5 bookkeeping of `lowModApprox_assembly`
upgrades it to the summed (variational) estimate with the gain `1`. -/
theorem lowModApprox_of_nonAliasingCore (P : ℤ[X]) (r : ℝ≥0) (hr : 2 < r) (C₀ : ℕ)
    (hC₀ : 1 ≤ C₀) (hcore : ModApproxErrCoreNAU P C₀) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
        MaeCaseA ρ C₀ a l₁ l₂ k₁ k₂ →
        eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
          ≤ (K Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) *
              eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
  obtain ⟨ρc, hρc, H⟩ := hcore
  refine ⟨min ρc (1 / (8 * (C₀ : ℝ))), lt_min hρc (by positivity), ?_⟩
  intro ρ hρ hρle
  have hρc' : ρ ≤ ρc := le_trans hρle (min_le_left _ _)
  have hρ8 : ρ ≤ 1 / (8 * (C₀ : ℝ)) := le_trans hρle (min_le_right _ _)
  have hρC : 2 * ρ * (C₀ : ℝ) ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (C₀ : ℝ))] at hρ8
    nlinarith
  obtain ⟨A, hA, C, hC⟩ := H ρ hρ hρc'
  exact lowModApprox_assembly P r hr C₀ hC₀ ρ hρ hρC A hA C
    (fun a _ l₁ l₂ k₁ k₂ => MaeCaseA ρ C₀ a l₁ l₂ k₁ k₂)
    (fun a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ hcase hf hg n hc =>
      hC a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ hf hg n hcase.1 (hcase.2 n hc))

/-- **The dichotomy, assembled.**  `LowModApprox P r C₀` follows from the two halves of the
corrected decomposition (`NOTES_A6_LowModApproxU_ASSEMBLY.md` §3):

* `hA` — the case-(A) single-scale core `ModApproxErrCoreNAU` (the `N⁻¹` bound under non-aliasing
  at the window scale `-uScale ρ L` and the strict plateau); the §5 bookkeeping
  (`lowModApprox_of_nonAliasingCore`) turns it into the estimate with the gain `1`;
* `hB` — the case-(B) estimate: the complement of the case predicate (`¬NonAliasing (-uScale ρ L)`,
  or the plateau failing at a core scale) gives the same shape with a `ρ`-dependent gain;
* the two are merged with `c := min 1 c₂`, `ρ₀ := min ρ₀A ρ₀B`, `K := fun Λ => max (K₁ Λ) (K₂ Λ)`,
  the `lcWeight` monotonicity `lcWeight_le_of_le` and the excluded middle on `MaeCaseA` (which is
  convertible to the disjunction of `hB`'s hypothesis by classical logic). -/
theorem lowModApprox_of_dichotomy (P : ℤ[X]) (r : ℝ≥0) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hA : ModApproxErrCoreNAU P C₀)
    (hB : ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ K : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
        (¬ NonAliasing (-(uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))
              (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ l₂)
          ∨ ∃ n : ℕ, inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
                (Nat.floor (a n))
              ∧ splitCut ρ (lcL l₁ l₂ k₁ k₂) < Nat.floor (a n)
              ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n))
              ∧ ¬ (max k₁ k₂ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
                  ≤ (logN (Nat.floor (a n))).toNat)) →
        eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
          ≤ (K Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
              * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) :
    LowModApprox P r C₀ := by
  classical
  obtain ⟨ρA, hρA, hA'⟩ := lowModApprox_of_nonAliasingCore P r hr C₀ hC₀ hA
  obtain ⟨c₂, hc₂, ρ₂, hρ₂, hB'⟩ := hB
  refine ⟨min 1 c₂, lt_min one_pos hc₂, min ρA ρ₂, lt_min hρA hρ₂, ?_⟩
  intro ρ hρ hρle
  have hρA'' : ρ ≤ ρA := le_trans hρle (min_le_left _ _)
  have hρ₂'' : ρ ≤ ρ₂ := le_trans hρle (min_le_right _ _)
  obtain ⟨K₁, hK₁⟩ := hA' ρ hρ hρA''
  obtain ⟨K₂, hK₂⟩ := hB' ρ hρ hρ₂''
  refine ⟨fun Λ => max (K₁ Λ) (K₂ Λ), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ
  have hK₁le : (K₁ Λ : ℝ≥0∞) ≤ ((max (K₁ Λ) (K₂ Λ) : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast le_max_left (K₁ Λ) (K₂ Λ)
  have hK₂le : (K₂ Λ : ℝ≥0∞) ≤ ((max (K₁ Λ) (K₂ Λ) : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast le_max_right (K₁ Λ) (K₂ Λ)
  have hw₁ : ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂)
      ≤ ENNReal.ofReal (lcWeight (min 1 c₂) l₁ l₂ k₁ k₂) :=
    ENNReal.ofReal_le_ofReal (lcWeight_le_of_le (min_le_left 1 c₂) l₁ l₂ k₁ k₂)
  have hw₂ : ENNReal.ofReal (lcWeight c₂ l₁ l₂ k₁ k₂)
      ≤ ENNReal.ofReal (lcWeight (min 1 c₂) l₁ l₂ k₁ k₂) :=
    ENNReal.ofReal_le_ofReal (lcWeight_le_of_le (min_le_right 1 c₂) l₁ l₂ k₁ k₂)
  by_cases hcase : MaeCaseA ρ C₀ a l₁ l₂ k₁ k₂
  · have h1 := hK₁ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ hcase
    refine le_trans h1 ?_
    exact mul_le_mul' (mul_le_mul' (mul_le_mul' hK₁le hw₁) le_rfl) le_rfl
  · have hdefect : (¬ NonAliasing (-(uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))
          (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ l₂))
        ∨ ∃ n : ℕ, inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
              (Nat.floor (a n))
            ∧ splitCut ρ (lcL l₁ l₂ k₁ k₂) < Nat.floor (a n)
            ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n))
            ∧ ¬ (max k₁ k₂ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
                ≤ (logN (Nat.floor (a n))).toNat) := by
      by_cases hNA : NonAliasing (-(uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))
          (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ l₂)
      · right
        have hP : ¬ (∀ n, CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n →
            max k₁ k₂ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
              ≤ (logN (Nat.floor (a n))).toNat) :=
          fun hP => hcase ⟨hNA, hP⟩
        obtain ⟨n, hn⟩ := not_forall.mp hP
        have hnc : CoreCondA6 ρ C₀ a l₁ l₂ k₁ k₂ n := by
          by_contra hc
          exact hn (fun h => absurd h hc)
        have hnp : ¬ (max k₁ k₂ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
            ≤ (logN (Nat.floor (a n))).toNat) := fun hp => hn (fun _ => hp)
        have hnc' : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
              (Nat.floor (a n))
            ∧ splitCut ρ (lcL l₁ l₂ k₁ k₂) < Nat.floor (a n)
            ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n)) := hnc
        obtain ⟨h1, h2, h3⟩ := hnc'
        exact ⟨n, h1, h2, h3, hnp⟩
      · exact Or.inl hNA
    have h2 := hK₂ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ hdefect
    refine le_trans h2 ?_
    exact mul_le_mul' (mul_le_mul' (mul_le_mul' hK₂le hw₂) le_rfl) le_rfl

/-- **The case-(A) core in the form used below** (the shim between the proved
`Work.KMTPlan.A6.ModApproxErrCoreNonAliasingU` and the local Prop `ModApproxErrCoreNAU`). -/
lemma modApproxErrCoreNAU_of (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) :
    ModApproxErrCoreNAU P C₀ :=
  ModApproxErrCoreNonAliasingU P hd C₀

/-- **The target.**  `LowModApprox P r C₀` follows from the dichotomy of
`NOTES_A6_LowModApproxU_ASSEMBLY.md`: either the non-aliasing case (A) holds, where the
single-scale `N⁻¹` bound `ModApproxErrCoreNonAliasingU` (PROVED, in `A6/UModApprox/`) plus the §5
bookkeeping give the estimate with the gain `1`; or its complement, where the aliasing defect can
only occur at bounded height (`lcL_le_of_plateauFail` for the plateau branch and
`lcL_le_of_not_nonAliasingU` for the `¬NonAliasing (-uScale ρ L)` branch) and the loss estimate
`LowModApproxNoAliasingCaseU` (PROVED, `A6/LowModApproxNoAliasingCaseU.lean`) gives the same shape
with a `ρ`-dependent gain.  `lowModApprox_of_dichotomy` above is the merge. -/
theorem LowModApproxExactEstimate (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) :
    Work.KMTPlan.A6.LowModApprox P r C₀ :=
  lowModApprox_of_dichotomy P r hr C₀ hC₀
    (modApproxErrCoreNAU_of P hd C₀)
    (Work.KMTPlan.A6.LowFix.LowModApproxNoAliasingCaseU P hd r hr C₀ hC₀ hA1)

end

end Work.KMTPlan.A6.LowFix
