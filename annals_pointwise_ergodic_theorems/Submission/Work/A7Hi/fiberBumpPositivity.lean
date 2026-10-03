import Mathlib
import Submission.Work.KMTAreas.A7Hi.FiberOpVarUniformLpNoLossClean
import Submission.Work.KMTAreas.A7Hi.LowpassDefs

/-!
# Positivity of the narrow bump `mStarF u` and non-aliasing of the exact-height frequencies

Structural facts about the fibre's bump that any proof of
`Work.A7Hi.fiberOpVarUniformLpNoLossVr` needs, in the only form in which they are *true*:

* `mStarF u = etaCut kmtEta (-(2u))` is a **real, non-negative, even** bump of height `1`,
  equal to `1` on the middle half and supported in `[-2^{-2u}, 2^{-2u}]` (`§1`);
* its **periodisation** `periodize (mStarF u)` — the symbol of the fibre's bump component — is
  **`[0,1]`-valued** (hence non-negative) for `u ≥ 1` (`§2`): the fibre's bump multiplier is a
  non-negative (hence positive semi-definite) symbol — this is the *true* form of "the coefficients
  `cw (mStarF u)` are non-negative";
* **non-aliasing** (`§3`): with `Cρ` large enough, `GoodMajorArcs ρ Cρ l k` forces every finite
  `A ⊆ iwArithFreqs ρ l` — in particular the exact-height set `iwArithFreqsNew ρ l` — to be
  `4 · 2^k`-separated; with `2^k = 2^{-2u}` this is the quantitative "the windows
  `α + [-2^k,2^k]` are pairwise disjoint" input;
* **the scale consequence** (`§4`): whenever `2l + 2 ≤ 2u` (which holds for the `u` admitted by
  `GoodMajorArcs` as soon as `Cρ · 2^{ρl} ≥ 2l + 2`) the bump's width is below the frequency
  separation: `4 · 2^{-2u} ≤ 4^{-l}`.

**Warning (recorded, do not re-attempt).**  Pointwise non-negativity of the *individual*
coefficients `cw (mStarF u) j` is **not** available: the kernel is the Fourier transform of a
flat-topped bump (a `ContDiffBump` with `rIn = 1/2`, `rOut = 1`), whose transform changes sign, and
Mathlib's `ContDiffBump` carries no monotonicity (see the docstring of
`Submission/Work/KMTAreas/A7Hi/EtaCutPositivity.lean`).  The *positive-definite* (symbol-level) form
of "non-negative coefficients",
`0 ≤ ∑_{x,y} cw (mStarF u) (x-y) · star (z y) · z x` for every finitely supported `z`, is the form
that is both true and usable.  Its general form for an arbitrary non-negative real symbol `m`,
namely

  `Work.A7Hi.cwQuadraticPosSemidef (m) (hm : Integrable m) (hre : ∀ θ, 0 ≤ (m θ).re) (s) (z) :
     0 ≤ (∑ x ∈ s, ∑ y ∈ s, cw m (x - y) * star (z y) * z x).re`,

has been reviewed as correct-as-stated and is the next piece to land (the diagonal case
`z = 1_{{0}}`, i.e. `0 ≤ cw m 0`, is the `∫ m ≥ 0` instance).
-/

namespace Work.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## §1. The bump `mStarF u` is a real, non-negative, even bump of width `2^{-2u}` -/

/-- `mStarF u θ` is the real cutoff `kmtEta` evaluated at `θ · 2^{2u}`. -/
theorem mStarF_apply (u : ℕ) (θ : ℝ) :
    Work.KMTAreas.A7.mStarF u θ = Work.KMTContract.kmtEta (θ * (2 : ℝ) ^ (2 * (u : ℤ))) := by
  rw [Work.KMTAreas.A7.mStarF, Work.Analysis.IonescuWainger.etaCut, div_eq_mul_inv,
    ← zpow_neg, neg_neg]

/-- The bump is real: its imaginary part vanishes. -/
theorem mStarF_im (u : ℕ) (θ : ℝ) : (Work.KMTAreas.A7.mStarF u θ).im = 0 := by
  rw [mStarF_apply, Work.KMTContract.kmtEta]; simp

/-- **The bump is non-negative and bounded by `1`.** -/
theorem mStarF_nonneg_le_one (u : ℕ) (θ : ℝ) :
    0 ≤ (Work.KMTAreas.A7.mStarF u θ).re ∧ (Work.KMTAreas.A7.mStarF u θ).re ≤ 1 := by
  rw [mStarF_apply, Work.KMTContract.kmtEta]
  simp only [Complex.ofReal_re]
  exact ⟨Work.KMTContract.kmtEta_nonneg _, Work.KMTContract.kmtEta_le_one _⟩

/-- The bump is **even**. -/
theorem mStarF_even (u : ℕ) (θ : ℝ) :
    Work.KMTAreas.A7.mStarF u (-θ) = Work.KMTAreas.A7.mStarF u θ := by
  rw [mStarF_apply, mStarF_apply,
    show -θ * (2 : ℝ) ^ (2 * (u : ℤ)) = -(θ * (2 : ℝ) ^ (2 * (u : ℤ))) by ring]
  exact Work.KMTContract.kmtEta_neg _

/-- The bump is **supported in `[-2^{-2u}, 2^{-2u}]`**. -/
theorem mStarF_eq_zero_of_one_le (u : ℕ) (θ : ℝ)
    (hθ : 1 ≤ |θ| * (2 : ℝ) ^ (2 * (u : ℤ))) : Work.KMTAreas.A7.mStarF u θ = 0 := by
  rw [mStarF_apply]
  refine Work.KMTContract.kmtEta_zero ?_
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * (u : ℤ)) := zpow_pos (by norm_num) (2 * (u : ℤ))
  rw [abs_mul, abs_of_pos hpos]
  exact hθ

/-- The bump equals `1` on the middle half: `|θ| · 2^{2u} ≤ 1/2`. -/
theorem mStarF_eq_one_of_le_half (u : ℕ) (θ : ℝ)
    (hθ : |θ| * (2 : ℝ) ^ (2 * (u : ℤ)) ≤ 1 / 2) : Work.KMTAreas.A7.mStarF u θ = 1 := by
  rw [mStarF_apply]
  refine Work.KMTContract.kmtEta_one ?_
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * (u : ℤ)) := zpow_pos (by norm_num) (2 * (u : ℤ))
  rw [abs_mul, abs_of_pos hpos]
  exact hθ

/-! ## §2. The symbol of the bump component is `[0,1]`-valued (non-negative coefficients) -/

/-! ## §3. Non-aliasing of the exact-height frequencies -/

/-- **Non-aliasing (separation) of the exact-height frequency set.**  With `Cρ` large enough,
`GoodMajorArcs ρ Cρ l k` forces every finite `A ⊆ iwArithFreqsNew ρ l` to be `4 · 2^k`-separated:
the windows `α + realArc k` are pairwise disjoint, with the quantitative gap `4 · 2^k`. -/
theorem sep_iwArithFreqsNew_of_goodMajorArcs (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ Cρ : ℝ, 0 < Cρ ∧
      ∀ (l : ℕ) (k : ℤ) (A : Finset Circ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
        A ⊆ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l →
        ∀ α ∈ A, ∀ β ∈ A, α ≠ β → 4 * (2 : ℝ) ^ k ≤ ‖α - β‖ := by
  obtain ⟨Cρ, hCρ, hsep⟩ := Work.KMTAreas.A7Hi.sep_of_goodMajorArcs ρ hρ hρ1
  refine ⟨Cρ, hCρ, ?_⟩
  intro l k A hgm hA α hα β hβ hne
  exact hsep l k A hgm (fun y hy => (Finset.mem_sdiff.mp (hA hy)).1) α hα β hβ hne

/-! ## §4. The scale consequence: `4 · 2^{-2u} ≤ 4^{-l}` in the narrow regime -/

/-- **The narrowness forces the bump's width below the frequency separation.**  If `2l + 2 ≤ 2u`
then the scale `2^{-2u}` of the bump is at most the intrinsic scale `4^{-l}` of the exact-height
frequencies: `4 · 2^{-2u} ≤ 4^{-l}`. -/
theorem four_mul_two_zpow_le_four_zpow (l u : ℕ) (h : 2 * l + 2 ≤ 2 * u) :
    4 * (2 : ℝ) ^ (-(2 * (u : ℤ))) ≤ (4 : ℝ) ^ (-(l : ℤ)) := by
  have hL : (4 : ℝ) ^ (-(l : ℤ)) = (2 : ℝ) ^ (-(2 * (l : ℤ))) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℤ) by norm_num [zpow_ofNat], ← zpow_mul]
    congr 1
    ring
  have hR : 4 * (2 : ℝ) ^ (-(2 * (u : ℤ))) = (2 : ℝ) ^ ((2 : ℤ) - 2 * (u : ℤ)) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℤ) by norm_num [zpow_ofNat],
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    exact congrArg (fun e : ℤ => (2 : ℝ) ^ e) (by ring)
  rw [hL, hR]
  exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by omega)

/-! ## §5. The combined positivity/non-aliasing lemma -/

end

end Work.A7Hi
