/-
# The non-Farey (bounded-scale) regime of the fibre variational estimate

`Work.KMTAreas.A7.fiberVarSamplingCoreTex` isolates a *non-Farey* regime: when
`L = max (max l₁ l₂) (max k₁ k₂) ≤ B ρ` for a fixed `B`, the packet band of the symbol can sit
above the Farey gap of the frequency set, but the scale `L` then ranges over a *bounded* set, and
the elementary Young inequality for the fibre kernel suffices.

This module proves that bound: for `r > 2`, `p ∈ (1,∞)` and any bound function `B : ℝ → ℕ` there is
`C > 0` such that for **all** `l₁ l₂ k₁ k₂` with `max (max l₁ l₂) (max k₁ k₂) ≤ B ρ`, all residues
`n₀` and all families `u : ℕ → ℤ → ℂ`,

  `‖ V^r( n ↦ fiberOp ρ l₁ (mStarF (uScale ρ L)) n₀ (u n) ) ‖_{ℓ^p(ℤ)} ≤ C ‖ V^r( n ↦ u n ) ‖_{ℓ^p(ℤ)}`.

The proof is the composition of two unconditional, completely elementary facts:

* the pointwise Young bound `fiberOpVarYoungExact` for the fibre, whose kernel is
  `j ↦ (∑_{α ∈ (ℚ/ℤ)_l} e(α(n₀-j))) · (𝓕⁻m j)`;
* the `ℓ¹` mass of that kernel is at most `#(ℚ/ℤ)_l · ∑_j ‖𝓕⁻m j‖` (triangle inequality for the
  character sum, plus absolute summability of the coefficients of the narrow bump `mStarF u`);

and these give, via Young's convolution inequality for `ℝ≥0∞`-valued functions on the counting
measure of `ℤ`, the per-tuple estimate

  `‖ V^r(fiberOp n₀ u) ‖_p ≤ ofReal (#(ℚ/ℤ)_{l₁} · ∑_j ‖cw m j‖) · ‖ V^r(u) ‖_p`

(unconditional in `n₀`, `u`, `l₁` and the scale `L`).  The constant is then made *uniform* over the
finite box `{l₁, L ≤ B ρ}` by summing the finitely many per-tuple constants.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.fiberOpVarYoungExact
import Submission.Work.KMTAreas.A7.cw_etaCut_decay
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform
import Submission.Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## Summability of the coefficients of the narrow bump -/

/-- The Fourier coefficients of the narrow bump `mStarF u = η_{≤-2u}` are absolutely summable.
(The workspace's `Work.KMTAreas.A7.summable_cw_mStarF` lives in a module whose import closure is
currently broken, so the three-line proof is reproduced here.) -/
private theorem summable_cw_mStarF_aux (u : ℕ) : Summable (fun j : ℤ => ‖cw (mStarF u) j‖) := by
  obtain ⟨C, _hCpos, hC⟩ := cw_etaCut_decay (-(2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (summable_kmtKernWeight.mul_left C)
  rw [norm_kmtKernWeight, mul_one_div]
  simpa only [mStarF] using hC j

/-! ## The character sum of the exact-height arithmetic frequencies -/

/-- A single Fourier character is unimodular on the circle. -/
private theorem norm_fourier_int (y : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    ‖fourier (T := 1) y α‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- **The triangle inequality for the exact-height arithmetic character**: for every `y : ℤ`,
`‖∑_{α ∈ (ℚ/ℤ)_l} e(αy)‖ ≤ #(ℚ/ℤ)_l`. -/
private theorem norm_arithCharNew_le (ρ : ℝ) (l : ℕ) (y : ℤ) :
    ‖∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) y α‖ ≤ ((iwArithFreqsNew ρ l).card : ℝ) := by
  have hsum : (∑ α ∈ iwArithFreqsNew ρ l, ‖fourier (T := 1) y α‖)
      = ((iwArithFreqsNew ρ l).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun α _ => norm_fourier_int y α)]
    simp
  exact (norm_sum_le _ _).trans (le_of_eq hsum)

/-! ## The `ℓ¹` mass of the fibre kernel -/

/-- **The `ℓ¹` mass of the kernel of the fibre `fiberOp ρ l (mStarF u) n₀`** is at most
`#(ℚ/ℤ)_l` times the `ℓ¹` mass of the coefficients of `mStarF u`; in particular it is finite and
independent of the residue `n₀`. -/
private theorem tsum_enorm_fiberKernel_le_aux (ρ : ℝ) (l u : ℕ) (n₀ : ℤ) :
    (∑' j : ℤ, ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)
        * cw (mStarF u) j‖ₑ)
      ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞) * (∑' j : ℤ, ‖cw (mStarF u) j‖ₑ) := by
  have hterm : ∀ j : ℤ,
      ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α) * cw (mStarF u) j‖ₑ
        ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞) * ‖cw (mStarF u) j‖ₑ := by
    intro j
    have h1 : ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)‖ₑ
        ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (norm_arithCharNew_le ρ l (n₀ - j))
    rw [enorm_mul]
    exact mul_le_mul_left h1 _
  calc (∑' j : ℤ, ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)
          * cw (mStarF u) j‖ₑ)
      ≤ ∑' j : ℤ, ((iwArithFreqsNew ρ l).card : ℝ≥0∞) * ‖cw (mStarF u) j‖ₑ :=
        ENNReal.tsum_le_tsum hterm
    _ = ((iwArithFreqsNew ρ l).card : ℝ≥0∞) * (∑' j : ℤ, ‖cw (mStarF u) j‖ₑ) :=
        ENNReal.tsum_mul_left

/-! ## Young's inequality for the counting measure of `ℤ` -/

/-- **Young's/convolution inequality for the counting measure of `ℤ`, in the `ℝ≥0∞` form**: for
`q ≥ 1` and arbitrary `K : ℤ → ℂ`, `W : ℤ → ℝ≥0∞`,

  `‖ x ↦ ∑'_j ‖K j‖ · W (x - j) ‖_{ℓ^q} ≤ (∑'_j ‖K j‖) · ‖W‖_{ℓ^q}`.

Obtained from Minkowski's inequality for countable `ℝ≥0∞`-valued sums, the homogeneity of
`eLpNorm` under multiplication by a constant and the translation invariance of `eLpNorm` for the
counting measure. -/
private theorem eLpNorm_tsum_enorm_mul_sub_le_aux {q : ℝ} (hq : 1 ≤ q) (K : ℤ → ℂ)
    (W : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => ∑' j : ℤ, ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
      ≤ (∑' j : ℤ, ‖K j‖ₑ) * eLpNorm W (ENNReal.ofReal q) Measure.count := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hmink := eLpNorm_tsum_le_tsum_eLpNorm (μ := Measure.count) (p := ENNReal.ofReal q)
    (ENNReal.one_le_ofReal.mpr hq) (f := fun j : ℤ => fun x : ℤ => ‖K j‖ₑ * W (x - j))
    (fun j => (measurable_of_countable (fun x : ℤ => ‖K j‖ₑ * W (x - j))).aemeasurable)
  have hconst : ∀ j : ℤ,
      eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
        = ‖K j‖ₑ * eLpNorm W (ENNReal.ofReal q) Measure.count := by
    intro j
    rw [show eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
        = eLpNorm (fun x : ℤ => ‖K j‖ₑ * W x) (ENNReal.ofReal q) Measure.count from
        Commons.Analysis.Convolution.eLpNorm_sub_right_ennreal (fun y : ℤ => ‖K j‖ₑ * W y) j hq0]
    exact Commons.Analysis.Convolution.eLpNorm_const_mul_ennreal_of_pos
      (f := W) (measurable_of_countable W).aemeasurable (‖K j‖ₑ) hq0
  refine hmink.trans_eq ?_
  rw [tsum_congr hconst, ENNReal.tsum_mul_right]

/-! ## The per-tuple estimate -/

/-- **The per-tuple fibre variational estimate.**  For `r ≥ 1` and `q ≥ 1`, the `ℓ^q` norm of the
variational norm of the family `n ↦ fiberOp ρ l (mStarF u) n₀ (U n)` is bounded by the explicit
constant `#(ℚ/ℤ)_l · ∑_j ‖cw (mStarF u) j‖` times the `ℓ^q` norm of the variational norm of `U`.
No hypothesis on `n₀`, on `l`, or on the scale `u` is needed. -/
private theorem eLpNorm_varNorm_fiberOp_le_aux (r : NNReal) (hr : 1 ≤ r) (ρ : ℝ) (l : ℕ)
    (u : ℕ) (n₀ : ℤ) (U : ℕ → ℤ → ℂ) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => fiberOp ρ l (mStarF u) n₀ (U n) x)) (ENNReal.ofReal q) Measure.count
      ≤ ENNReal.ofReal (((iwArithFreqsNew ρ l).card : ℝ)
            * (∑' j : ℤ, ‖cw (mStarF u) j‖))
          * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => U n x))
              (ENNReal.ofReal q) Measure.count := by
  set W : ℤ → ℝ≥0∞ := fun x => variationalNorm r (fun n : ℕ => U n x) with hW
  set K : ℤ → ℂ := fun j => (∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)
    * cw (mStarF u) j with hK
  have hpt : ∀ x : ℤ, variationalNorm r (fun n : ℕ => fiberOp ρ l (mStarF u) n₀ (U n) x)
      ≤ ∑' j : ℤ, ‖K j‖ₑ * W (x - j) := by
    intro x
    simpa only [hK, hW] using fiberOpVarYoungExact ρ l (mStarF u) n₀ U r hr x
  have hmass : (∑' j : ℤ, ‖K j‖ₑ)
      ≤ ENNReal.ofReal (((iwArithFreqsNew ρ l).card : ℝ)
          * (∑' j : ℤ, ‖cw (mStarF u) j‖)) := by
    have h := tsum_enorm_fiberKernel_le_aux ρ l u n₀
    have hT : (∑' j : ℤ, ‖cw (mStarF u) j‖ₑ)
        = ENNReal.ofReal (∑' j : ℤ, ‖cw (mStarF u) j‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) (summable_cw_mStarF_aux u)]
      exact tsum_congr fun j => (ofReal_norm _).symm
    have hofReal : ENNReal.ofReal (((iwArithFreqsNew ρ l).card : ℝ)
          * (∑' j : ℤ, ‖cw (mStarF u) j‖))
        = ((iwArithFreqsNew ρ l).card : ℝ≥0∞) * (∑' j : ℤ, ‖cw (mStarF u) j‖ₑ) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← hT]
    rw [hK]
    exact h.trans (le_of_eq hofReal.symm)
  calc eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => fiberOp ρ l (mStarF u) n₀ (U n) x)) (ENNReal.ofReal q) Measure.count
      ≤ eLpNorm (fun x : ℤ => ∑' j : ℤ, ‖K j‖ₑ * W (x - j))
          (ENNReal.ofReal q) Measure.count :=
        eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by simpa only [enorm_eq_self] using hpt x
    _ ≤ (∑' j : ℤ, ‖K j‖ₑ) * eLpNorm W (ENNReal.ofReal q) Measure.count :=
        eLpNorm_tsum_enorm_mul_sub_le_aux hq K W
    _ ≤ ENNReal.ofReal (((iwArithFreqsNew ρ l).card : ℝ)
            * (∑' j : ℤ, ‖cw (mStarF u) j‖))
          * eLpNorm W (ENNReal.ofReal q) Measure.count := mul_le_mul_left hmass _
    _ = ENNReal.ofReal (((iwArithFreqsNew ρ l).card : ℝ)
            * (∑' j : ℤ, ‖cw (mStarF u) j‖))
          * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => U n x))
              (ENNReal.ofReal q) Measure.count := by rw [hW]

/-! ## The uniform constant over the box `l, L ≤ B ρ` -/

/-- The finite bookkeeping constant of the non-Farey regime: the sum of the per-tuple kernel masses
over all pairs of scales `l ≤ B ρ`, `L ≤ B ρ`. -/
noncomputable def boxKernelConst (ρ : ℝ) (B : ℝ → ℕ) : ℝ :=
  ∑ L ∈ Finset.range (B ρ + 1), ∑ l ∈ Finset.range (B ρ + 1),
    ((iwArithFreqsNew ρ l).card : ℝ) * (∑' j : ℤ, ‖cw (mStarF (uScale ρ L)) j‖)

private theorem kernelConst_nonneg (ρ : ℝ) (l L : ℕ) :
    0 ≤ ((iwArithFreqsNew ρ l).card : ℝ) * (∑' j : ℤ, ‖cw (mStarF (uScale ρ L)) j‖) :=
  mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg fun j => norm_nonneg _)

private theorem boxKernelConst_nonneg (ρ : ℝ) (B : ℝ → ℕ) : 0 ≤ boxKernelConst ρ B :=
  Finset.sum_nonneg fun L _ => Finset.sum_nonneg fun l _ => kernelConst_nonneg ρ l L

private theorem kernelConst_le_boxKernelConst (ρ : ℝ) (B : ℝ → ℕ) {l L : ℕ}
    (hL : L ≤ B ρ) (hl : l ≤ B ρ) :
    ((iwArithFreqsNew ρ l).card : ℝ) * (∑' j : ℤ, ‖cw (mStarF (uScale ρ L)) j‖)
      ≤ boxKernelConst ρ B := by
  have hLm : L ∈ Finset.range (B ρ + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hL)
  have hlm : l ∈ Finset.range (B ρ + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hl)
  have hinner : ∀ i ∈ Finset.range (B ρ + 1),
      0 ≤ ∑ l' ∈ Finset.range (B ρ + 1),
        ((iwArithFreqsNew ρ l').card : ℝ) * (∑' j : ℤ, ‖cw (mStarF (uScale ρ i)) j‖) :=
    fun i _ => Finset.sum_nonneg fun l' _ => kernelConst_nonneg ρ l' i
  refine (Finset.single_le_sum (fun l' _ => kernelConst_nonneg ρ l' L) hlm).trans ?_
  exact Finset.single_le_sum hinner hLm

/-! ## The theorem -/

theorem fiberOpVarNonFareyBounded (r : NNReal) (hr : 2 < r) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (B : ℝ → ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ l₂ k₁ k₂ : ℕ), max (max l₁ l₂) (max k₁ k₂) ≤ B ρ →
        ∀ (n₀ : ℤ) (u : ℕ → ℤ → ℂ),
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
                  (max (max l₁ l₂) (max k₁ k₂)))) n₀ (u n) x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => u n x)) p MeasureTheory.Measure.count := by
  refine ⟨boxKernelConst ρ B + 1, by linarith [boxKernelConst_nonneg ρ B], ?_⟩
  intro l₁ l₂ k₁ k₂ hL n₀ u
  set L : ℕ := max (max l₁ l₂) (max k₁ k₂) with hLdef
  have hLLe : L ≤ B ρ := by rw [hLdef]; exact hL
  have hl₁ : l₁ ≤ B ρ := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hL
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hptop' : p ≠ ⊤ := ne_of_lt hptop
  have hq : (1 : ℝ) ≤ p.toReal := by
    have h1 : ((1 : ENNReal).toReal) ≤ p.toReal := ENNReal.toReal_mono hptop' (le_of_lt hp)
    simpa using h1
  have hper := eLpNorm_varNorm_fiberOp_le_aux r hr1 ρ l₁ (uScale ρ L) n₀ u hq
  have hconst : ((iwArithFreqsNew ρ l₁).card : ℝ)
        * (∑' j : ℤ, ‖cw (mStarF (uScale ρ L)) j‖) ≤ boxKernelConst ρ B + 1 :=
    (kernelConst_le_boxKernelConst ρ B hLLe hl₁).trans (le_add_of_nonneg_right zero_le_one)
  calc MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => fiberOp ρ l₁ (mStarF (uScale ρ L)) n₀ (u n) x))
        p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => fiberOp ρ l₁ (mStarF (uScale ρ L)) n₀ (u n) x))
          (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := by
          rw [ENNReal.ofReal_toReal hptop']
    _ ≤ ENNReal.ofReal (((iwArithFreqsNew ρ l₁).card : ℝ)
            * (∑' j : ℤ, ‖cw (mStarF (uScale ρ L)) j‖))
          * MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
              (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := hper
    _ ≤ ENNReal.ofReal (boxKernelConst ρ B + 1)
          * MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
              (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hconst) _
    _ = ENNReal.ofReal (boxKernelConst ρ B + 1)
          * MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
              p MeasureTheory.Measure.count := by
          rw [ENNReal.ofReal_toReal hptop']

end Work.KMTAreas.A7
