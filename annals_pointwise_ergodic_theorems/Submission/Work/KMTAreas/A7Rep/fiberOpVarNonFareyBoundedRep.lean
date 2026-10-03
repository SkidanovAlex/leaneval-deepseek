/-
# The non-Farey (bounded-scale) regime of the fibre variational estimate, at the *repaired*
window `uRep`

`Work.KMTAreas.A7.fiberOpVarNonFareyBounded` proves the non-Farey regime of the §8 fibre estimate
for the KMT band `uScale ρ L`, `L = max (max l₁ l₂) (max k₁ k₂)`:

  `‖ V^r( n ↦ fiberOp ρ l₁ (mStarF (uScale ρ L)) n₀ (u n) ) ‖_{ℓ^p(ℤ)} ≤ C ‖ V^r( n ↦ u n ) ‖_{ℓ^p(ℤ)}`

for all `l₁ l₂ k₁ k₂` with `L ≤ B ρ`.  The present module transfers that estimate to the *repaired*
band `uRep ρ l₁ l₂ k₁ k₂ = max (uScale ρ L) (max l₁ l₂ + 3)` of `Work.KMTAreas.A7.modelTupleRep`
(whose plateau is narrow enough that the composed model operator has no cross-fibre terms); the
`uRep`-version is what the `Rep`-chain of Area A7 consumes.

The proof repeats the two unconditional, completely elementary facts of the `uScale` case:

* the pointwise Young bound `fiberOpVarYoungExact` for the fibre, whose kernel is
  `j ↦ (∑_{α ∈ (ℚ/ℤ)_l} e(α(n₀-j))) · (𝓕⁻m j)`;
* the `ℓ¹` mass of that kernel is at most `#(ℚ/ℤ)_l · ∑_j ‖𝓕⁻m j‖`,

giving the per-tuple estimate

  `‖ V^r(fiberOp n₀ u) ‖_p ≤ ofReal (#(ℚ/ℤ)_{l₁} · ∑_j ‖cw m j‖) · ‖ V^r(u) ‖_p`

for **every** band `m = mStarF u` and every `l₁, n₀, u`.  It is then enough to make the constant
uniform over the finite box: `l₁ ≤ B ρ` and `uRep ρ l₁ l₂ k₁ k₂ ≤ max (uScale ρ (B ρ)) (B ρ + 3)`
(the first by monotonicity of `L ↦ uScale ρ L`, the second from `max l₁ l₂ ≤ L ≤ B ρ`).  Summing
the per-tuple kernel masses over that box gives the constant of the statement.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.fiberOpVarNonFareyBounded
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Rep

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## Summability of the coefficients of the narrow bump -/

/-- The Fourier coefficients of the narrow bump `mStarF u = η_{≤-2u}` are absolutely summable.
(This is the `uRep`-independent part of the argument; the same three lines are `private` in
`Work.KMTAreas.A7.fiberOpVarNonFareyBounded`, so they are reproduced here.) -/
private theorem rep_summable_cw_mStarF (u : ℕ) :
    Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖) := by
  obtain ⟨C, _hCpos, hC⟩ := Work.KMTAreas.A7.cw_etaCut_decay (-(2 * (u : ℤ)))
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (Work.KMTAreas.A7.summable_kmtKernWeight.mul_left C)
  rw [Work.KMTAreas.A7.norm_kmtKernWeight, mul_one_div]
  simpa only [Work.KMTAreas.A7.mStarF] using hC j

/-! ## The character sum of the exact-height arithmetic frequencies -/

/-- A single Fourier character is unimodular on the circle. -/
private theorem rep_norm_fourier_int (y : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    ‖fourier (T := 1) y α‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

/-- **The triangle inequality for the exact-height arithmetic character**: for every `y : ℤ`,
`‖∑_{α ∈ (ℚ/ℤ)_l} e(αy)‖ ≤ #(ℚ/ℤ)_l`. -/
private theorem rep_norm_arithCharNew_le (ρ : ℝ) (l : ℕ) (y : ℤ) :
    ‖∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) y α‖
      ≤ ((iwArithFreqsNew ρ l).card : ℝ) := by
  have hsum : (∑ α ∈ iwArithFreqsNew ρ l, ‖fourier (T := 1) y α‖)
      = ((iwArithFreqsNew ρ l).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun α _ => rep_norm_fourier_int y α)]
    simp
  exact (norm_sum_le _ _).trans (le_of_eq hsum)

/-! ## The `ℓ¹` mass of the fibre kernel -/

/-- **The `ℓ¹` mass of the kernel of the fibre `fiberOp ρ l (mStarF u) n₀`** is at most
`#(ℚ/ℤ)_l` times the `ℓ¹` mass of the coefficients of `mStarF u`; in particular it is finite and
independent of the residue `n₀`. -/
private theorem rep_tsum_enorm_fiberKernel_le (ρ : ℝ) (l u : ℕ) (n₀ : ℤ) :
    (∑' j : ℤ, ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)
        * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖ₑ)
      ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞)
        * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖ₑ) := by
  have hterm : ∀ j : ℤ,
      ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)
        * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖ₑ
        ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞)
          * ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖ₑ := by
    intro j
    have h1 : ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)‖ₑ
        ≤ ((iwArithFreqsNew ρ l).card : ℝ≥0∞) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (rep_norm_arithCharNew_le ρ l (n₀ - j))
    rw [enorm_mul]
    exact mul_le_mul_left h1 _
  calc (∑' j : ℤ, ‖(∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)
          * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖ₑ)
      ≤ ∑' j : ℤ, ((iwArithFreqsNew ρ l).card : ℝ≥0∞)
          * ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖ₑ :=
        ENNReal.tsum_le_tsum hterm
    _ = ((iwArithFreqsNew ρ l).card : ℝ≥0∞)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖ₑ) :=
        ENNReal.tsum_mul_left

/-! ## Young's inequality for the counting measure of `ℤ` -/

/-- **Young's/convolution inequality for the counting measure of `ℤ`, in the `ℝ≥0∞` form**: for
`q ≥ 1` and arbitrary `K : ℤ → ℂ`, `W : ℤ → ℝ≥0∞`,

  `‖ x ↦ ∑'_j ‖K j‖ · W (x - j) ‖_{ℓ^q} ≤ (∑'_j ‖K j‖) · ‖W‖_{ℓ^q}`.

Obtained from Minkowski's inequality for countable `ℝ≥0∞`-valued sums, the homogeneity of
`eLpNorm` under multiplication by a constant and the translation invariance of `eLpNorm` for the
counting measure. -/
private theorem rep_eLpNorm_tsum_enorm_mul_sub_le {q : ℝ} (hq : 1 ≤ q) (K : ℤ → ℂ)
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

/-- **The per-tuple fibre variational estimate, at an arbitrary band `u`.**  For `r ≥ 1` and
`q ≥ 1`, the `ℓ^q` norm of the variational norm of the family
`n ↦ fiberOp ρ l (mStarF u) n₀ (U n)` is bounded by the explicit constant
`#(ℚ/ℤ)_l · ∑_j ‖cw (mStarF u) j‖` times the `ℓ^q` norm of the variational norm of `U`.
No hypothesis on `n₀`, on `l`, or on the band `u` is needed. -/
private theorem rep_eLpNorm_varNorm_fiberOp_le (r : NNReal) (hr : 1 ≤ r) (ρ : ℝ) (l : ℕ)
    (u : ℕ) (n₀ : ℤ) (U : ℕ → ℤ → ℂ) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStarF u) n₀ (U n) x))
        (ENNReal.ofReal q) Measure.count
      ≤ ENNReal.ofReal (((iwArithFreqsNew ρ l).card : ℝ)
            * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖))
          * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => U n x))
              (ENNReal.ofReal q) Measure.count := by
  set W : ℤ → ℝ≥0∞ := fun x => variationalNorm r (fun n : ℕ => U n x) with hW
  set K : ℤ → ℂ := fun j => (∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)
    * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j with hK
  have hpt : ∀ x : ℤ, variationalNorm r
      (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStarF u) n₀ (U n) x)
      ≤ ∑' j : ℤ, ‖K j‖ₑ * W (x - j) := by
    intro x
    simpa only [hK, hW] using
      Work.KMTAreas.A7.fiberOpVarYoungExact ρ l (Work.KMTAreas.A7.mStarF u) n₀ U r hr x
  have hmass : (∑' j : ℤ, ‖K j‖ₑ)
      ≤ ENNReal.ofReal (((iwArithFreqsNew ρ l).card : ℝ)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖)) := by
    have h := rep_tsum_enorm_fiberKernel_le ρ l u n₀
    have hsummable := rep_summable_cw_mStarF u
    have hT : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖ₑ)
        = ENNReal.ofReal (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hsummable]
      exact tsum_congr fun j => (ofReal_norm _).symm
    have hofReal : ENNReal.ofReal (((iwArithFreqsNew ρ l).card : ℝ)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖))
        = ((iwArithFreqsNew ρ l).card : ℝ≥0∞)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖ₑ) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← hT]
    rw [hK]
    exact h.trans (le_of_eq hofReal.symm)
  calc eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStarF u) n₀ (U n) x))
          (ENNReal.ofReal q) Measure.count
      ≤ eLpNorm (fun x : ℤ => ∑' j : ℤ, ‖K j‖ₑ * W (x - j))
          (ENNReal.ofReal q) Measure.count :=
        eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by simpa only [enorm_eq_self] using hpt x
    _ ≤ (∑' j : ℤ, ‖K j‖ₑ) * eLpNorm W (ENNReal.ofReal q) Measure.count :=
        rep_eLpNorm_tsum_enorm_mul_sub_le hq K W
    _ ≤ ENNReal.ofReal (((iwArithFreqsNew ρ l).card : ℝ)
            * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖))
          * eLpNorm W (ENNReal.ofReal q) Measure.count := mul_le_mul_left hmass _
    _ = ENNReal.ofReal (((iwArithFreqsNew ρ l).card : ℝ)
            * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖))
          * eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => U n x))
              (ENNReal.ofReal q) Measure.count := by rw [hW]

/-! ## The uniform constant over the box `l ≤ B ρ`, `uRep ρ l₁ l₂ k₁ k₂ ≤ max (uScale ρ (B ρ)) (B ρ+3)` -/

/-- Monotonicity of the auxiliary scale `uScale ρ L = ⌊2^{2ρL}⌋` in `L` (reproduced so that this
module does not have to import the heavy `goodRegime` module). -/
private theorem rep_uScale_mono {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Monotone fun L : ℕ => Work.KMTAreas.A7.uScale ρ L := by
  intro L B hLB
  have hfloor : ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋
      ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (B : ℝ))⌋ := by
    refine Int.floor_mono ?_
    simp only [Nat.cast_one, one_mul]
    rw [Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
    have hLB' : (L : ℝ) ≤ (B : ℝ) := by exact_mod_cast hLB
    nlinarith
  have hL0 : (0 : ℤ) ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ :=
    Int.floor_nonneg.mpr (by positivity)
  have hB0 : (0 : ℤ) ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (B : ℝ))⌋ :=
    Int.floor_nonneg.mpr (by positivity)
  unfold Work.KMTAreas.A7.uScale Work.Analysis.EndVar.scaleCount
  have hcast : ((⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat : ℤ))
      ≤ ((⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (B : ℝ))⌋.toNat : ℤ)) := by
    rw [Int.toNat_of_nonneg hL0, Int.toNat_of_nonneg hB0]
    exact hfloor
  exact_mod_cast hcast

/-- The uniform bound on the repaired band `uRep ρ l₁ l₂ k₁ k₂` over the box
`max (max l₁ l₂) (max k₁ k₂) ≤ B ρ`. -/
noncomputable def uRepBound (ρ : ℝ) (B : ℝ → ℕ) : ℕ :=
  max (Work.KMTAreas.A7.uScale ρ (B ρ)) (B ρ + 3)

/-- **The repaired band stays in the box.**  If `max (max l₁ l₂) (max k₁ k₂) ≤ B ρ` and `ρ ≥ 0`,
then `uRep ρ l₁ l₂ k₁ k₂ ≤ uRepBound ρ B`. -/
private theorem rep_uRep_le_uRepBound (ρ : ℝ) (hρ : 0 ≤ ρ) (B : ℝ → ℕ) (l₁ l₂ k₁ k₂ : ℕ)
    (hL : max (max l₁ l₂) (max k₁ k₂) ≤ B ρ) :
    Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ ≤ uRepBound ρ B := by
  refine max_le ?_ ?_
  · exact le_trans (rep_uScale_mono hρ hL) (le_max_left _ _)
  · have h2 : max l₁ l₂ ≤ B ρ := le_trans (le_max_left _ _) hL
    exact le_trans (Nat.add_le_add_right h2 3) (le_max_right _ _)

/-- The finite bookkeeping constant of the non-Farey regime at the repaired band: the sum of the
per-tuple kernel masses over all bands `U ≤ uRepBound ρ B` and all scale pairs `l ≤ B ρ`. -/
noncomputable def boxKernelConstRep (ρ : ℝ) (B : ℝ → ℕ) : ℝ :=
  ∑ U ∈ Finset.range (uRepBound ρ B + 1),
    ∑ l ∈ Finset.range (B ρ + 1),
      ((iwArithFreqsNew ρ l).card : ℝ)
        * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖)

private theorem rep_kernelConst_nonneg (ρ : ℝ) (l U : ℕ) :
    0 ≤ ((iwArithFreqsNew ρ l).card : ℝ)
        * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖) :=
  mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg fun j => norm_nonneg _)

private theorem rep_boxKernelConst_nonneg (ρ : ℝ) (B : ℝ → ℕ) :
    0 ≤ boxKernelConstRep ρ B :=
  Finset.sum_nonneg fun U _ => Finset.sum_nonneg fun l _ => rep_kernelConst_nonneg ρ l U

private theorem rep_kernelConst_le_boxKernelConst (ρ : ℝ) (B : ℝ → ℕ) {l U : ℕ}
    (hU : U ≤ uRepBound ρ B) (hl : l ≤ B ρ) :
    ((iwArithFreqsNew ρ l).card : ℝ)
        * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖)
      ≤ boxKernelConstRep ρ B := by
  have hUm : U ∈ Finset.range (uRepBound ρ B + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hU)
  have hlm : l ∈ Finset.range (B ρ + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hl)
  have hinner : ∀ i ∈ Finset.range (uRepBound ρ B + 1),
      0 ≤ ∑ l' ∈ Finset.range (B ρ + 1),
        ((iwArithFreqsNew ρ l').card : ℝ)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF i) j‖) :=
    fun i _ => Finset.sum_nonneg fun l' _ => rep_kernelConst_nonneg ρ l' i
  refine (Finset.single_le_sum (fun l' _ => rep_kernelConst_nonneg ρ l' U) hlm).trans ?_
  exact Finset.single_le_sum hinner hUm

/-! ## The theorem -/

theorem fiberOpVarNonFareyBoundedRep (r : NNReal) (hr : 2 < r) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (B : ℝ → ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (l₁ l₂ k₁ k₂ : ℕ), max (max l₁ l₂) (max k₁ k₂) ≤ B ρ →
        ∀ (n₀ : ℤ) (u : ℕ → ℤ → ℂ),
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
                (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀ (u n) x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C *
              MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => u n x)) p MeasureTheory.Measure.count := by
  refine ⟨boxKernelConstRep ρ B + 1, by linarith [rep_boxKernelConst_nonneg ρ B], ?_⟩
  intro l₁ l₂ k₁ k₂ hL n₀ u
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hptop' : p ≠ ⊤ := ne_of_lt hptop
  have hq : (1 : ℝ) ≤ p.toReal := by
    have h1 : ((1 : ENNReal).toReal) ≤ p.toReal := ENNReal.toReal_mono hptop' (le_of_lt hp)
    simpa using h1
  have hl₁ : l₁ ≤ B ρ := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hL
  have huU : Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂ ≤ uRepBound ρ B :=
    rep_uRep_le_uRepBound ρ (le_of_lt hρ) B l₁ l₂ k₁ k₂ hL
  have hper := rep_eLpNorm_varNorm_fiberOp_le r hr1 ρ l₁
    (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂) n₀ u hq
  have hconst : ((iwArithFreqsNew ρ l₁).card : ℝ)
        * (∑' j : ℤ,
            ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) j‖)
        ≤ boxKernelConstRep ρ B + 1 :=
    (rep_kernelConst_le_boxKernelConst ρ B huU hl₁).trans (le_add_of_nonneg_right zero_le_one)
  calc MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
          (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀ (u n) x))
        p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.fiberOp ρ l₁
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) n₀ (u n) x))
          (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := by
          rw [ENNReal.ofReal_toReal hptop']
    _ ≤ ENNReal.ofReal (((iwArithFreqsNew ρ l₁).card : ℝ)
            * (∑' j : ℤ,
                ‖Work.KMTAreas.A7.cw
                  (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uRep ρ l₁ l₂ k₁ k₂)) j‖))
          * MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
              (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count := hper
    _ ≤ ENNReal.ofReal (boxKernelConstRep ρ B + 1)
          * MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
              (ENNReal.ofReal p.toReal) MeasureTheory.Measure.count :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hconst) _
    _ = ENNReal.ofReal (boxKernelConstRep ρ B + 1)
          * MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
              p MeasureTheory.Measure.count := by
          rw [ENNReal.ofReal_toReal hptop']

end Work.KMTAreas.A7Rep
