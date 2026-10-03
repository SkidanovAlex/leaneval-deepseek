import Mathlib
import Submission.Work.KMTAreas.A4.symbolRatioDefs

namespace Work.KMTAreas.A4

open MeasureTheory
open Work.Analysis.IonescuWainger

/-! ## Elementary facts about the rescaled cutoff `bumpRescaled` -/

/-- `η_{≤k}(θ) = 1` when `|θ/2^k| ≤ 1/2`. -/
theorem bumpRescaled_eq_one {k : ℤ} {θ : ℝ} (h : |θ / (2 : ℝ) ^ k| ≤ 1 / 2) :
    bumpRescaled k θ = 1 := by
  rw [bumpRescaled]
  refine ContDiffBump.one_of_mem_closedBall _ ?_
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  show |θ / (2 : ℝ) ^ k| ≤ (1 : ℝ) / 2
  exact h

/-- `η_{≤k}(θ) = 0` when `1 ≤ |θ/2^k|`. -/
theorem bumpRescaled_eq_zero {k : ℤ} {θ : ℝ} (h : 1 ≤ |θ / (2 : ℝ) ^ k|) :
    bumpRescaled k θ = 0 := by
  rw [bumpRescaled]
  refine ContDiffBump.zero_of_le_dist _ ?_
  rw [dist_zero_right, Real.norm_eq_abs]
  show (1 : ℝ) ≤ |θ / (2 : ℝ) ^ k|
  exact h

/-- The rescaling identity `θ/2^{k'} = 2^{k-k'} · (θ/2^k)` for `k' ≤ k`. -/
private theorem div_zpow_eq_mul_div_zpow {k k' : ℤ} (θ : ℝ) :
    θ / (2 : ℝ) ^ k' = (2 : ℝ) ^ (k - k') * (θ / (2 : ℝ) ^ k) := by
  have hpow : (2 : ℝ) ^ (k - k') * (2 : ℝ) ^ k' = (2 : ℝ) ^ k := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [← hpow, mul_div_assoc']
  exact (mul_div_mul_left (c := (2 : ℝ) ^ (k - k')) θ ((2 : ℝ) ^ k')
    (ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 2) (k - k')))).symm

/-- **Monotonicity of the rescaled cutoff in the scale**: `η_{≤k'}(θ) ≤ η_{≤k}(θ)` for `k' ≤ k`.

`η` is equal to `1` on `[-1/2,1/2]` and vanishes off `[-1,1]`, so `kmtBump (θ/2^k)` can only
increase with `k`: the argument `θ/2^k` shrinks towards `0` as `k` grows.  This is the only
place where the explicit values of the `ContDiffBump` are used. -/
theorem bumpRescaled_mono {k k' : ℤ} (hk : k' ≤ k) (θ : ℝ) :
    bumpRescaled k' θ ≤ bumpRescaled k θ := by
  by_cases h : |θ / (2 : ℝ) ^ k| ≤ 1 / 2
  · rw [bumpRescaled_eq_one h]
    exact bumpRescaled_le_one k' θ
  · have h : 1 / 2 < |θ / (2 : ℝ) ^ k| := lt_of_not_ge h
    rcases eq_or_lt_of_le hk with hkk | hkk
    · subst hkk; exact le_rfl
    · have h' : 1 ≤ |θ / (2 : ℝ) ^ (k')| := by
        rw [div_zpow_eq_mul_div_zpow (k := k) (k' := k') θ, abs_mul,
          abs_of_nonneg (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) (k - k')))]
        have hp : (2 : ℝ) ≤ (2 : ℝ) ^ (k - k') := by
          have h1 : (1 : ℤ) ≤ k - k' := by omega
          simpa using zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) h1
        have hpos : 0 < (2 : ℝ) ^ (k - k') := zpow_pos (by norm_num : (0 : ℝ) < 2) _
        have hlt := mul_lt_mul_of_pos_left h hpos
        nlinarith
      rw [bumpRescaled_eq_zero h']
      exact bumpRescaled_nonneg k θ

/-! ## Monotonicity of the symbol -/

/-- **Monotonicity of the real Ionescu–Wainger symbol in `(l,k)`.**

`Work.KMTAreas.A4.symReal ρ l k R ξ` is the real-valued version of the paper's symbol
`σ_{l,k}(ξ) = ∑_{α ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(ξ - α)`, expanded over the periodisation index set
`Work.KMTAreas.A4.suppIdx R`.  Since `(ℚ/ℤ)_{≤l'} ⊆ (ℚ/ℤ)_{≤l}` for `l' ≤ l`
(`iwArithFreqs_mono`) and the cutoff `θ ↦ kmtBump (θ/2^k)` is pointwise nondecreasing in `k`
(`η = 1` on `[-1/2,1/2]` and `η = 0` off `[-1,1]`), the symbol is monotone in `(l,k)`.

Route for the `k`-part, which is the only subtle point: `kmtBump` is an *arbitrary*
`ContDiffBump 0` with `rIn = 1/2`, `rOut = 1` — its fields give `kmtBump x = 1` for `|x| ≤ 1/2`
and `kmtBump x = 0` for `1 ≤ |x|`, but do **not** by themselves give monotonicity in `|x|`.
Write `θ/2^{k'} = 2^{k-k'} · (θ/2^k)`.  If `|θ/2^k| ≤ 1/2` then `kmtBump (θ/2^k) = 1 ≥
kmtBump (θ/2^{k'})`.  If `|θ/2^k| > 1/2`: for `k' = k` the two arguments coincide, and for
`k' < k` one has `|θ/2^{k'}| = 2^{k-k'}|θ/2^k| > 1`, so `kmtBump (θ/2^{k'}) = 0`. -/
theorem symRealMono {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l l' : ℕ} (hl : l' ≤ l)
    {k k' : ℤ} (hk : k' ≤ k) (R : ℝ) (ξ : Work.Analysis.IonescuWainger.Circle) :
    Work.KMTAreas.A4.symReal ρ l' k' R ξ ≤ Work.KMTAreas.A4.symReal ρ l k R ξ := by
  -- step 1: grow the arithmetic-frequency set from `l'` to `l` at fixed scale `k'`
  have h1 : symReal ρ l' k' R ξ ≤ symReal ρ l k' R ξ := by
    unfold symReal
    refine Finset.sum_le_sum_of_subset_of_nonneg (iwArithFreqs_mono hρ hρ1 hl) ?_
    intro α _ _
    exact Finset.sum_nonneg fun j _ => bumpRescaled_nonneg k' _
  -- step 2: grow the scale from `k'` to `k` at fixed height `l`
  have h2 : symReal ρ l k' R ξ ≤ symReal ρ l k R ξ := by
    unfold symReal
    exact Finset.sum_le_sum fun α _ =>
      Finset.sum_le_sum fun _ _ => bumpRescaled_mono hk _
  exact le_trans h1 h2

end Work.KMTAreas.A4
