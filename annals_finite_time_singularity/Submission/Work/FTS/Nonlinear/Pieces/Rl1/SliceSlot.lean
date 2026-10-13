import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.SliceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

/-! ## The two weight comparisons of a single angular slice

The `H^k`-integrand carries the weights `w(z)²·sin(2θ)^{-η}` (radial slots) and
`w(z)²·sin(2θ)^{-γ}` (mixed slots).  On `z > 0` one has `1 ≤ w z`, and on
`0 < θ < π/2` one has `1 ≤ sin(2θ)^{-r}` for every `r ≥ 0`; hence each slot weight
dominates `w z` alone, which is exactly the amount of weight needed to compare the
plain angular `L²`-norm of a slot with its weighted version. -/

/-- `1 ≤ w z` for `z > 0`, since `w z = (1+z)²/z²` and `(1+z)² ≥ z²`. -/
private lemma one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith [sq_nonneg z]

/-- For `0 < y ≤ 1` and `0 ≤ r` one has `1 ≤ y ^ (-r)`. -/
private lemma one_le_rpow_neg {y r : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hr : 0 ≤ r) :
    1 ≤ y ^ (-r) := by
  rw [Real.rpow_neg hy.le, one_le_inv₀ (Real.rpow_pos_of_pos hy r)]
  exact Real.rpow_le_one hy.le hy1 hr

/-- `sin (2θ) > 0` on the open angular interval. -/
private lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `1 ≤ sin(2θ)^{-γ}` on the open angular interval, for `0 < α` (i.e. `γ > 0`). -/
private lemma one_le_thGam {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    1 ≤ Work.FTS.EllipticEst.thGam α θ := by
  rw [Work.FTS.EllipticEst.thGam]
  exact one_le_rpow_neg (sin_two_pos hθ) (Real.sin_le_one _) (Work.Spaces.gam_pos hα).le

/-- `1 ≤ sin(2θ)^{-η}` on the open angular interval (`η = 99/100 > 0`). -/
private lemma one_le_thEta {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.FTS.EllipticEst.thEta]
  exact one_le_rpow_neg (sin_two_pos hθ) (Real.sin_le_one _) Work.Spaces.eta_pos.le

/-- Pointwise slot comparison for a mixed derivative: on the open angular interval the
weighted square `(a·Wt)² = a²·w(z)²·sin(2θ)^{-γ}` dominates `w(z)·a²`, because
`w(z)·sin(2θ)^{-γ} ≥ 1`. -/
private lemma w_mul_sq_le_mixed {α z θ a : ℝ} (hα : 0 < α) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z * a ^ 2 ≤ (a * Work.Spaces.Wt α z θ) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hw1 : 1 ≤ Work.Spaces.w z := one_le_w hz
  have hw0 : 0 ≤ Work.Spaces.w z := le_trans zero_le_one hw1
  have hprod : 1 ≤ Work.Spaces.w z * Work.FTS.EllipticEst.thGam α θ := by
    have h := mul_le_mul hw1 (one_le_thGam hα hθ) (zero_le_one (α := ℝ)) hw0
    simpa using h
  calc Work.Spaces.w z * a ^ 2 = a ^ 2 * Work.Spaces.w z * 1 := by ring
    _ ≤ a ^ 2 * Work.Spaces.w z * (Work.Spaces.w z * Work.FTS.EllipticEst.thGam α θ) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg a) hw0)
    _ = (a * Work.Spaces.Wt α z θ) ^ 2 := by
        rw [mul_pow, Work.FTS.EllipticEst.Wt_sq hθI α z]
        ring

/-- Pointwise slot comparison for a pure `D_z`-derivative: on the open angular interval the
weighted square `(a·w(z)/sin(2θ)^{η/2})² = a²·w(z)²·sin(2θ)^{-η}` dominates `w(z)·a²`,
because `w(z)·sin(2θ)^{-η} ≥ 1`. -/
private lemma w_mul_sq_le_rad {z θ a : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z * a ^ 2
      ≤ (a * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hw1 : 1 ≤ Work.Spaces.w z := one_le_w hz
  have hw0 : 0 ≤ Work.Spaces.w z := le_trans zero_le_one hw1
  have hprod : 1 ≤ Work.Spaces.w z * Work.FTS.EllipticEst.thEta θ := by
    have h := mul_le_mul hw1 (one_le_thEta hθ) (zero_le_one (α := ℝ)) hw0
    simpa using h
  calc Work.Spaces.w z * a ^ 2 = a ^ 2 * Work.Spaces.w z * 1 := by ring
    _ ≤ a ^ 2 * Work.Spaces.w z * (Work.Spaces.w z * Work.FTS.EllipticEst.thEta θ) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg a) hw0)
    _ = (a * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [mul_pow, Work.FTS.EllipticEst.w_div_sin_sq hθI z]
        ring

/-- Single-slot domination of `HkIntegrand` by a weighted angular `L²`-norm of one slot: for
`0 < α`, `f ∈ ℋ^k` in the honest sense (`HkMem`) and `z > 0`, each `θ`-slice square
`∫_θ (D_z^jD_θ^i f)²` (`i ≥ 1`, `i+j ≤ k`) and `∫_θ (D_z^i f)²` (`i ≤ k`) is dominated by
`(1/w z)∫_θ HkIntegrand α k f z θ`.
Route: pointwise on `θ ∈ (0,π/2)` the slot weight satisfies `1 ≤ w z·sin(2θ)^{-γ}` (this uses
`0 < α`, i.e. `γ = 1+α/10 ≥ 0`), hence `w z·(mixed j i f)² ≤ (mixed j i f·Wt)² ≤ HkIntegrand`
(a.e. in `θ`, the two boundary lines are null); `∫_θ HkIntegrand` is `θ`-integrable by
`hmem.1 z hz`; conclude with `MeasureTheory.integral_mono_of_nonneg`, which needs no
measurability of the dominated integrand.  (The second conjunct uses `eta > 0`.) -/
theorem SliceSlot (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hmem : Work.Spaces.HkMem α k f) :
    (∀ j i : ℕ, 1 ≤ i → i + j ≤ k → ∀ z : ℝ, 0 < z →
      Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) ∧
    (∀ i : ℕ, i ≤ k → ∀ z : ℝ, 0 < z →
      Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hS0 : (volume : Measure ℝ) ({0, π / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (Set.Finite.insert 0 (Set.finite_singleton (π / 2))) volume
  -- a.e. every `θ` is different from the two angular endpoints
  have hglobS : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({0, π / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ hS0
    intro θ hθ
    by_contra h
    exact hθ h
  -- a.e. `θ ∈ Iθ` and `θ` is not an endpoint: the angular integrand set of the pointwise bound
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      θ ∉ ({0, π / 2} : Set ℝ) ∧ θ ∈ Work.Spaces.Iθ :=
    (MeasureTheory.ae_restrict_of_ae hglobS).and
      (MeasureTheory.ae_restrict_of_forall_mem hIθ_meas fun θ hθ => hθ)
  have hIθ_open : ∀ θ : ℝ, θ ∉ ({0, π / 2} : Set ℝ) → θ ∈ Work.Spaces.Iθ →
      θ ∈ Set.Ioo 0 (π / 2) := by
    intro θ hθS hθI
    have hne : θ ≠ 0 ∧ θ ≠ π / 2 := by simpa using hθS
    have hI : 0 ≤ θ ∧ θ ≤ π / 2 := by simpa [Work.Spaces.Iθ] using hθI
    exact ⟨lt_of_le_of_ne hI.1 (Ne.symm hne.1), lt_of_le_of_ne hI.2 hne.2⟩
  constructor
  · intro j i hi hij z hz
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ =>
        mul_nonneg (le_trans zero_le_one (one_le_w hz)) (sq_nonneg _))
      (hmem.1 z (by simp [Work.Spaces.Iz]; linarith)) ?_
    refine Filter.Eventually.mono hae fun θ hθ => ?_
    exact le_trans (w_mul_sq_le_mixed hα hz (hIθ_open θ hθ.1 hθ.2))
      (Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j hi hij)
  · intro i hi z hz
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ =>
        mul_nonneg (le_trans zero_le_one (one_le_w hz)) (sq_nonneg _))
      (hmem.1 z (by simp [Work.Spaces.Iz]; linarith)) ?_
    refine Filter.Eventually.mono hae fun θ hθ => ?_
    exact le_trans (w_mul_sq_le_rad hz (hIθ_open θ hθ.1 hθ.2))
      (Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hi)

end Work.FTS.Nonlinear.Pieces.Rl1
