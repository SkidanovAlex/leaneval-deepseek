/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `ℋ^k`-norm of the explicit bump is uniformly bounded

The projection `PZero.Pz = id − (L₁₂ · 0 / pzNorm) • bump` of `StrongEps/PZero.lean` is
bounded on `ℋ^k` by `‖Pz f‖ ≤ ‖f‖ + |L₁₂ f 0|/pzNorm · ‖bump‖`, so the constant in
`hkNorm_Pz_le` needs a *single* bound for `HkNorm α k bump` over the whole parameter range
`α ∈ (0,1]`, `k ≤ 6` — that is exactly `bumpHkNormBound`.

The bound is elementary.  The only place where `α` enters `HkIntegrand` is through the
angular weight `Wt α z θ = w z · sin(2θ)^{-γ(α)/2}`, and

* `γ(α) = 1 + α/10 ≤ γ(1) = 11/10` for `α ≤ 1`, while
* on `Iθ = [0,π/2]` the base `sin(2θ)` lies in `[0,1]`,

so `wTheta α θ ≤ wTheta 1 θ` pointwise on `Iθ` (`rpow` is antitone in the exponent for a
base in `[0,1]`).  Hence `HkIntegrand α k bump ≤ HkIntegrand 1 6 bump` pointwise
(the sums only gain terms when `k` grows), and the two integrals are compared with the
integrability supplied by `HkMem_bump`.  The resulting constant is
`√(HkSq 1 6 bump) + 1`, i.e. an explicit, `α`-independent number.

Everything below is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.PZeroAux.softClass_Pz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

set_option autoImplicit false

/-! ## The two families of summands of `HkIntegrand` -/

/-- The pure `D_z`-slot of `HkIntegrand` (no dependence on `α`). -/
def bumpHk_zTerm (i : ℕ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter i Work.FTS.StrongEps.bump z θ
    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed slot of `HkIntegrand`. -/
def bumpHk_slotTerm (α : ℝ) (k : ℕ) (i j : ℕ) (z θ : ℝ) : ℝ :=
  if 1 ≤ i ∧ i + j ≤ k
    then (Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ * Work.Spaces.Wt α z θ) ^ 2
    else 0

theorem bumpHk_zTerm_nonneg (i : ℕ) (z θ : ℝ) : 0 ≤ bumpHk_zTerm i z θ := by
  rw [bumpHk_zTerm]; exact sq_nonneg _

theorem bumpHk_slotTerm_nonneg (α : ℝ) (k : ℕ) (i j : ℕ) (z θ : ℝ) :
    0 ≤ bumpHk_slotTerm α k i j z θ := by
  rw [bumpHk_slotTerm]; split_ifs <;> [exact sq_nonneg _; exact le_refl 0]

/-- `HkIntegrand` of the bump, written with the two named summands. -/
theorem bumpHk_HkIntegrand_eq (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump z θ
      = (∑ i ∈ Finset.range (k + 1), bumpHk_zTerm i z θ)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            bumpHk_slotTerm α k i j z θ := by
  simp only [Work.Spaces.HkIntegrand, bumpHk_zTerm, bumpHk_slotTerm]

/-! ## Monotonicity of the angular weight in `α` -/

/-- The angular weight is antitone in `α` on `(0,1]`: `γ(α) ≤ γ(1)` and the base
`sin(2θ) ∈ [0,1]` on `θ ∈ [0,π/2]`. -/
theorem bumpHk_wTheta_le_one {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {θ : ℝ}
    (hθ : 0 ≤ Real.sin (2 * θ)) :
    Work.Spaces.wTheta α θ ≤ Work.Spaces.wTheta 1 θ := by
  rw [Work.Spaces.wTheta, Work.Spaces.wTheta]
  have hgam : Work.Spaces.gam α ≤ Work.Spaces.gam 1 := by
    rw [Work.Spaces.gam, Work.Spaces.gam]; linarith [hα.2]
  refine Real.rpow_le_rpow_of_exponent_ge_of_imp hθ (Real.sin_le_one _)
    (by linarith) ?_
  intro hx hy
  have hp := Work.Spaces.gam_pos hα.1
  exfalso; linarith

/-- The angular weight is nonnegative where `sin(2θ) ≥ 0` (in particular on `Iθ`). -/
theorem bumpHk_wTheta_nonneg {α : ℝ} {θ : ℝ} (hθ : 0 ≤ Real.sin (2 * θ)) :
    0 ≤ Work.Spaces.wTheta α θ := by
  rw [Work.Spaces.wTheta]; exact Real.rpow_nonneg hθ _

/-- Absolute-value form of the monotonicity of `Wt`. -/
theorem bumpHk_Wt_abs_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {θ : ℝ}
    (hθ : 0 ≤ Real.sin (2 * θ)) (z : ℝ) :
    |Work.Spaces.Wt α z θ| ≤ |Work.Spaces.Wt 1 z θ| := by
  have hw : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have h1 := bumpHk_wTheta_le_one hα hθ
  have h0 : 0 ≤ Work.Spaces.wTheta α θ := bumpHk_wTheta_nonneg hθ
  have h2 : 0 ≤ Work.Spaces.wTheta 1 θ := bumpHk_wTheta_nonneg hθ
  rw [Work.Spaces.Wt, Work.Spaces.Wt, abs_mul, abs_mul, abs_of_nonneg hw,
    abs_of_nonneg h0, abs_of_nonneg h2]
  exact mul_le_mul_of_nonneg_left h1 hw

/-- The mixed slot is monotone in `(α, k)` on the admissible range. -/
theorem bumpHk_slotTerm_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {θ : ℝ}
    (hθ : 0 ≤ Real.sin (2 * θ)) (z : ℝ) {k : ℕ} (hk : k ≤ 6) (i j : ℕ) :
    bumpHk_slotTerm α k i j z θ ≤ bumpHk_slotTerm 1 6 i j z θ := by
  have habs : |Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ * Work.Spaces.Wt α z θ|
      ≤ |Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ * Work.Spaces.Wt 1 z θ| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (bumpHk_Wt_abs_le hα hθ z) (abs_nonneg _)
  rw [bumpHk_slotTerm, bumpHk_slotTerm]
  by_cases h : 1 ≤ i ∧ i + j ≤ k
  · have h6 : 1 ≤ i ∧ i + j ≤ 6 := ⟨h.1, by omega⟩
    rw [if_pos h, if_pos h6, sq_le_sq]
    exact habs
  · rw [if_neg h]
    split_ifs with h6
    · exact sq_nonneg _
    · exact le_refl 0

/-! ## The pointwise comparison of the integrands -/

/-- **Pointwise comparison.**  On the angular interval (where `sin(2θ) ≥ 0`), the
`ℋ^k`-integrand of the bump for `α ≤ 1`, `k ≤ 6` is dominated by the `ℋ⁶`-integrand at
`α = 1`: the `α`-dependence is only in the weight, which is antitone in `α`, and growing
`k` only adds nonnegative summands. -/
theorem bumpHk_HkIntegrand_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {k : ℕ} (hk : k ≤ 6)
    {z θ : ℝ} (hθ : 0 ≤ Real.sin (2 * θ)) :
    Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump z θ
      ≤ Work.Spaces.HkIntegrand 1 6 Work.FTS.StrongEps.bump z θ := by
  have hk7 : k + 1 ≤ 7 := by omega
  rw [bumpHk_HkIntegrand_eq α k z θ, bumpHk_HkIntegrand_eq 1 6 z θ]
  have h1 : (∑ i ∈ Finset.range (k + 1), bumpHk_zTerm i z θ)
      ≤ (∑ i ∈ Finset.range 7, bumpHk_zTerm i z θ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hk7)
      (fun i _ _ => bumpHk_zTerm_nonneg i z θ)
  have hinner : ∀ i, (∑ j ∈ Finset.range (k + 1), bumpHk_slotTerm α k i j z θ)
      ≤ (∑ j ∈ Finset.range 7, bumpHk_slotTerm 1 6 i j z θ) := fun i =>
    calc (∑ j ∈ Finset.range (k + 1), bumpHk_slotTerm α k i j z θ)
        ≤ (∑ j ∈ Finset.range (k + 1), bumpHk_slotTerm 1 6 i j z θ) :=
          Finset.sum_le_sum fun j _ => bumpHk_slotTerm_le hα hθ z hk i j
      _ ≤ (∑ j ∈ Finset.range 7, bumpHk_slotTerm 1 6 i j z θ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun j _ _ => bumpHk_slotTerm_nonneg 1 6 i j z θ)
  have h2a : (∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (k + 1), bumpHk_slotTerm α k i j z θ)
      ≤ (∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range 7, bumpHk_slotTerm 1 6 i j z θ) :=
    Finset.sum_le_sum fun i _ => hinner i
  have h2b : (∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range 7, bumpHk_slotTerm 1 6 i j z θ)
      ≤ (∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7, bumpHk_slotTerm 1 6 i j z θ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hk7)
      (fun i _ _ => Finset.sum_nonneg fun j _ => bumpHk_slotTerm_nonneg 1 6 i j z θ)
  exact add_le_add h1 (le_trans h2a h2b)

/-- On `Iθ` the sine of the doubled angle is nonnegative. -/
theorem bumpHk_sin_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-! ## Monotonicity of `HkSq` -/

/-- **`HkSq` is monotone in `(α, k)`** on the admissible range.  Integrability of the
dominating integrand is `HkMem_bump 1 6`. -/
theorem bumpHk_HkSq_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {k : ℕ} (hk : k ≤ 6) :
    Work.Spaces.HkSq α k Work.FTS.StrongEps.bump
      ≤ Work.Spaces.HkSq 1 6 Work.FTS.StrongEps.bump := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_mono_on (HkMem_bump α k).2 (HkMem_bump 1 6).2
    measurableSet_Ici ?_
  intro z hz
  refine MeasureTheory.setIntegral_mono_on ((HkMem_bump α k).1 z hz) ((HkMem_bump 1 6).1 z hz)
    ?_ ?_
  · rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  · intro θ hθ
    exact bumpHk_HkIntegrand_le hα hk (bumpHk_sin_nonneg_of_mem_Iθ hθ)

/-! ## The target -/

theorem bumpHkNormBound :
    ∃ B : ℝ, 0 < B ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, k ≤ 6 →
      Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump ≤ B := by
  refine ⟨Real.sqrt (Work.Spaces.HkSq 1 6 Work.FTS.StrongEps.bump) + 1, by positivity, ?_⟩
  intro α hα k hk
  rw [Work.Spaces.HkNorm]
  refine le_trans (Real.sqrt_le_sqrt (bumpHk_HkSq_le hα hk)) ?_
  have hnn : 0 ≤ Real.sqrt (Work.Spaces.HkSq 1 6 Work.FTS.StrongEps.bump) :=
    Real.sqrt_nonneg _
  linarith

end Work.FTS.StrongEps.PZeroAux
