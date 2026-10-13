/-
# `D_θ` preserves `ℋ^k`-membership for the full range `α ≥ -1/10`

The `ℋ^k`-integrand of the paper (`Work.Spaces.HkIntegrand`) carries two angular weights:
the *light* weight `w(z)/sin(2θ)^{η/2}` (η = 99/100) on the pure radial derivatives `D_z^i f`
and the *heavy* weight `W = w(z)·sin(2θ)^{-γ/2}` (γ = 1 + α/10) on the genuinely mixed
derivatives `D_z^j D_θ^i f`, `i ≥ 1`.

For `g = D_θ f` every summand of `HkIntegrand α k g` is (up to the weight comparison) a
summand of `HkIntegrand α (k+1) f`:

* the pure summands of `g` are `D_z^i D_θ f`, which occur in the integrand of `f` at level
  `k+1` as mixed summands with the *heavy* weight, so the pointwise comparison needed is
  `w/√sin(2θ)^η ≤ w·sin(2θ)^{-γ/2}` — i.e. `η ≤ γ`, i.e. exactly `α ≥ -1/10`;
* the mixed summands of `g` are `D_z^j D_θ^{i+1} f`, which are literally mixed summands of
  `f` at level `k + 1` (the index reindexing `Work.Coercivity.SumRowShift_eq`).

This is the analogue of `Work.Coercivity.HkIntegrand_Dth_le`, whose hypothesis `0 < α` is
strengthened here to the sharp range `α ≥ -1/10` (at `α = -1/10` the two weights coincide).
The membership statement is then assembled with `Work.FTS.LocData.HkMem_of_majorant`, the
continuity of the integrand coming from `SmoothQuad (D_θ f)`
(`Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`), which the class
`Work.FTS.Nonlin.RegQ` supplies through its first component.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Coercivity.SumRowShift_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.E2Bound

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The weight comparison in the sharp range `α ≥ -1/10` -/

/-- `Work.Spaces.H_le_Wt` in its full range of validity: the light `H^0`-weight
`w/ sin(2θ)^{η/2}` is dominated by the heavy weight `Wt α = w·sin(2θ)^{-γ(α)/2}`
whenever `η ≤ γ(α)`, i.e. for `α ≥ -1/10` — the hypothesis of `H_le_Wt` (`0 < α`) can be
weakened to the sharp threshold, since its only use is `η ≤ γ(α)`. -/
theorem H_le_Wt_ge (α : ℝ) (hα : -(1/10 : ℝ) ≤ α) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  -- `w z ≥ 0` always, and `s := sin(2θ) ∈ [0,1]` for `θ ∈ [0,π/2]`.
  have ha : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  -- `η ≤ γ(α)` is exactly `α ≥ -1/10`.
  have hgam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
  -- Since `-γ/2 ≤ -η/2` and `sin(2θ) ∈ [0,1]`, we have `sin(2θ)^{-η/2} ≤ sin(2θ)^{-γ/2}`.
  have hkey : 1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    have h1 : 1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
      rw [one_div, ← Real.rpow_neg hs0]
    rw [h1]
    apply Real.rpow_le_rpow_of_exponent_ge_of_imp hs0 hs1
    · linarith
    · intro _ hy
      exact absurd hy (by norm_num [Work.Spaces.eta])
  -- Multiply by `w z ≥ 0` and square (both sides are nonnegative).
  calc (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z * (1 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [div_eq_mul_one_div]
    _ ≤ (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
        apply pow_le_pow_left₀ _ _ 2
        · exact mul_nonneg ha (div_nonneg zero_le_one (Real.rpow_nonneg hs0 _))
        · exact mul_le_mul_of_nonneg_left hkey ha

/-! ## Structural identities for the shifted families -/

/-- The pure family of the `H^k`-integrand of `D_θ f` is the family of mixed derivatives
`D_z^i D_θ f = mixed i 1 f` of `f`. -/
private lemma DzIter_Dth_eq (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dth f) = Work.Spaces.mixed i 1 f := by
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]

/-- The mixed family of the `H^k`-integrand of `D_θ f` is the mixed family of `f` with
the `D_θ`-order raised by one: `D_z^j D_θ^i D_θ f = mixed j (i+1) f`. -/
private lemma mixed_Dth_eq (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth f) = Work.Spaces.mixed j (i + 1) f := by
  simp only [Work.Spaces.mixed]
  have h : Work.Spaces.Dth f = Work.Spaces.DthIter 1 f := rfl
  rw [h, Work.Spaces.DthIter_add_right]

/-! ## Pointwise domination of the shifted integrands -/

/-- **Pointwise domination, `D_θ` case, sharp range.**  Every summand of the `H^k`-integrand
of `D_θ f` is dominated by a summand of the `H^{k+1}`-integrand of `f`: the pure summands
`D_z^i D_θ f` are mixed summands of `f` with weight `w/√sin^η ≤ W` (valid for `α ≥ -1/10`),
and the mixed summands `D_z^j D_θ^{i+1} f` are themselves mixed summands of `f` at level
`k + 1`. -/
theorem HkIntegrand_Dth_le_ge (α : ℝ) (hα : -(1/10 : ℝ) ≤ α) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
      ≤ Work.Spaces.HkIntegrand α (k + 1) f z θ := by
  set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  have hLHS : Work.Spaces.HkIntegrand α k (Work.Spaces.Dth f) z θ
      = (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * W) ^ 2
              else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Work.Spaces.HkIntegrand α (k + 1) f z θ
      = (∑ a ∈ Finset.range (k + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
            (if 1 ≤ a ∧ a + b ≤ k + 1 then (Work.Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ * H) ^ 2)
      ≤ ∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 1 f z θ * W) ^ 2 := by
    calc (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i (Work.Spaces.Dth f) z θ * H) ^ 2)
        = ∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 1 f z θ * H) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dth_eq i f])
      _ ≤ ∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 1 f z θ * W) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hw := H_le_Wt_ge α hα z θ hz hθ
          have h1 : (Work.Spaces.mixed i 1 f z θ * H) ^ 2
              = (Work.Spaces.mixed i 1 f z θ) ^ 2 * H ^ 2 := by ring
          have h2 : (Work.Spaces.mixed i 1 f z θ * W) ^ 2
              = (Work.Spaces.mixed i 1 f z θ) ^ 2 * W ^ 2 := by ring
          rw [h1, h2]
          exact mul_le_mul_of_nonneg_left hw (sq_nonneg _)
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (Work.Spaces.Dth f) z θ * W) ^ 2
                else 0))
      = (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, mixed_Dth_eq j i f]
    · rw [if_neg hc, if_neg hc]
  have hkey : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.mixed i 1 f z θ * W) ^ 2)
      + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j (i + 1) f z θ * W) ^ 2 else 0))
      = (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
          (if 1 ≤ a ∧ a + b ≤ k + 1 then (Work.Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simpa only using Work.Coercivity.SumRowShift_eq k
      (fun a b => (Work.Spaces.mixed b a f z θ * W) ^ 2)
  have hnn : 0 ≤ ∑ a ∈ Finset.range (k + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey, hnn]

/-! ## The membership target -/

/-- **`ℋ^k` is closed under `D_θ`, for `α ≥ -1/10`.**  The statement `HkMem_dth_of_RegQ_ge`
of the `E2Bound` node: if `f` lies in the regular class `RegQ α (n+1)`, then `D_θ f` lies in
`ℋⁿ`.  The class supplies the interior smoothness (`SmoothQuad`, hence the a.e. strong
measurability of the integrand needed by `HkMem_of_majorant`) and the honest `ℋ^{n+1}`
membership of `f`, which together with the pointwise domination `HkIntegrand_Dth_le_ge`
gives the claim. -/
theorem HkMem_dth_of_RegQ_ge (α : ℝ) (n : ℕ) (hα : -(1/10 : ℝ) ≤ α) {f : ℝ → ℝ → ℝ} (h : Work.FTS.Nonlin.RegQ α (n + 1) f) : Work.Spaces.HkMem α n (Work.Spaces.Dth f) := by
  obtain ⟨hsm, hmem, _hbd⟩ := h
  have hsm' : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) := by
    simpa using hsm.DthIter 1
  refine Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.Spaces.Dth f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ) ?_ hmem.1 hmem.2 ?_
  · exact Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α n (Work.Spaces.Dth f) hsm'
  · exact fun z hz θ hθ => HkIntegrand_Dth_le_ge α hα n f z θ hz hθ

end Work.FTS.CoercivityFix.E2Bound
