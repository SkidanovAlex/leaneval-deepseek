import Mathlib
import Submission.Work.TMComp.IDSDefs
import Submission.Work.TMComp.prove_UniqErg
import Submission.Work.TMComp.IDSEqui.defs
import Submission.Work.TMComp.IDSEqui.visitBound
import Submission.Work.TMComp.IDSEqui.integralRamp

/-!
# `IDSEqui`: the orbit visits the arc `{fracDist < δ}` at frequency `2δ`

`Work.TMComp.shiftCount α θ δ n` is the number of `j < n` with `fracDist (θ + jα) < δ`,
i.e. the number of visits of the finite orbit `θ, θ+α, …, θ+(n-1)α` of the irrational rotation
by `α` to the arc `A_δ = {fracDist < δ}` of the circle, of measure `2δ`.

The rotation is uniquely ergodic, so the visit frequency converges to `2δ`, *uniformly in the
starting point*; this uniform lower bound is the content of `count`.

The proof uses the uniform form of Weyl equidistribution, `Work.TMComp.prove_UniqErg`
(`P_UniqErg`), applied to a *continuous* minorant `minor δ δ'` of the indicator of `A_δ`:

* `minor δ δ'` (in `IDSEqui/defs.lean`) is `1` on `{fracDist ≤ δ'}`, drops linearly to `0` on
  `{δ' ≤ fracDist ≤ δ}` and vanishes on `{fracDist ≥ δ}`; it is continuous and `1`-periodic,
  so equidistribution applies to it, and its mean is at least `2δ'` (`IDSEqui/integralRamp`);
* a sum of any function bounded by `1` and vanishing off `A_δ` is bounded by `shiftCount`
  (`IDSEqui/visitBound`);
* choosing `δ' = δ - η/4` (in the non-trivial case `2δ > η`) turns the mean bound `2δ'` into
  `2δ - η/2`, which absorbs the equidistribution error `η/4` and the loss `η/4` in the slope.
-/

namespace Work.TMComp.IDSEqui

open scoped BigOperators
open Filter

/-- **Visit frequency of the orbit to the arc `{fracDist < δ}`.**  For irrational `α` and
`δ ≤ 1/2`, the number of `j < n` with `fracDist (θ + jα) < δ` is at least `(2δ - η) n` for
all sufficiently large `n`, *uniformly in* `θ ∈ ℝ`. -/
theorem count (α : ℝ) (hα : Irrational α) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1/2) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : ℝ,
      (2 * δ - η) * (n : ℝ) ≤ (Work.TMComp.shiftCount α θ δ n : ℝ) := by
  by_cases hcase : 2 * δ - η ≤ 0
  · -- the target bound is nonpositive: no visit count is needed
    refine ⟨1, fun n _ _ => ?_⟩
    exact (mul_nonpos_of_nonpos_of_nonneg hcase (Nat.cast_nonneg n)).trans (Nat.cast_nonneg _)
  · have hpos : 0 < 2 * δ - η := not_le.mp hcase
    set δ' : ℝ := δ - η / 4 with hδ'mem
    have hδ'pos : 0 < δ' := by rw [hδ'mem]; linarith
    have hδ'lt : δ' < δ := by rw [hδ'mem]; linarith
    have hcont : Continuous (minor δ δ') := continuous_minor δ δ'
    have hper : ∀ x : ℝ, minor δ δ' (x + 1) = minor δ δ' x := minor_periodic δ δ'
    -- uniform Birkhoff convergence for the continuous minorant
    have htu : TendstoUniformly
        (fun (n : ℕ) (x : ℝ) => (∑ j ∈ Finset.range n, minor δ δ' (x + (j : ℝ) * α)) / (n : ℝ))
        (fun _ => ∫ x in (0 : ℝ)..1, minor δ δ' x) atTop :=
      Work.TMComp.prove_UniqErg α hα (minor δ δ') hcont hper
    rw [Metric.tendstoUniformly_iff] at htu
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x : ℝ,
        dist (∫ x in (0 : ℝ)..1, minor δ δ' x)
          ((∑ j ∈ Finset.range n, minor δ δ' (x + (j : ℝ) * α)) / (n : ℝ)) < η / 4 := by
      have h := htu (η / 4) (by linarith)
      rwa [eventually_atTop] at h
    -- the mean of the minorant
    have hN := integralRamp δ δ' hδ'pos hδ'lt hδ'
    refine ⟨max N₀ 1, fun n hn θ => ?_⟩
    have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hdist := hN₀ n hnN₀ θ
    rw [Real.dist_eq] at hdist
    have hlow : (∫ x in (0 : ℝ)..1, minor δ δ' x) - η / 4 <
        (∑ j ∈ Finset.range n, minor δ δ' (θ + (j : ℝ) * α)) / (n : ℝ) := by
      have h := (abs_lt.mp hdist).2
      linarith
    -- clear the division by `n`
    have hS1 : (n : ℝ) * ((∫ x in (0 : ℝ)..1, minor δ δ' x) - η / 4) <
        ∑ j ∈ Finset.range n, minor δ δ' (θ + (j : ℝ) * α) := by
      have hmul := mul_lt_mul_of_pos_left hlow hnpos
      rwa [mul_div_cancel₀ _ (ne_of_gt hnpos)] at hmul
    have hS2 : (n : ℝ) * (2 * δ' - η / 4) ≤
        (n : ℝ) * ((∫ x in (0 : ℝ)..1, minor δ δ' x) - η / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hnpos)
    have hS3 : (2 * δ - η) * (n : ℝ) ≤ (n : ℝ) * (2 * δ' - η / 4) := by
      have hcoef : 2 * δ - η ≤ 2 * δ' - η / 4 := by rw [hδ'mem]; linarith
      calc (2 * δ - η) * (n : ℝ) ≤ (2 * δ' - η / 4) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right hcoef (le_of_lt hnpos)
        _ = (n : ℝ) * (2 * δ' - η / 4) := by ring
    -- the minorant is dominated by the visit count
    have hvisit := visitBound α θ δ n (minor δ δ') (fun x => minor_le_one δ δ' x)
        (fun x hx => minor_eq_zero hδ'lt hx)
    exact (lt_of_le_of_lt (hS3.trans hS2) hS1).le.trans hvisit

end Work.TMComp.IDSEqui
