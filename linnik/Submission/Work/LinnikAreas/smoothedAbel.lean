/-
# The smoothed Abel identity for `Ssm`

For a Dirichlet character `χ` mod `q` whose coefficients `λ(n) = Σ_{d ∣ n} χ(d)` are real, and
any real `β`, the triangle-weighted sum

  `Ssm χ β x = Σ_{n ≤ x} λ(n) n^{-β} (1 - n/x)`

is the Abel-type integral of the partial sums `A(u) = Σ_{n ≤ u} λ(n)`:

  `Ssm χ β x = ∫_1^x ( (1-β) u^{-β}/x + β u^{-(β+1)} ) A(u) du`     (`x` a positive integer).

The integrand is `F(u) = u^{1-β}/x - u^{-β}`, and `F(x) - F(n) = n^{-β}(1 - n/x)`, which is
exactly the `n`-th summand.  Formally the proof is a standard staircase decomposition: `A` is
constant on each interval between consecutive integers, so the integral is a finite sum of
integrals over `[n, x]`, computed by the fundamental theorem of calculus.

The individual pieces are proved in the sibling modules of this directory:

* `smoothedAbelStepSum` — the pointwise step-function identity `A(u) = Σ_{n ≤ x} λ(n)·1_{n ≤ u}`
  (valid for `u ≤ x`);
* `integral_step_mul` (below) — the staircase decomposition
  `∫_1^x g·(Σ_{n ≤ x} c_n·1_{n ≤ u}) = Σ_{n ≤ x} c_n ∫_n^x g`;
* `smoothedAbelInnerIntegral` — the evaluation `∫_n^x ((1-β)u^{-β}/x + β u^{-(β+1)}) du =
  n^{-β}(1 - n/x)` (FTC for `F`);
* `smoothedAbelIntegrable` — interval integrability of the weight (continuity on `[1,x]`);
* `smoothedAbelLhsCast` — the coercion of the real sum `Ssm` to the complex expression with
  complex powers.
-/
import Mathlib
import Submission.Work.LinnikAreas.RatioDefs
import Submission.Work.LinnikAreas.lamRealNonneg
import Submission.Work.LinnikAreas.smoothedAbelInnerIntegral
import Submission.Work.LinnikAreas.smoothedAbelLhsCast
import Submission.Work.LinnikAreas.smoothedAbelStepSum
import Submission.Work.LinnikAreas.smoothedAbelIntegrable

namespace Work.LinnikAreas

open DirichletCharacter Complex MeasureTheory
open scoped BigOperators

noncomputable section

/-- Pointwise algebra behind the staircase decomposition: multiplying the step function
`Σ_{n ∈ Icc 1 x} c_n · 1_{n ≤ u}` by `g u` and splitting off the constant part gives
`(Σ_n c_n)·g u - Σ_n g u·(c_n·1_{u < n})`.  (For real `n, u` one has `1_{n ≤ u} + 1_{u < n} = 1`.) -/
private lemma step_pointwise (c : ℕ → ℂ) (g : ℝ → ℂ) (x : ℕ) (u : ℝ) :
    g u * (∑ n ∈ Finset.Icc 1 x, c n * (if (n:ℝ) ≤ u then (1:ℂ) else 0))
      = (∑ n ∈ Finset.Icc 1 x, c n) * g u
        - ∑ n ∈ Finset.Icc 1 x, g u * (c n * (if u < (n:ℝ) then (1:ℂ) else 0)) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases le_or_gt ((n:ℝ)) u with h | h
  · rw [if_neg (not_lt.mpr h), if_pos h]; ring
  · rw [if_neg (not_le.mpr h), if_pos h]; ring

/-- **The staircase (Abel) decomposition.**  For an interval-integrable `g` and any coefficients
`c`, the integral against the step function `Σ_{n ∈ Icc 1 x} c_n·1_{n ≤ u}` is the finite sum of
the integrals of `g` over `[n, x]`:

  `∫_1^x g(u)·(Σ_{n ≤ x} c_n·1_{n ≤ u}) du = Σ_{n ≤ x} c_n ∫_n^x g(u) du`.

The proof writes the sum of indicator functions as `Σ_n c_n - Σ_n c_n·1_{u<n}`, uses a.e. equality
of `1_{u<n}` with the indicator of `(-∞, n]` (they differ only at the single point `u = n`) and the
truncation rule `∫_1^x 1_{u ≤ n}·g = ∫_1^n g`. -/
private lemma integral_step_mul (c : ℕ → ℂ) (g : ℝ → ℂ) (x : ℕ) (hx : 1 ≤ x)
    (hint : IntervalIntegrable g volume (1:ℝ) (x:ℝ)) :
    ∫ u in (1:ℝ)..(x:ℝ), g u * (∑ n ∈ Finset.Icc 1 x, c n * (if (n:ℝ) ≤ u then (1:ℂ) else 0))
      = ∑ n ∈ Finset.Icc 1 x, c n * ∫ u in (n:ℝ)..(x:ℝ), g u := by
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  -- each summand `g·(c_i·1_{u<i})` is interval integrable (a bounded step function times `g`)
  have hone : ∀ i ∈ Finset.Icc 1 x,
      IntervalIntegrable (fun u : ℝ => g u * (c i * (if u < (i:ℝ) then (1:ℂ) else 0)))
        volume (1:ℝ) (x:ℝ) := by
    intro i _
    refine intervalIntegrable_iff.mpr ((hint.def').mul_bdd (c := ‖c i‖) ?_ ?_)
    · exact (measurable_const.mul
        (Measurable.ite measurableSet_Iio measurable_const measurable_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => by
        by_cases h : u < (i:ℝ) <;> simp [h]
  have hT : IntervalIntegrable
      (fun u : ℝ => ∑ n ∈ Finset.Icc 1 x, g u * (c n * (if u < (n:ℝ) then (1:ℂ) else 0)))
      volume (1:ℝ) (x:ℝ) := by
    refine (IntervalIntegrable.sum (Finset.Icc 1 x) hone).congr (fun u _ => ?_)
    simp only [Finset.sum_apply]
  have hSg : IntervalIntegrable (fun u : ℝ => (∑ n ∈ Finset.Icc 1 x, c n) * g u)
      volume (1:ℝ) (x:ℝ) :=
    hint.const_mul _
  have hfun : (fun u : ℝ => g u * (∑ n ∈ Finset.Icc 1 x, c n * (if (n:ℝ) ≤ u then (1:ℂ) else 0)))
      = fun u : ℝ => (∑ n ∈ Finset.Icc 1 x, c n) * g u
          - ∑ n ∈ Finset.Icc 1 x, g u * (c n * (if u < (n:ℝ) then (1:ℂ) else 0)) :=
    funext fun u => step_pointwise c g x u
  rw [hfun, intervalIntegral.integral_sub hSg hT, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum
        (f := fun n u => g u * (c n * (if u < (n:ℝ) then (1:ℂ) else 0))) hone]
  -- the `n`-th integral is a constant multiple of the truncation `∫_1^n g`
  have hJn : ∀ n ∈ Finset.Icc 1 x,
      (∫ u in (1:ℝ)..(x:ℝ), g u * (c n * (if u < (n:ℝ) then (1:ℂ) else 0)))
        = c n * ∫ u in (1:ℝ)..(n:ℝ), g u := by
    intro n hn
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
    have hn1place : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have hnxplace : (n:ℝ) ≤ (x:ℝ) := by exact_mod_cast hnx
    have hnmem : (n:ℝ) ∈ Set.Icc (1:ℝ) (x:ℝ) := ⟨hn1place, hnxplace⟩
    -- `1_{u<n}` agrees with the indicator of `(-∞, n]` except at `u = n`
    have hnull : ∀ᵐ u : ℝ ∂volume, u ≠ (n:ℝ) := by
      rw [MeasureTheory.ae_iff]
      have hset : {u : ℝ | ¬ u ≠ (n:ℝ)} = {(n:ℝ)} := by ext u; simp
      rw [hset]; exact MeasureTheory.measure_singleton _
    have hae : ∀ᵐ u : ℝ ∂volume, u ∈ Set.uIoc (1:ℝ) (x:ℝ) →
        g u * (c n * (if u < (n:ℝ) then (1:ℂ) else 0))
          = c n * (Set.Iic (n:ℝ)).indicator g u := by
      filter_upwards [hnull] with u hu _
      rw [Set.indicator_apply]
      simp only [Set.mem_Iic]
      by_cases h : u < (n:ℝ)
      · rw [if_pos h, if_pos (le_of_lt h)]; ring
      · rw [if_neg h, if_neg (not_le.mpr (lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hu)))]; ring
    have hind : (∫ u in (1:ℝ)..(x:ℝ), (Set.Iic (n:ℝ)).indicator g u)
        = ∫ u in (1:ℝ)..(n:ℝ), g u :=
      intervalIntegral.integral_indicator hnmem
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul, hind]
  rw [Finset.sum_congr rfl hJn, Finset.sum_mul, ← Finset.sum_sub_distrib]
  -- `∫_1^x g - ∫_1^n g = ∫_n^x g`
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
  have hn1place : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hnxplace : (n:ℝ) ≤ (x:ℝ) := by exact_mod_cast hnx
  have h1n : IntervalIntegrable g volume (1:ℝ) (n:ℝ) := by
    refine intervalIntegrable_iff.mpr ((intervalIntegrable_iff.mp hint).mono_set ?_)
    intro u hu
    rw [Set.uIoc_of_le hn1place] at hu
    rw [Set.uIoc_of_le hx1]
    exact ⟨hu.1, le_trans hu.2 hnxplace⟩
  rw [← mul_sub, intervalIntegral.integral_interval_sub_left hint h1n]

/-- **The smoothed Abel identity.**  For a character whose `λ`-coefficients are real and a positive
integer `x`,

  `Ssm χ β x = ∫_1^x ( (1-β) u^{-β}/x + β u^{-(β+1)} ) A(u) du`,

where `A(u) = Σ_{n ≤ u} λ(n)` is the (complex) summatory function and the powers are complex
powers of the positive real `u`. -/
theorem smoothedAbel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχre : ∀ n : ℕ, (Work.LinnikAreas.lam χ n).im = 0) (β : ℝ) {x : ℕ} (hx : 1 ≤ x) :
    (Work.LinnikAreas.Ssm χ β (x:ℝ) : ℂ) = ∫ u in (1:ℝ)..(x:ℝ),
      (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1)))
        * Work.LinnikAreas.Asum χ u := by
  rw [smoothedAbelLhsCast χ hχre β hx]
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  -- replace `A(u)` by its step-function form `Σ_{n ≤ x} λ(n)·1_{n ≤ u}`
  have hcongr : (∫ u in (1:ℝ)..(x:ℝ),
        (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1)))
          * Work.LinnikAreas.Asum χ u)
      = ∫ u in (1:ℝ)..(x:ℝ),
        (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ) + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1)))
          * (∑ n ∈ Finset.Icc 1 x,
              Work.LinnikAreas.lam χ n * (if (n:ℝ) ≤ u then (1:ℂ) else 0)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hx1] at hu
    rw [smoothedAbelStepSum χ x u hu.2]
  rw [hcongr, integral_step_mul (Work.LinnikAreas.lam χ)
      (fun u : ℝ => (((1 - β) : ℂ) * (u:ℂ) ^ (-(β:ℂ)) / (x:ℂ)
        + (β:ℂ) * (u:ℂ) ^ (-((β:ℂ) + 1))))
      x hx (smoothedAbelIntegrable β x hx)]
  -- evaluate each inner integral by the fundamental theorem of calculus
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
  rw [smoothedAbelInnerIntegral β x n hn1 hnx]

end

end Work.LinnikAreas
