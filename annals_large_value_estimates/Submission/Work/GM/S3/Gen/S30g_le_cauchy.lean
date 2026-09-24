import Mathlib
import Submission.Work.GM.S3.gen_defs
import Submission.Work.GM.S3.RtildeSq_continuous
import Submission.Work.GM.S3.integral_mul_le_sqrt_mul_sqrt

namespace Work.GM.S3.Gen

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun)

/-- Flatten a triple nested sum over `s₁`, `s₂`, `s₃` into a single sum over the product index set
`s₁.product (s₂.product s₃)` (the shape required by `intervalIntegral.integral_finsetSum`; stated
product-first because that is what `Finset.sum_product` produces). -/
private lemma S30g_sum_prod_eq_nested3 (s₁ s₂ s₃ : Finset ℤ) (F : ℤ → ℤ → ℤ → ℝ) :
    ∑ p ∈ s₁.product (s₂.product s₃), F p.1 p.2.1 p.2.2
      = ∑ m₁ ∈ s₁, ∑ m₂ ∈ s₂, ∑ m₃ ∈ s₃, F m₁ m₂ m₃ := by
  calc ∑ p ∈ s₁.product (s₂.product s₃), F p.1 p.2.1 p.2.2
      = ∑ m₁ ∈ s₁, ∑ p ∈ s₂.product s₃, F m₁ p.1 p.2 :=
        Finset.sum_product s₁ (s₂.product s₃) (fun x : ℤ × (ℤ × ℤ) => F x.1 x.2.1 x.2.2)
    _ = ∑ m₁ ∈ s₁, ∑ m₂ ∈ s₂, ∑ m₃ ∈ s₃, F m₁ m₂ m₃ :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_product s₂ s₃ (fun x : ℤ × ℤ => F a x.1 x.2))

/-- **GM 10.1, first Cauchy–Schwarz step, three independent dyadic scales.**

With `S₃,₀ = Σ_m ∫_{v≍1} ‖R(v)‖ R̃(a₁)R̃(a₂) dv` (`S30g`), `S₃,₂ = ∫_{v≍1} (Σ_m R̃(a₁)R̃(a₂))² dv`
(`S32g`), and `R̃ = Rtilde W N B ψ₁ ψ₂` a nonnegative smoothing of `‖R‖²` (so
`Gsumg = Σ_m R̃ R̃ ≥ 0`), we have
`S₃,₀ ≤ (∫_{1/2}^{2}‖R(v)‖² dv)^{1/2} (S₃,₂)^{1/2}`.

Proof: interchange the finite `m`-sum with the interval integral, then Cauchy–Schwarz for
integrals.  The hypothesis `hB : 0 ≤ (N : ℝ) * B` is not needed for this step. -/
theorem S30g_le_cauchy (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hψ₁ : Work.GM.S3.IsBumpAtZero ψ₁ 16) (hψ₂ : Work.GM.S3.IsBumpAtOne ψ₂ 16) :
    Work.GM.S3.Gen.S30g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤
      Real.sqrt (∫ v in (1 / 2 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2) *
        Real.sqrt (Work.GM.S3.Gen.S32g N W B M₁ M₂ M₃ ψ₁ ψ₂) := by
  classical
  -- `Rtilde` is continuous (as `√(RtildeSq)`).
  have hc : Continuous (fun u : ℝ => Rtilde W N B ψ₁ ψ₂ u) := by
    have h := (RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂).sqrt
    simpa only [Rtilde, RtildeSq] using h
  -- both arguments of `Rtilde` are continuous on `[1/2,2]` (`v` stays away from `0` there).
  have harg1 : ∀ m₁ m₂ m₃ : ℤ, ContinuousOn
      (fun v : ℝ => Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v)) (Set.Icc (1 / 2 : ℝ) 2) := by
    intro m₁ m₂ m₃
    refine hc.comp_continuousOn ?_
    by_cases h : m₂ = 0
    · subst h
      have hconst : arg1 m₁ 0 m₃ = fun _ : ℝ => 0 := by funext v; simp [arg1]
      rw [hconst]; exact continuousOn_const
    · have hne : (m₂ : ℝ) ≠ 0 := by exact_mod_cast h
      refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
      intro v hv
      have hvne : v ≠ 0 := by
        have hvpos : (0 : ℝ) < v := lt_of_lt_of_le (by norm_num) hv.1
        exact ne_of_gt hvpos
      exact mul_ne_zero hne hvne
  have harg2 : ∀ m₁ m₂ m₃ : ℤ, ContinuousOn
      (fun v : ℝ => Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v)) (Set.Icc (1 / 2 : ℝ) 2) := by
    intro m₁ m₂ m₃
    refine hc.comp_continuousOn ?_
    by_cases h : m₂ = 0
    · subst h
      have hconst : arg2 m₁ 0 m₃ = fun _ : ℝ => 0 := by funext v; simp [arg2]
      rw [hconst]; exact continuousOn_const
    · have hne : (m₂ : ℝ) ≠ 0 := by exact_mod_cast h
      refine ContinuousOn.div (by fun_prop) continuousOn_const ?_
      intro v hv
      exact hne
  -- `‖R‖` is continuous on `[1/2,2]`.
  have hRcont : ContinuousOn (Rfun W) (Set.Icc (1 / 2 : ℝ) 2) := fun v hv =>
    (continuousAt_Rfun W (by
      have hvpos : (0 : ℝ) < v := lt_of_lt_of_le (by norm_num) hv.1
      exact ne_of_gt hvpos)).continuousWithinAt
  have hRnorm : ContinuousOn (fun v : ℝ => ‖Rfun W v‖) (Set.Icc (1 / 2 : ℝ) 2) := hRcont.norm
  -- each summand is interval-integrable on `[1/2,2]`.
  have hInt : ∀ m₁ m₂ m₃ : ℤ, IntervalIntegrable
      (fun v : ℝ => ‖Rfun W v‖ * Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v) *
        Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v)) volume (1 / 2 : ℝ) 2 := by
    intro m₁ m₂ m₃
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) / 2 ≤ 2)]
    exact (hRnorm.mul (harg1 m₁ m₂ m₃)).mul (harg2 m₁ m₂ m₃)
  -- `Gsumg` in the shape of a single sum over the product index set.
  have hGsum_prod : ∀ v : ℝ, Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v =
      ∑ p ∈ (idx1 M₁).product ((idxM M₂).product (idxM M₃)),
        Rtilde W N B ψ₁ ψ₂ (arg1 p.1 p.2.1 p.2.2 v) *
          Rtilde W N B ψ₁ ψ₂ (arg2 p.1 p.2.1 p.2.2 v) := by
    intro v
    unfold Gsumg
    exact (S30g_sum_prod_eq_nested3 (idx1 M₁) (idxM M₂) (idxM M₃)
      (fun m₁ m₂ m₃ => Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v) *
        Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v))).symm
  -- interchange the finite `m`-sum with the integral.
  have hS30 : S30g N W B M₁ M₂ M₃ ψ₁ ψ₂ =
      ∫ v in (1 / 2 : ℝ)..2, ‖Rfun W v‖ * Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v := by
    unfold S30g
    rw [← S30g_sum_prod_eq_nested3 (idx1 M₁) (idxM M₂) (idxM M₃)
      (fun m₁ m₂ m₃ => ∫ v in (1 / 2 : ℝ)..2, ‖Rfun W v‖ *
        Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v) *
          Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v))]
    rw [← intervalIntegral.integral_finsetSum
      (s := (idx1 M₁).product ((idxM M₂).product (idxM M₃)))
      (f := fun p : ℤ × ℤ × ℤ => fun v : ℝ => ‖Rfun W v‖ *
        Rtilde W N B ψ₁ ψ₂ (arg1 p.1 p.2.1 p.2.2 v) *
          Rtilde W N B ψ₁ ψ₂ (arg2 p.1 p.2.1 p.2.2 v))
      (fun p _ => hInt p.1 p.2.1 p.2.2)]
    refine intervalIntegral.integral_congr fun v _ => ?_
    rw [hGsum_prod v, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  -- `Gsumg` is continuous and non-negative on `[1/2,2]`.
  have hGs : ContinuousOn (fun v : ℝ => Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v)
      (Set.Icc (1 / 2 : ℝ) 2) := by
    unfold Gsumg
    refine continuousOn_finsetSum _ (fun m₁ _ => continuousOn_finsetSum _ (fun m₂ _ =>
      continuousOn_finsetSum _ (fun m₃ _ => ?_)))
    exact (harg1 m₁ m₂ m₃).mul (harg2 m₁ m₂ m₃)
  have hf0 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 0 ≤ ‖Rfun W x‖ := fun x _ => norm_nonneg _
  have hg0 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 0 ≤ Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ x := by
    intro x _
    unfold Gsumg
    exact Finset.sum_nonneg fun m₁ _ => Finset.sum_nonneg fun m₂ _ =>
      Finset.sum_nonneg fun m₃ _ =>
        mul_nonneg (Rtilde_nonneg W N B ψ₁ ψ₂ _) (Rtilde_nonneg W N B ψ₁ ψ₂ _)
  -- Cauchy–Schwarz for the interval integral.
  calc S30g N W B M₁ M₂ M₃ ψ₁ ψ₂
      = ∫ v in (1 / 2 : ℝ)..2, ‖Rfun W v‖ * Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v := hS30
    _ ≤ Real.sqrt (∫ v in (1 / 2 : ℝ)..2, ‖Rfun W v‖ ^ 2) *
          Real.sqrt (∫ v in (1 / 2 : ℝ)..2, (Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v) ^ 2) :=
        integral_mul_le_sqrt_mul_sqrt (by norm_num) hRnorm hGs hf0 hg0
    _ = Real.sqrt (∫ v in (1 / 2 : ℝ)..2, ‖Rfun W v‖ ^ 2) *
          Real.sqrt (S32g N W B M₁ M₂ M₃ ψ₁ ψ₂) := rfl

end Work.GM.S3.Gen
