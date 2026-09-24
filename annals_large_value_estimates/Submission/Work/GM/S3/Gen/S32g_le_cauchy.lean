import Mathlib
import Submission.Work.GM.S3.gen_defs
import Submission.Work.GM.S3.S32_le_cauchy

namespace Work.GM.S3.Gen

open Complex Finset MeasureTheory
open scoped BigOperators

open Submission.GM (Rfun)

/-- Flattening of a triple sum into a sum over the product index set `s₁ × (s₂ × s₃)`.
(Stated in this direction, i.e. product first, because it is the exact conclusion of
`Finset.sum_product` applied twice.)  Same as `Work.GM.S3.cauchyS32_sum_prod3`, but with the
second and third index sets independent (needed for the three-scale objects). -/
lemma cauchyS32g_sum_prod3 (s₁ s₂ s₃ : Finset ℤ) (F : ℤ → ℤ → ℤ → ℝ) :
    ∑ p ∈ s₁.product (s₂.product s₃), F p.1 p.2.1 p.2.2
      = ∑ m₁ ∈ s₁, ∑ m₂ ∈ s₂, ∑ m₃ ∈ s₃, F m₁ m₂ m₃ := by
  calc ∑ p ∈ s₁.product (s₂.product s₃), F p.1 p.2.1 p.2.2
      = ∑ m₁ ∈ s₁, ∑ p ∈ s₂.product s₃, F m₁ p.1 p.2 :=
        Finset.sum_product s₁ (s₂.product s₃) (fun x : ℤ × (ℤ × ℤ) => F x.1 x.2.1 x.2.2)
    _ = ∑ m₁ ∈ s₁, ∑ m₂ ∈ s₂, ∑ m₃ ∈ s₃, F m₁ m₂ m₃ :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_product s₂ s₃ (fun x : ℤ × ℤ => F a x.1 x.2))

/-- Cauchy–Schwarz for a triple sum over three independent index sets:
`(Σ a·b)² ≤ (Σ a²)(Σ b²)` (no sign hypothesis on `a`, `b`). -/
lemma cauchyS32g_nested_cs (s₁ s₂ s₃ : Finset ℤ) (a b : ℤ → ℤ → ℤ → ℝ) :
    (∑ m₁ ∈ s₁, ∑ m₂ ∈ s₂, ∑ m₃ ∈ s₃, a m₁ m₂ m₃ * b m₁ m₂ m₃)^2 ≤
      (∑ m₁ ∈ s₁, ∑ m₂ ∈ s₂, ∑ m₃ ∈ s₃, a m₁ m₂ m₃^2) *
      (∑ m₁ ∈ s₁, ∑ m₂ ∈ s₂, ∑ m₃ ∈ s₃, b m₁ m₂ m₃^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s₁.product (s₂.product s₃))
    (fun p : ℤ × ℤ × ℤ => a p.1 p.2.1 p.2.2) (fun p : ℤ × ℤ × ℤ => b p.1 p.2.1 p.2.2)
  rw [cauchyS32g_sum_prod3 s₁ s₂ s₃ (fun m₁ m₂ m₃ => a m₁ m₂ m₃ * b m₁ m₂ m₃),
      cauchyS32g_sum_prod3 s₁ s₂ s₃ (fun m₁ m₂ m₃ => a m₁ m₂ m₃^2),
      cauchyS32g_sum_prod3 s₁ s₂ s₃ (fun m₁ m₂ m₃ => b m₁ m₂ m₃^2)] at h
  exact h

/-- **GM 10.1, second Cauchy–Schwarz step, three independent dyadic scales.**
With `G(v) = Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v` and `A(v) = Asumg … v`, `B(v) = Bsumg … v`
(every summand is non-negative, so `A, B ≥ 0`),

`S₃,₂ = ∫_{1/2}^2 G² ≤ (S₃,₃)^{1/2} (S₃,₄)^{1/2}`,  `S₃,₃ = ∫ A²`, `S₃,₄ = ∫ B²`.

Proof: Cauchy–Schwarz in the finite index `ℤ³` gives `G v ^ 2 ≤ A v * B v` pointwise, and then
`∫ G² ≤ ∫ A·B ≤ (∫A²)^{1/2}(∫B²)^{1/2}` by Cauchy–Schwarz for integrals
(`Work.GM.S3.integral_mul_le_sqrt_mul_sqrt`, proved in this workspace).  Everything is continuous
(finite sums of products of compositions of the continuous `x ↦ Rtilde W N B ψ₁ ψ₂ x`, cf.
`RtildeSq_continuous`). -/
theorem S32g_le_cauchy (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hψ₁ : Work.GM.S3.IsBumpAtZero ψ₁ 16) (hψ₂ : Work.GM.S3.IsBumpAtOne ψ₂ 16)
    (hB : 0 ≤ (N : ℝ) * B) :
    Work.GM.S3.Gen.S32g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤
      Real.sqrt (Work.GM.S3.Gen.S33g N W B M₁ M₂ M₃ ψ₁ ψ₂) *
        Real.sqrt (Work.GM.S3.Gen.S34g N W B M₁ M₂ M₃ ψ₁ ψ₂) := by
  -- `Rtilde` is continuous, being `√(RtildeSq)`.
  have hc : Continuous (fun u => Rtilde W N B ψ₁ ψ₂ u) := by
    have h := (Work.GM.S3.RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂).sqrt
    simpa only [Rtilde, RtildeSq] using h
  -- On `[1/2,2]` both arguments `a₁`, `a₂` of `Rtilde` are continuous (`v` stays away from `0`).
  have harg1 : ∀ m₁ m₂ m₃ : ℤ, ContinuousOn
      (fun v : ℝ => Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v)) (Set.Icc (1/2) 2) := by
    intro m₁ m₂ m₃
    refine hc.comp_continuousOn ?_
    by_cases h : m₂ = 0
    · subst h
      have hconst : arg1 m₁ 0 m₃ = fun _ : ℝ => 0 := by
        funext v; simp [arg1]
      rw [hconst]; exact continuousOn_const
    · have hne : (m₂ : ℝ) ≠ 0 := by exact_mod_cast h
      have hnum : ContinuousOn (fun v : ℝ => (m₁ : ℝ) * v + (m₃ : ℝ)) (Set.Icc (1/2) 2) := by
        fun_prop
      have hden : ContinuousOn (fun v : ℝ => (m₂ : ℝ) * v) (Set.Icc (1/2) 2) := by
        fun_prop
      refine ContinuousOn.div hnum hden ?_
      intro v hv
      have hvne : v ≠ 0 := by
        have : (0:ℝ) < v := lt_of_lt_of_le (by norm_num) hv.1
        exact ne_of_gt this
      exact mul_ne_zero hne hvne
  have harg2 : ∀ m₁ m₂ m₃ : ℤ, ContinuousOn
      (fun v : ℝ => Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v)) (Set.Icc (1/2) 2) := by
    intro m₁ m₂ m₃
    refine hc.comp_continuousOn ?_
    by_cases h : m₂ = 0
    · subst h
      have hconst : arg2 m₁ 0 m₃ = fun _ : ℝ => 0 := by
        funext v; simp [arg2]
      rw [hconst]; exact continuousOn_const
    · have hne : (m₂ : ℝ) ≠ 0 := by exact_mod_cast h
      have hnum : ContinuousOn (fun v : ℝ => (m₁ : ℝ) * v + (m₃ : ℝ)) (Set.Icc (1/2) 2) := by
        fun_prop
      refine ContinuousOn.div hnum continuousOn_const ?_
      intro v hv
      exact hne
  have hGs : ContinuousOn (fun v => Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v) (Set.Icc (1/2) 2) := by
    unfold Gsumg
    refine continuousOn_finsetSum _ (fun m₁ _ =>
      continuousOn_finsetSum _ (fun m₂ _ => continuousOn_finsetSum _ (fun m₃ _ => ?_)))
    exact (harg1 m₁ m₂ m₃).mul (harg2 m₁ m₂ m₃)
  have hAs : ContinuousOn (fun v => Asumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v) (Set.Icc (1/2) 2) := by
    unfold Asumg
    refine continuousOn_finsetSum _ (fun m₁ _ =>
      continuousOn_finsetSum _ (fun m₂ _ => continuousOn_finsetSum _ (fun m₃ _ => ?_)))
    exact (harg1 m₁ m₂ m₃).pow 2
  have hBs : ContinuousOn (fun v => Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v) (Set.Icc (1/2) 2) := by
    unfold Bsumg
    refine continuousOn_finsetSum _ (fun m₁ _ =>
      continuousOn_finsetSum _ (fun m₂ _ => continuousOn_finsetSum _ (fun m₃ _ => ?_)))
    exact (harg2 m₁ m₂ m₃).pow 2
  -- Pointwise Cauchy–Schwarz in the index `(m₁,m₂,m₃)`.
  have hpt : ∀ v : ℝ, (Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v)^2 ≤
      Asumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v * Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v := by
    intro v
    have h := cauchyS32g_nested_cs (idx1 M₁) (idxM M₂) (idxM M₃)
      (fun m₁ m₂ m₃ => Rtilde W N B ψ₁ ψ₂ (arg1 m₁ m₂ m₃ v))
      (fun m₁ m₂ m₃ => Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v))
    simpa only [Gsumg, Asumg, Bsumg] using h
  have hA0 : ∀ x ∈ Set.Icc (1/2:ℝ) 2, 0 ≤ Asumg N W B M₁ M₂ M₃ ψ₁ ψ₂ x := by
    intro x _
    unfold Asumg
    exact Finset.sum_nonneg (fun m₁ _ =>
      Finset.sum_nonneg (fun m₂ _ => Finset.sum_nonneg (fun m₃ _ => sq_nonneg _)))
  have hB0 : ∀ x ∈ Set.Icc (1/2:ℝ) 2, 0 ≤ Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ x := by
    intro x _
    unfold Bsumg
    exact Finset.sum_nonneg (fun m₁ _ =>
      Finset.sum_nonneg (fun m₂ _ => Finset.sum_nonneg (fun m₃ _ => sq_nonneg _)))
  -- Integrability on `[1/2,2]` (from continuity).
  have hGu : ContinuousOn (fun v => Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v) (Set.uIcc (1/2:ℝ) 2) := by
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)]; exact hGs
  have hAu : ContinuousOn (fun v => Asumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v) (Set.uIcc (1/2:ℝ) 2) := by
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)]; exact hAs
  have hBu : ContinuousOn (fun v => Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v) (Set.uIcc (1/2:ℝ) 2) := by
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)]; exact hBs
  have hIntG : IntervalIntegrable (fun v => (Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v)^2) volume (1/2:ℝ) 2 :=
    (hGu.pow 2).intervalIntegrable
  have hIntAB : IntervalIntegrable
      (fun v => Asumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v * Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v)
      volume (1/2:ℝ) 2 :=
    (hAu.mul hBu).intervalIntegrable
  have hmono : ∫ v in (1/2:ℝ)..2, (Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v)^2 ≤
      ∫ v in (1/2:ℝ)..2, Asumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v * Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v :=
    intervalIntegral.integral_mono_on (by norm_num) hIntG hIntAB (fun x _ => hpt x)
  have hCS := Work.GM.S3.integral_mul_le_sqrt_mul_sqrt (a := (1/2:ℝ)) (b := 2) (by norm_num)
    hAs hBs hA0 hB0
  calc S32g N W B M₁ M₂ M₃ ψ₁ ψ₂
      = ∫ v in (1/2:ℝ)..2, (Gsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v)^2 := rfl
    _ ≤ ∫ v in (1/2:ℝ)..2, Asumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v * Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v := hmono
    _ ≤ Real.sqrt (∫ v in (1/2:ℝ)..2, (Asumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v)^2) *
        Real.sqrt (∫ v in (1/2:ℝ)..2, (Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v)^2) := hCS
    _ = Real.sqrt (S33g N W B M₁ M₂ M₃ ψ₁ ψ₂) *
        Real.sqrt (S34g N W B M₁ M₂ M₃ ψ₁ ψ₂) := rfl

end Work.GM.S3.Gen
