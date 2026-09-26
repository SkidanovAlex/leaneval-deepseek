import Mathlib
import Submission.Work.Core.Basic

namespace Work.Sampling

open LeanEval.Analysis.CKMRVInterpolation
open Filter
open scoped Topology

/-- On `Set.Ici k₀`, the cofinite filter is coarser than `atTop`: every `atTop`-set is
cofinite, because the complement of a tail is finite. -/
lemma cofinite_le_atTop_Ici (k₀ : ℕ) :
    (Filter.cofinite : Filter (Set.Ici k₀)) ≤ Filter.atTop := by
  rw [Filter.le_def]
  intro s hs
  rw [Filter.mem_atTop_sets] at hs
  obtain ⟨M, hM⟩ := hs
  rw [Filter.mem_cofinite]
  have hfin : ({x : Set.Ici k₀ | x < M}).Finite := by
    refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    refine (Set.finite_Iio M.1).subset ?_
    rintro y ⟨x, hx, rfl⟩
    simpa using hx
  refine hfin.subset fun x hx => ?_
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢
  by_contra h
  push Not at h
  exact hx (hM x h)

theorem summable_norm_mul_pow (k₀ N : ℕ) (a : Set.Ici k₀ → ℂ)
    (ha : RapidlyDecreasing a) :
    Summable fun k : Set.Ici k₀ => ‖a k‖ * (((k : ℕ) : ℝ) + 1) ^ N := by
  have hg : Summable (fun k : Set.Ici k₀ => 1 / (((k : ℕ) : ℝ) + 1) ^ 2) := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr h1
      simpa using h
    exact h2.comp_injective Subtype.val_injective
  have hc : Tendsto (fun k : Set.Ici k₀ => (((k : ℕ) : ℝ) + 1) ^ (N + 2) * ‖a k‖)
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun k : Set.Ici k₀ =>
        ∑ i ∈ Finset.range ((N + 2) + 1),
          ((N + 2).choose i : ℝ) * (((k : ℕ) : ℝ) ^ i * ‖a k‖)) atTop (𝓝 0) := by
      have h := tendsto_finsetSum (Finset.range ((N + 2) + 1))
        (f := fun i => fun k : Set.Ici k₀ =>
          ((N + 2).choose i : ℝ) * (((k : ℕ) : ℝ) ^ i * ‖a k‖))
        (a := fun _ : ℕ => (0 : ℝ))
        (fun i _ => by simpa using (ha i).const_mul ((N + 2).choose i : ℝ))
      simpa using h
    refine hsum.congr fun k => ?_
    rw [add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp
    ring
  have hc_ev : ∀ᶠ k : Set.Ici k₀ in atTop, (((k : ℕ) : ℝ) + 1) ^ (N + 2) * ‖a k‖ ≤ 1 :=
    hc.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hle : ∀ᶠ k : Set.Ici k₀ in atTop,
      ‖‖a k‖ * (((k : ℕ) : ℝ) + 1) ^ N‖ ≤ 1 / (((k : ℕ) : ℝ) + 1) ^ 2 := by
    refine hc_ev.mono fun k hk => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    rw [le_div_iff₀ (by positivity)]
    calc ‖a k‖ * (((k : ℕ) : ℝ) + 1) ^ N * (((k : ℕ) : ℝ) + 1) ^ 2
        = (((k : ℕ) : ℝ) + 1) ^ (N + 2) * ‖a k‖ := by
          rw [mul_assoc, ← pow_add, mul_comm]
      _ ≤ 1 := hk
  exact Summable.of_norm_bounded_eventually hg
    (Filter.Eventually.filter_mono (cofinite_le_atTop_Ici k₀) hle)

end Work.Sampling
