import Mathlib
import Submission.Work.ZeroFreeTables.P3.Imports
import Submission.Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric

set_option autoImplicit false
set_option maxHeartbeats 0

open Complex DirichletCharacter Metric Filter MeromorphicOn Function Set
open scoped Real BigOperators Topology

namespace Work.LinnikAreas.FarRepel

/-- **Summability of the divisor sum of `Λ(·,χ)` against an inverse-square weight, and convergence of its closed-ball partial sums.** (module `Submission.Work.LinnikAreas.FarRepel.divisorSumBallTendsto`; declare in `namespace Work.LinnikAreas.FarRepel`.)

Let `χ` be a non-principal primitive character mod `N`, `Λ = completedLFunction χ` (entire), and let `Φ` satisfy `‖Φ u‖ ≤ A/‖u‖²` for every `u` in the critical strip with `‖u‖ ≥ 2`. Then the global divisor sum `∑'_u (divisor Λ univ u) · Φ u` is summable, and its closed-ball partial sums converge to that sum (as `R → ∞`).

This conjugates `Commons.NumberTheory.DirichletCharacter.divisorSum_summable_and_tendsto` (first conjunct) with `Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero` (which is imported here).

PROOF ROUTE / IMPORT WARNING. This module must be importable together with the `Submission/Work/ZeroFreeTables/P3/...` family (it is imported alongside it), so it must NOT import `Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect` nor anything importing it (`Commons.NumberTheory.DirichletCharacter.divisorSum_summable_and_tendsto`, `Submission.Work.LinnikAreas.summable_zeroMult_norm_mul`, ...): that family re-declares `Commons.NumberTheory.Linnik.pfP`, which clashes with the P3 family (`logDeriv_pf_identity`), so the two cannot be imported together. Hence the summability half has to be re-proved here, adapting the proof of `Commons.NumberTheory.DirichletCharacter.divisorSum_summable_and_tendsto` (which you may READ for the argument, but must not import): it uses only the P3-family inputs `Commons.NumberTheory.Linnik.completedL_zero_strip`, `Commons.NumberTheory.Linnik.completedL_zeroCount`, `Commons.NumberTheory.Linnik.zeroSum_invSq_bound`, `Commons.NumberTheory.Linnik.grg_zeroSet_finite` (`Submission.Commons.NumberTheory.Linnik.goodRadius_geometric`), together with the neutral `Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast`, `Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound` and Mathlib. The second conjunct then follows from the first by `Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero` applied to `MeromorphicOn (completedLFunction χ) Set.univ` (from `DirichletCharacter.differentiable_completedLFunction hχ`). -/
theorem divisorSumBallTendsto {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {Φ : ℂ → ℂ} {A : ℝ} (hA : 0 < A)
    (hΦ : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ → ‖Φ u‖ ≤ A / ‖u‖ ^ 2) :
    Summable (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u)
      ∧ Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u)
        Filter.atTop (nhds (∑' u : ℂ,
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u)) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛdiff : Differentiable ℂ Λ := by
    simpa [Λ] using DirichletCharacter.differentiable_completedLFunction hχ
  have hΛan : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := fun U z _ => hΛdiff.analyticAt z
  have hdivuniv : ∀ u : ℂ, MeromorphicOn.divisor Λ Set.univ u = (analyticOrderNatAt Λ u : ℤ) :=
    fun u => Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hΛan Set.univ) (Set.mem_univ u)
  have hΛzero : ∀ u : ℂ, analyticOrderNatAt Λ u ≠ 0 → Λ u = 0 := fun u h =>
    apply_eq_zero_of_analyticOrderNatAt_ne_zero h
  have hstripΛ : ∀ u : ℂ, Λ u = 0 → 0 < u.re ∧ u.re < 1 := fun u h =>
    Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim (by simpa [Λ] using h)
  have hballfin : ∀ B : ℝ, 0 ≤ B → ({u : ℂ | Λ u = 0 ∧ ‖u‖ ≤ B} : Set ℂ).Finite := fun B hB =>
    by simpa [Λ] using Commons.NumberTheory.Linnik.grg_zeroSet_finite χ hχ hχprim (B := B) hB
  let D : ℂ → ℕ := fun u => analyticOrderNatAt Λ u
  let f : ℂ → ℂ := fun u => (D u : ℂ) * Φ u
  let F : ℂ → ℝ := fun u => (D u : ℝ) * (if 2 ≤ ‖u‖ then A / ‖u‖ ^ 2 else ‖Φ u‖)
  have hFnn : ∀ u : ℂ, 0 ≤ F u := by
    intro u
    by_cases h : 2 ≤ ‖u‖
    · simp only [F, h, if_true]; positivity
    · simp only [F, h, if_false]; positivity
  -- the inverse-square kernel bound, uniform in the radius
  obtain ⟨Cz, hCzpos, hCzkern⟩ := Commons.NumberTheory.Linnik.zeroSum_invSq_bound χ hχ hχprim
  -- Step 1: the tail bound for `F` over finite sets of large norm
  have htailF : ∀ t : Finset ℂ, (∀ u ∈ t, 2 < ‖u‖) →
      ∑ u ∈ t, F u ≤ 2 * A * Cz * (Real.log (N : ℝ) + Real.log 2 + 2) := by
    intro t ht
    set R : ℝ := 2 + ∑ u ∈ t, ‖u‖ with hRdef
    have hsum_nn : 0 ≤ ∑ u ∈ t, ‖u‖ := Finset.sum_nonneg (fun u _ => norm_nonneg u)
    have hRn : ∀ u ∈ t, ‖u‖ ≤ R := by
      intro u hu
      have h1 : ‖u‖ ≤ ∑ v ∈ t, ‖v‖ := Finset.single_le_sum (fun v _ => norm_nonneg v) hu
      rw [hRdef]; linarith
    have hdiv : ∀ u ∈ t, MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) R) u = (D u : ℤ) := by
      intro u hu
      exact Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hΛan _)
        (by rw [Metric.mem_closedBall, dist_zero_right]; exact hRn u hu)
    have hperterm : ∀ u ∈ t, F u ≤ 2 * A * ((D u : ℝ) / (1 + ‖u‖ ^ 2)) := by
      intro u hu
      have hu2 : (2 : ℝ) ≤ ‖u‖ := le_of_lt (ht u hu)
      have hF : F u = (D u : ℝ) * (A / ‖u‖ ^ 2) := by simp only [F, hu2, if_true]
      have hden1 : (0 : ℝ) < 1 + ‖u‖ ^ 2 := by positivity
      have hden2 : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
      have h14 : (1 : ℝ) ≤ ‖u‖ ^ 2 := by nlinarith [ht u hu, norm_nonneg u]
      have hcmp : (1 : ℝ) / ‖u‖ ^ 2 ≤ 2 / (1 + ‖u‖ ^ 2) := by
        rw [div_le_div_iff₀ hden2 hden1]
        nlinarith
      calc F u = A * ((D u : ℝ) * (1 / ‖u‖ ^ 2)) := by
              rw [hF]; ring
        _ ≤ A * ((D u : ℝ) * (2 / (1 + ‖u‖ ^ 2))) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hcmp (Nat.cast_nonneg _)) (le_of_lt hA)
        _ = 2 * A * ((D u : ℝ) / (1 + ‖u‖ ^ 2)) := by ring
    have hkern : ∑ u ∈ t, (D u : ℝ) / (1 + ‖u‖ ^ 2) ≤ Cz * (Real.log (N : ℝ) + Real.log 2 + 2) := by
      let g : ℂ → ℝ := fun u =>
        |(((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) R)) u : ℤ) : ℝ)| * (1 / (1 + ‖u‖ ^ 2))
      have hgnn : ∀ u : ℂ, 0 ≤ g u := fun u => by
        simp only [g]; positivity
      have hSfin : (Function.support
          (fun u : ℂ => MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) R) u)).Finite :=
        MeromorphicOn.divisor_support_finite_of_subset (f := Λ) (U := Metric.closedBall (0 : ℂ) R)
          (V := Metric.closedBall (0 : ℂ) R) (hΛan _).meromorphicOn
          (isCompact_closedBall (0 : ℂ) R) (Set.Subset.refl _)
      have hgsupp : Function.support g ⊆ ((hSfin.toFinset : Finset ℂ) : Set ℂ) := by
        intro u hu
        rw [Function.mem_support] at hu
        rw [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support]
        intro h0
        exact hu (by simp only [g, h0, Int.cast_zero, abs_zero, zero_mul])
      have hterm : ∀ u ∈ t, (D u : ℝ) / (1 + ‖u‖ ^ 2) = g u := by
        intro u hu
        simp only [g]
        rw [hdiv u hu, abs_of_nonneg (Nat.cast_nonneg (D u))]
        push_cast
        ring
      calc ∑ u ∈ t, (D u : ℝ) / (1 + ‖u‖ ^ 2)
          = ∑ u ∈ t, g u := Finset.sum_congr rfl hterm
        _ ≤ ∑ u ∈ t ∪ hSfin.toFinset, g u :=
              Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
                (fun i _ _ => hgnn i)
        _ = ∑ u ∈ hSfin.toFinset, g u := by
              refine (Finset.sum_subset (s₁ := hSfin.toFinset) (s₂ := t ∪ hSfin.toFinset)
                Finset.subset_union_right ?_).symm
              intro x hx hxn
              by_contra hgx
              exact hxn (hgsupp (by rwa [Function.mem_support]))
        _ = ∑ᶠ u : ℂ, g u := (finsum_eq_sum_of_support_subset g hgsupp).symm
        _ ≤ Cz * (Real.log (N : ℝ) + Real.log 2 + 2) := by
              have h := hCzkern (0 : ℂ) R
              simp only [g, Λ, norm_zero, zero_sub, norm_neg, add_zero] at h ⊢
              exact h
    calc ∑ u ∈ t, F u ≤ ∑ u ∈ t, 2 * A * ((D u : ℝ) / (1 + ‖u‖ ^ 2)) :=
          Finset.sum_le_sum hperterm
      _ = 2 * A * ∑ u ∈ t, (D u : ℝ) / (1 + ‖u‖ ^ 2) := by rw [Finset.mul_sum]
      _ ≤ 2 * A * (Cz * (Real.log (N : ℝ) + Real.log 2 + 2)) :=
          mul_le_mul_of_nonneg_left hkern (by positivity)
      _ = 2 * A * Cz * (Real.log (N : ℝ) + Real.log 2 + 2) := by ring
  -- Step 2: the small-norm part is bounded because only zeros with `‖u‖ ≤ 2` matter
  have hsmallF : ∃ c : ℝ, ∀ s : Finset ℂ, (∀ u ∈ s, ‖u‖ ≤ 2) → ∑ u ∈ s, F u ≤ c := by
    refine ⟨∑ u ∈ (hballfin 2 (by norm_num)).toFinset, F u, ?_⟩
    intro s hs
    set Z : Finset ℂ := (hballfin 2 (by norm_num)).toFinset with hZdef
    have hZmem : ∀ u : ℂ, u ∈ Z ↔ Λ u = 0 ∧ ‖u‖ ≤ 2 := by
      intro u; simp only [hZdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    have hzero : ∀ u ∈ s ∪ Z, u ∉ Z → F u = 0 := by
      intro u hu huz
      by_contra hFu
      have hDne : D u ≠ 0 := by
        intro hD0
        exact hFu (by simp only [F, hD0, Nat.cast_zero, zero_mul])
      have hzerou : Λ u = 0 := hΛzero u hDne
      have hu_s : u ∈ s := by
        rcases Finset.mem_union.mp hu with h | h
        · exact h
        · exact absurd h huz
      exact huz ((hZmem u).mpr ⟨hzerou, hs u hu_s⟩)
    calc ∑ u ∈ s, F u ≤ ∑ u ∈ s ∪ Z, F u :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun i _ _ => hFnn i)
      _ = ∑ u ∈ Z, F u := (Finset.sum_subset (s₁ := Z) (s₂ := s ∪ Z)
            Finset.subset_union_right hzero).symm
  have hFsumm : Summable F :=
    Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound hFnn hsmallF htailF
  -- Step 3: dominate `f` by `F`
  have hdom : ∀ u : ℂ, ‖f u‖ ≤ F u := by
    intro u
    by_cases hD0 : D u = 0
    · simp only [f, hD0, Nat.cast_zero, zero_mul, norm_zero]
      exact hFnn u
    · have hΛu : Λ u = 0 := hΛzero u hD0
      have hst := hstripΛ u hΛu
      have hnorm : ‖f u‖ = (D u : ℝ) * ‖Φ u‖ := by
        simp only [f, norm_mul, Complex.norm_natCast]
      rw [hnorm]
      by_cases h2 : 2 ≤ ‖u‖
      · rw [show F u = (D u : ℝ) * (A / ‖u‖ ^ 2) by simp only [F, h2, if_true]]
        exact mul_le_mul_of_nonneg_left (hΦ u hst.1 hst.2 h2) (Nat.cast_nonneg _)
      · rw [show F u = (D u : ℝ) * ‖Φ u‖ by simp only [F, h2, if_false]]
  have hfsumm : Summable f := Summable.of_norm_bounded hFsumm hdom
  refine ⟨?_, ?_⟩
  · have hcongr : (fun u : ℂ =>
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u) = f := by
      funext u
      have h := hdivuniv u
      rw [show MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u
            = (analyticOrderNatAt Λ u : ℤ) from h]
      simp only [f, D, Int.cast_natCast]
    rw [hcongr]
    exact hfsumm
  · have hsumm : Summable (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u) := by
      have hcongr : (fun u : ℂ =>
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u) = f := by
        funext u
        have h := hdivuniv u
        rw [show MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u
              = (analyticOrderNatAt Λ u : ℤ) from h]
        simp only [f, D, Int.cast_natCast]
      rw [hcongr]
      exact hfsumm
    exact Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
      (f := DirichletCharacter.completedLFunction χ) (hΛan Set.univ).meromorphicOn hsumm

end Work.LinnikAreas.FarRepel
