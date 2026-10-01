import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_zeroSet_box_finite
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Commons.NumberTheory.Linnik.zeroSum_invSq_bound
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Commons.Analysis.InfiniteSum.summable_of_finset_tail_bound
import Submission.Commons.Analysis.InfiniteSum.hasSum_tendsto_finset_sum

set_option autoImplicit false
set_option maxHeartbeats 0

open Complex DirichletCharacter Metric Filter MeromorphicOn Function Set
open scoped Real BigOperators Topology

namespace Commons.NumberTheory.DirichletCharacter

-- Please make sure this module imports Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
-- (or any module from that family) and NOT Submission.Commons.NumberTheory.Linnik.logDeriv_pf_identity or
-- Submission.Commons.NumberTheory.Linnik.stripSum_tendsto_of_ballSum_tendsto: the two families both define a
-- name `Commons.NumberTheory.Linnik.pfP` and therefore cannot be imported into the same file.
theorem divisorSum_summable_and_tendsto {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {Φ : ℂ → ℂ} {A : ℝ} (hA : 0 < A)
    (hΦ : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ → ‖Φ u‖ ≤ A / ‖u‖ ^ 2) :
    Summable (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u)
    ∧ Filter.Tendsto (fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then
        (((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) * Φ u) else 0))
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
  -- Step 4: the truncated sums converge
  let S : ℝ → Finset ℂ := fun T =>
    ((hballfin (max T 0 + 1) (by positivity)).toFinset).filter (fun u => |u.im| < T)
  have hSmem : ∀ (T : ℝ) (u : ℂ), u ∈ S T ↔ Λ u = 0 ∧ ‖u‖ ≤ max T 0 + 1 ∧ |u.im| < T := by
    intro T u
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, and_assoc]
  have hSfin : ∀ u : ℂ, f u ≠ 0 → ∀ᶠ T in Filter.atTop, u ∈ S T := by
    intro u hfu
    have hDne : D u ≠ 0 := by
      intro h0; exact hfu (by simp only [f, h0, Nat.cast_zero, zero_mul])
    have hΛu : Λ u = 0 := hΛzero u hDne
    refine eventually_atTop.mpr ⟨‖u‖ + 1, fun T hT => ?_⟩
    have hT0 : (0 : ℝ) < T := by linarith [norm_nonneg u]
    rw [hSmem]
    refine ⟨hΛu, ?_, ?_⟩
    · rw [max_eq_left (le_of_lt hT0)]; linarith
    · have h1 : |u.im| ≤ ‖u‖ := Complex.abs_im_le_norm u
      linarith
  have hfinsum_eq : ∀ T : ℝ,
      (∑ᶠ u : ℂ, (if |u.im| < T then f u else 0)) = ∑ u ∈ S T, f u := by
    intro T
    have hsupp : Function.support (fun u : ℂ => if |u.im| < T then f u else 0) ⊆
        ((S T : Finset ℂ) : Set ℂ) := by
      intro u hu
      rw [Function.mem_support] at hu
      have him : |u.im| < T := by
        by_contra h; exact hu (by rw [if_neg h])
      have hfu : f u ≠ 0 := by
        by_contra h; exact hu (by rw [if_pos him, h])
      have hDne : D u ≠ 0 := by
        intro h0; exact hfu (by simp only [f, h0, Nat.cast_zero, zero_mul])
      have hΛu : Λ u = 0 := hΛzero u hDne
      have hst := hstripΛ u hΛu
      have h1 : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
      have hre : |u.re| < 1 := by rw [abs_of_pos hst.1]; exact hst.2
      have hT0 : (0 : ℝ) < T := lt_of_le_of_lt (abs_nonneg _) him
      rw [Finset.mem_coe, hSmem]
      exact ⟨hΛu, by rw [max_eq_left (le_of_lt hT0)]; linarith, him⟩
    have h1 : (∑ᶠ u : ℂ, (if |u.im| < T then f u else 0)) =
        ∑ u ∈ S T, (if |u.im| < T then f u else 0) :=
      finsum_eq_sum_of_support_subset _ hsupp
    rw [h1]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [if_pos ((hSmem T u).mp hu).2.2]
  have hlim : Filter.Tendsto (fun T : ℝ => ∑ u ∈ S T, f u) Filter.atTop (nhds (∑' u : ℂ, f u)) :=
    Commons.Analysis.InfiniteSum.hasSum_tendsto_finset_sum hfsumm.hasSum hSfin
  have hlim2 : Filter.Tendsto (fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then f u else 0))
      Filter.atTop (nhds (∑' u : ℂ, f u)) :=
    Filter.Tendsto.congr (fun T => (hfinsum_eq T).symm) hlim
  -- Step 5: transfer the divisor to `analyticOrderNatAt`
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
  · have hcongr1 : (fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then
          (((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) * Φ u) else 0)) =
        fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then f u else 0) := by
      funext T
      refine finsum_congr (fun u => ?_)
      by_cases h : |u.im| < T
      · simp only [h, if_true, f, D, Λ]
      · simp only [h, if_false]
    have hcongr2 : (∑' u : ℂ,
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u)
        = ∑' u : ℂ, f u := by
      refine tsum_congr (fun u => ?_)
      have h := hdivuniv u
      rw [show MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ u
            = (analyticOrderNatAt Λ u : ℤ) from h]
      simp only [f, D, Int.cast_natCast]
    rw [hcongr1, hcongr2]
    exact hlim2

end Commons.NumberTheory.DirichletCharacter
