import Mathlib

/-!
# Uniform bounds on the derivatives of a smooth cutoff product

For every order `J` there is a single constant `C ≥ 0` bounding the `m`-th derivative
(`m ≤ J`) of the compactly supported cutoff

  `s ↦ (Real.smoothTransition (s + 1) * Real.smoothTransition (T + 2 - s) : ℂ)`

uniformly in the shift parameter `T` and the point `s`.

The proof has two ingredients.

* A bound for the complexified `Real.smoothTransition` itself: its `m`-th derivative
  (`m ≥ 1`) vanishes off `[0, 1]` and is continuous, hence bounded; the order `0` term is
  bounded by `1` (as `0 ≤ smoothTransition ≤ 1`).  A finite supremum over `m ≤ J` gives one
  constant.
* Leibniz' rule for iterated derivatives of a product (`iteratedDeriv_mul`), together with
  the translation/reflection invariance of iterated derivatives
  (`iteratedDeriv_comp_add_const`, `iteratedDeriv_comp_const_sub`), which shows that each of
  the two factors has iterated derivatives of every order `≤ J` bounded by the very same
  constant.
-/

namespace Work.Radial

open scoped ContDiff Topology
open Filter

/-- The complexified smooth transition function is smooth up to any finite order. -/
lemma smoothTransition_cast_contDiff_infty :
    ContDiff ℝ ∞ (fun y : ℝ => (Real.smoothTransition y : ℂ)) :=
  (Complex.ofRealCLM.contDiff (n := ∞)).comp (Real.smoothTransition.contDiff (n := ⊤))

/-- All iterated derivatives of order `≤ J` of the complexified `smoothTransition`
are bounded by a single nonnegative constant. -/
lemma smoothTransition_cast_iteratedDeriv_bound (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, m ≤ J → ∀ t : ℝ,
      ‖iteratedDeriv m (fun y : ℝ => (Real.smoothTransition y : ℂ)) t‖ ≤ C := by
  have hψsm := smoothTransition_cast_contDiff_infty
  -- The `m`-th derivative, `m ≥ 1`, vanishes off the interval `[0, 1]`.
  have hzero : ∀ m : ℕ, 1 ≤ m → ∀ x : ℝ, x ∉ Set.Icc (0 : ℝ) 1 →
      iteratedDeriv m (fun y : ℝ => (Real.smoothTransition y : ℂ)) x = 0 := by
    intro m hm x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · -- `x < 0`: the function is identically `0` near `x`.
      have hev : (fun y : ℝ => (Real.smoothTransition y : ℂ)) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
        filter_upwards [Metric.ball_mem_nhds x (by linarith : (0 : ℝ) < -x)] with y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have hy' : y < 0 := by have := abs_lt.mp hy; linarith [this.2]
        exact_mod_cast Real.smoothTransition.zero_of_nonpos hy'.le
      rw [Filter.EventuallyEq.iteratedDeriv_eq m hev, iteratedDeriv_const]
      simp [show m ≠ 0 by omega]
    · -- `1 < x`: the function is identically `1` near `x`.
      have hev : (fun y : ℝ => (Real.smoothTransition y : ℂ)) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
        filter_upwards [Metric.ball_mem_nhds x (by linarith : (0 : ℝ) < x - 1)] with y hy
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have hy' : 1 < y := by have := abs_lt.mp hy; linarith [this.1]
        exact_mod_cast Real.smoothTransition.one_of_one_le hy'.le
      rw [Filter.EventuallyEq.iteratedDeriv_eq m hev, iteratedDeriv_const]
      simp [show m ≠ 0 by omega]
  have hle : ∀ m : ℕ, (m : ℕ∞ω) ≤ (∞ : ℕ∞ω) := fun m => by exact_mod_cast le_top
  -- A bound for every single order `m`.
  have hbound : ∀ m : ℕ, ∃ C : ℝ, ∀ t : ℝ,
      ‖iteratedDeriv m (fun y : ℝ => (Real.smoothTransition y : ℂ)) t‖ ≤ C := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hm
    · subst hm0
      refine ⟨1, fun t => ?_⟩
      rw [iteratedDeriv_zero]
      rw [show ‖((Real.smoothTransition t : ℝ) : ℂ)‖ = |Real.smoothTransition t| by simp,
        abs_of_nonneg (Real.smoothTransition.nonneg t)]
      exact Real.smoothTransition.le_one t
    · have hcs : HasCompactSupport
          (iteratedDeriv m (fun y : ℝ => (Real.smoothTransition y : ℂ))) :=
        HasCompactSupport.intro isCompact_Icc (hzero m hm)
      exact hcs.exists_bound_of_continuous
        (ContDiff.continuous_iteratedDeriv m hψsm (hle m))
  let B : ℕ → ℝ := fun m => Classical.choose (hbound m)
  have hB : ∀ m : ℕ, ∀ t : ℝ,
      ‖iteratedDeriv m (fun y : ℝ => (Real.smoothTransition y : ℂ)) t‖ ≤ B m :=
    fun m => Classical.choose_spec (hbound m)
  refine ⟨∑ m ∈ Finset.range (J + 1), max (B m) 0, ?_, ?_⟩
  · exact Finset.sum_nonneg fun m _ => le_max_right _ _
  · intro m hm t
    have hmem : m ∈ Finset.range (J + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    calc ‖iteratedDeriv m (fun y : ℝ => (Real.smoothTransition y : ℂ)) t‖
        ≤ B m := hB m t
      _ ≤ max (B m) 0 := le_max_left _ _
      _ ≤ ∑ m' ∈ Finset.range (J + 1), max (B m') 0 :=
            Finset.single_le_sum (fun i _ => le_max_right _ _) hmem

theorem cutoff_deriv_bound (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (m : ℕ), m ≤ J → ∀ t : ℝ,
      ‖iteratedDeriv m
        (fun s : ℝ => ((Real.smoothTransition (s + 1) *
          Real.smoothTransition (T + 2 - s) : ℝ) : ℂ)) t‖ ≤ C := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := smoothTransition_cast_iteratedDeriv_bound J
  have hψsm := smoothTransition_cast_contDiff_infty
  refine ⟨∑ i ∈ Finset.range (J + 1), (J.choose i : ℝ) * Cψ * Cψ, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCψ0) hCψ0)
  · intro T m hm t
    -- Rewrite the cutoff as the product of the two complexified factors.
    have hfun : (fun s : ℝ => ((Real.smoothTransition (s + 1) *
          Real.smoothTransition (T + 2 - s) : ℝ) : ℂ))
        = (fun s : ℝ => (Real.smoothTransition (s + 1) : ℂ))
          * (fun s : ℝ => (Real.smoothTransition (T + 2 - s) : ℂ)) := by
      funext s
      exact Complex.ofReal_mul _ _
    rw [hfun]
    have hfsm : ContDiff ℝ ∞ (fun s : ℝ => (Real.smoothTransition (s + 1) : ℂ)) :=
      hψsm.comp (contDiff_id.add contDiff_const)
    have hgsm : ContDiff ℝ ∞ (fun s : ℝ => (Real.smoothTransition (T + 2 - s) : ℂ)) :=
      hψsm.comp (contDiff_const.sub contDiff_id)
    have hfd : ContDiffAt ℝ (↑m) (fun s : ℝ => (Real.smoothTransition (s + 1) : ℂ)) t :=
      (contDiff_infty.mp hfsm m).contDiffAt
    have hgd : ContDiffAt ℝ (↑m) (fun s : ℝ => (Real.smoothTransition (T + 2 - s) : ℂ)) t :=
      (contDiff_infty.mp hgsm m).contDiffAt
    rw [iteratedDeriv_mul hfd hgd]
    -- Bounds on the two factors, both by the same constant `Cψ`.
    have hA : ∀ i : ℕ, i ≤ m →
        ‖iteratedDeriv i (fun s : ℝ => (Real.smoothTransition (s + 1) : ℂ)) t‖ ≤ Cψ := by
      intro i hi
      have heq : iteratedDeriv i (fun s : ℝ => (Real.smoothTransition (s + 1) : ℂ)) t
          = iteratedDeriv i (fun y : ℝ => (Real.smoothTransition y : ℂ)) (t + 1) := by
        have h := congrFun (iteratedDeriv_comp_add_const i
          (fun y : ℝ => (Real.smoothTransition y : ℂ)) (1 : ℝ)) t
        simpa using h
      rw [heq]
      exact hCψ i (le_trans hi hm) (t + 1)
    have hBd : ∀ j : ℕ, j ≤ m →
        ‖iteratedDeriv j (fun s : ℝ => (Real.smoothTransition (T + 2 - s) : ℂ)) t‖ ≤ Cψ := by
      intro j hj
      have heq : iteratedDeriv j (fun s : ℝ => (Real.smoothTransition (T + 2 - s) : ℂ)) t
          = (-1 : ℝ) ^ j •
              iteratedDeriv j (fun y : ℝ => (Real.smoothTransition y : ℂ)) (T + 2 - t) := by
        have h := congrFun (iteratedDeriv_comp_const_sub j
          (fun y : ℝ => (Real.smoothTransition y : ℂ)) (T + 2)) t
        simpa using h
      rw [heq, norm_smul,
        show ‖(-1 : ℝ) ^ j‖ = 1 by rw [norm_pow, norm_neg, norm_one, one_pow], one_mul]
      exact hCψ j (le_trans hj hm) (T + 2 - t)
    -- Leibniz bound.
    calc ‖∑ i ∈ Finset.range (m + 1), (m.choose i : ℂ) *
            iteratedDeriv i (fun s : ℝ => (Real.smoothTransition (s + 1) : ℂ)) t *
            iteratedDeriv (m - i) (fun s : ℝ => (Real.smoothTransition (T + 2 - s) : ℂ)) t‖
        ≤ ∑ i ∈ Finset.range (m + 1), ‖(m.choose i : ℂ) *
            iteratedDeriv i (fun s : ℝ => (Real.smoothTransition (s + 1) : ℂ)) t *
            iteratedDeriv (m - i) (fun s : ℝ => (Real.smoothTransition (T + 2 - s) : ℂ)) t‖
          := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Cψ * Cψ := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rw [norm_mul, norm_mul, Complex.norm_natCast]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hA i hi') (Nat.cast_nonneg _))
            (hBd (m - i) (Nat.sub_le m i)) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hCψ0)
      _ ≤ ∑ i ∈ Finset.range (J + 1), (J.choose i : ℝ) * Cψ * Cψ := by
          calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Cψ * Cψ
              ≤ ∑ i ∈ Finset.range (m + 1), (J.choose i : ℝ) * Cψ * Cψ := by
                apply Finset.sum_le_sum
                intro i _
                have hch : (m.choose i : ℝ) ≤ (J.choose i : ℝ) := by
                  exact_mod_cast Nat.choose_le_choose i hm
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hch hCψ0) hCψ0
            _ ≤ ∑ i ∈ Finset.range (J + 1), (J.choose i : ℝ) * Cψ * Cψ :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hm))
                  (fun i _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCψ0) hCψ0)

end Work.Radial
