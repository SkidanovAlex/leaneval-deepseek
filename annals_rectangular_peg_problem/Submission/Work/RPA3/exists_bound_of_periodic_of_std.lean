import Mathlib

/-!
# A uniform bound for a periodic function that is constant for large `|x|`

Let `f : ℝ → ℝ → ℝ → V` take values in a normed additive commuative group `V` and suppose

* `f` is jointly continuous,
* `f τ x (t + 2π) = f τ x t` (periodicity in the third variable),
* `f τ x t = c` whenever `X0 < |x|` (the function is constant far out in the second variable).

Then the family `(τ, x, t) ↦ f τ x t` is uniformly bounded on the slab
`τ ∈ [-2, 3]` (and all `x`, `t`).

The proof is the usual one: on the compact box `[-2,3] × [-K,K] × [0,2π]` (where
`K = max X0 0 + 1`) joint continuity gives a bound, periodicity lets one reduce an
arbitrary period `t` to `[0, 2π]`, and outside the box in `x` the function equals `c`.
-/

set_option autoImplicit false

namespace Work.RPA3

/-- Reduction of a point of a `T`-periodic function to a fundamental interval:
if `g` is periodic of period `T > 0`, then for every `t` there is `t0 ∈ Icc 0 T`
with `g t = g t0`. -/
private lemma periodic_reduce {V : Type*} (g : ℝ → V)
    (hg : Function.Periodic g (2 * Real.pi)) (t : ℝ) :
    ∃ t0 ∈ Set.Icc (0 : ℝ) (2 * Real.pi), g t = g t0 := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨n, hn, -⟩ := (existsUnique_sub_zsmul_mem_Ico hp t 0)
  refine ⟨t - n • (2 * Real.pi), Set.Ico_subset_Icc_self (by simpa using hn), ?_⟩
  have ht : t = (t - n • (2 * Real.pi)) + n • (2 * Real.pi) := by abel
  conv_lhs => rw [ht]
  exact Function.Periodic.zsmul hg n (t - n • (2 * Real.pi))

theorem exists_bound_of_periodic_of_std (X0 : ℝ) {V : Type*} [NormedAddCommGroup V]
    (f : ℝ → ℝ → ℝ → V) (c : V)
    (hcont : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
    (hper : ∀ τ x t, f τ x (t + 2 * Real.pi) = f τ x t)
    (hstd : ∀ τ x t, X0 < |x| → f τ x t = c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (-2 : ℝ) 3, ∀ x t, ‖f τ x t‖ ≤ M := by
  -- The `x`-threshold beyond which `f` is constant.
  set K : ℝ := max X0 0 + 1 with hKdef
  have hKX0 : X0 < K := by
    rw [hKdef]
    exact lt_of_le_of_lt (le_max_left X0 0) (lt_add_one (max X0 0))
  -- Compactness of the box `[-2,3] × [-K,K] × [0,2π]`.
  have hcomp : IsCompact
      (Set.Icc (-2 : ℝ) 3 ×ˢ (Set.Icc (-K) K ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C ‖c‖, le_trans (norm_nonneg c) (le_max_right _ _), ?_⟩
  intro τ hτ x t
  by_cases hx : |x| ≤ K
  · -- Inside the box in `x`: reduce `t` to a fundamental period and use the compact bound.
    obtain ⟨t0, ht0, hft0⟩ := periodic_reduce (fun t => f τ x t) (fun t => hper τ x t) t
    have hxmem : x ∈ Set.Icc (-K) K := by
      simpa [Set.mem_Icc] using (abs_le.mp hx)
    have hmem : (τ, x, t0) ∈
        Set.Icc (-2 : ℝ) 3 ×ˢ (Set.Icc (-K) K ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
      ⟨hτ, hxmem, ht0⟩
    have hb := hC (τ, x, t0) hmem
    rw [hft0]
    exact le_trans hb (le_max_left _ _)
  · -- Outside the box in `x`: `f` is constantly `c`.
    have hxK : K < |x| := not_le.mp hx
    have hX0 : X0 < |x| := lt_of_lt_of_le hKX0 (le_of_lt hxK)
    rw [hstd τ x t hX0]
    exact le_max_right _ _

end Work.RPA3
