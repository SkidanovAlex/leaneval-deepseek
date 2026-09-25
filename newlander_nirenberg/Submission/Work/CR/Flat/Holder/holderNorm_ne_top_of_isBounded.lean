import Mathlib
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

/-- The elementary Hölder bound: if `h` is bounded by `C` at `x` and at `y` and is
`L`-Lipschitz on the pair `{x, y}`, then the divided difference of order `α ∈ [0,1]`
is bounded by `max L (2 C)`.  Small distances are handled by the Lipschitz bound
(`‖x - y‖ ^ (1 - α) ≤ 1`) and large ones by the sup bound (`‖x - y‖ ^ (-α) ≤ 1`). -/
private lemma norm_sub_div_rpow_le_max_of {X V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : X → V} {C L α : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    {x y : X} (hCx : ‖h x‖ ≤ C) (hCy : ‖h y‖ ≤ C)
    (hlip : ‖h x - h y‖ ≤ L * ‖x - y‖)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hxy : x ≠ y) :
    ‖h x - h y‖ / ‖x - y‖ ^ α ≤ max L (2 * C) := by
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hrle : 0 ≤ ‖x - y‖ := le_of_lt hr
  have h2C : ‖h x - h y‖ ≤ 2 * C := by
    have h := norm_sub_le (h x) (h y)
    linarith
  have hsub : ‖x - y‖ / ‖x - y‖ ^ α = ‖x - y‖ ^ (1 - α) := by
    rw [Real.rpow_sub hr (1 : ℝ) α, Real.rpow_one]
  by_cases hr1 : ‖x - y‖ ≤ 1
  · have hrpow : ‖x - y‖ ^ (1 - α) ≤ 1 := Real.rpow_le_one hrle hr1 (by linarith)
    calc ‖h x - h y‖ / ‖x - y‖ ^ α
        ≤ (L * ‖x - y‖) / ‖x - y‖ ^ α :=
          div_le_div_of_nonneg_right hlip (Real.rpow_nonneg hrle α)
      _ = L * ‖x - y‖ ^ (1 - α) := by rw [mul_div_assoc, hsub]
      _ ≤ L * 1 := mul_le_mul_of_nonneg_left hrpow hL
      _ = L := mul_one L
      _ ≤ max L (2 * C) := le_max_left _ _
  · have hr1' : 1 ≤ ‖x - y‖ := le_of_lt (not_le.mp hr1)
    have hαle : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow hr1' hα0
    calc ‖h x - h y‖ / ‖x - y‖ ^ α
        ≤ (2 * C) / ‖x - y‖ ^ α :=
          div_le_div_of_nonneg_right h2C (Real.rpow_nonneg hrle α)
      _ ≤ 2 * C := div_le_self (by linarith) hαle
      _ ≤ max L (2 * C) := le_max_right _ _

/-- **The `C^{k,α}` norm is finite for a smooth function on a bounded open set.**

If `Ω ⊆ {‖x‖ ≤ R}` and `f` is `C^{k+1}` on the whole space, then every iterated
derivative `D^i f` with `i ≤ k` is continuous, hence bounded on the compact closed
ball `B̄(0, max R 0 + 1) ⊇ Ω`, and the `(i+1)`-st derivative yields a Lipschitz bound
for `D^i f` on this ball by the mean value inequality.  Hence each term
`iterDerivNorm i f Ω + holderSeminorm i α f Ω` (`0 ≤ i ≤ k`) is finite, and so is the
whole sum. -/
theorem holderNorm_ne_top_of_isBounded {n : ℕ} {Ω : Set (Fin n → ℂ)} {R : ℝ}
    (hΩ : IsOpen Ω) (hR : ∀ x ∈ Ω, ‖x‖ ≤ R) {k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ (k + 1) f) :
    Work.CR.Flat.holderNorm k α f Ω ≠ ⊤ := by
  set M : ℝ := max R 0 with hM
  set S : Set (Fin n → ℂ) := Metric.closedBall 0 (M + 1) with hS
  have hΩS : Ω ⊆ S := by
    intro x hx
    rw [hS, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have h1 : ‖x‖ ≤ M := le_trans (hR x hx) (le_max_left R 0)
    have h2 : (0 : ℝ) ≤ M := le_max_right R 0
    linarith
  have h0S : (0 : Fin n → ℂ) ∈ S := by
    rw [hS, Metric.mem_closedBall, dist_self]
    have h2 : (0 : ℝ) ≤ M := le_max_right R 0
    linarith
  have hcompact : IsCompact S := by rw [hS]; exact isCompact_closedBall 0 (M + 1)
  have hconvex : Convex ℝ S := by rw [hS]; exact convex_closedBall 0 (M + 1)
  rw [Work.CR.Flat.holderNorm, ENNReal.sum_ne_top]
  intro i hi
  rw [Finset.mem_range] at hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp hi
  rw [ENNReal.add_ne_top]
  have hcont_i : Continuous (iteratedFDeriv ℝ i f) :=
    hf.continuous_iteratedFDeriv (m := i) (by exact_mod_cast (show i ≤ k + 1 by omega))
  have hcont_i1 : Continuous (iteratedFDeriv ℝ (i + 1) f) :=
    hf.continuous_iteratedFDeriv (m := i + 1) (by exact_mod_cast (show i + 1 ≤ k + 1 by omega))
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont_i.continuousOn
  obtain ⟨L, hL⟩ := hcompact.exists_bound_of_continuousOn hcont_i1.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 h0S)
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0 h0S)
  have hdiff : Differentiable ℝ (fun x => iteratedFDeriv ℝ i f x) :=
    hf.differentiable_iteratedFDeriv (m := i) (by exact_mod_cast (show i < k + 1 by omega))
  have heq := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) (s := Ω) i hΩ
  have hiter : Work.CR.Flat.iterDerivNorm i f Ω ≤ ENNReal.ofReal C := by
    simp only [Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun x hx => ?_
    rw [heq hx]
    exact ENNReal.ofReal_le_ofReal (hC x (hΩS hx))
  have hholder : Work.CR.Flat.holderSeminorm i α f Ω ≤ ENNReal.ofReal (max L (2 * C)) := by
    simp only [Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [heq hx, heq hy]
    refine ENNReal.ofReal_le_ofReal ?_
    have hlip : ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ L * ‖x - y‖ := by
      have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
        (f := fun z => iteratedFDeriv ℝ i f z) (s := S) (C := L)
        (fun z _ => hdiff z)
        (fun z hz => by rw [norm_fderiv_iteratedFDeriv]; exact hL z hz)
        hconvex (hΩS hx) (hΩS hy)
      simpa only [norm_sub_rev] using h
    exact norm_sub_div_rpow_le_max_of hC0 hL0 (hC x (hΩS hx)) (hC y (hΩS hy)) hlip
      (le_of_lt hα0) hα1 hxy
  constructor
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hiter
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hholder

end Work.CR.Flat.Holder
