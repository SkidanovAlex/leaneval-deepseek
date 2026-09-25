import Mathlib
import Submission.Work.CR.Flat.Holder

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- If the `i`-th iterated derivative of `f` is bounded on all of `Set.univ`, then the
corresponding sup norm of derivatives is finite (i.e. not `⊤`). -/
private lemma iterDerivNorm_univ_ne_top_of_bound {i : ℕ} {f : X → ℂ} {C : ℝ}
    (hC : ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C) :
    Work.CR.Flat.iterDerivNorm i f Set.univ ≠ ⊤ := by
  have hle : Work.CR.Flat.iterDerivNorm i f Set.univ ≤ ENNReal.ofReal C := by
    simp only [Work.CR.Flat.iterDerivNorm]
    rw [iteratedFDerivWithin_univ]
    exact iSup₂_le fun x _ => ENNReal.ofReal_le_ofReal (hC x)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- If the divided differences of the `i`-th iterated derivative of `f` are bounded by `B`,
then the Hölder seminorm of order `α` is finite (i.e. not `⊤`). -/
private lemma holderSeminorm_univ_ne_top_of_bound {i : ℕ} {α : ℝ} {f : X → ℂ} {B : ℝ}
    (hB : ∀ x y, x ≠ y →
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α ≤ B) :
    Work.CR.Flat.holderSeminorm i α f Set.univ ≠ ⊤ := by
  have hle : Work.CR.Flat.holderSeminorm i α f Set.univ ≤ ENNReal.ofReal B := by
    simp only [Work.CR.Flat.holderSeminorm]
    rw [iteratedFDerivWithin_univ]
    exact iSup₂_le fun x _ => iSup₂_le fun y _ =>
      iSup_le fun hxy => ENNReal.ofReal_le_ofReal (hB x y hxy)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

omit [NormedSpace ℝ X] in
/-- The elementary Hölder bound: a function which is bounded by `C` and `L`-Lipschitz has
divided differences of order `α ∈ [0,1]` bounded by `max L (2 C)`.  Small distances are
handled by the Lipschitz bound (`‖x - y‖ ^ (1 - α) ≤ 1`) and large ones by the sup bound
(`‖x - y‖ ^ (-α) ≤ 1`). -/
private lemma norm_sub_div_rpow_le_max {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : X → V} {C L α : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hnorm : ∀ x, ‖h x‖ ≤ C) (hlip : ∀ x y, ‖h x - h y‖ ≤ L * ‖x - y‖)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {x y : X} (hxy : x ≠ y) :
    ‖h x - h y‖ / ‖x - y‖ ^ α ≤ max L (2 * C) := by
  have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hrle : 0 ≤ ‖x - y‖ := le_of_lt hr
  have h2C : ‖h x - h y‖ ≤ 2 * C := by
    have h := norm_sub_le (h x) (h y)
    linarith [hnorm x, hnorm y]
  have hsub : ‖x - y‖ / ‖x - y‖ ^ α = ‖x - y‖ ^ (1 - α) := by
    rw [Real.rpow_sub hr (1 : ℝ) α, Real.rpow_one]
  by_cases hr1 : ‖x - y‖ ≤ 1
  · have hrpow : ‖x - y‖ ^ (1 - α) ≤ 1 := Real.rpow_le_one hrle hr1 (by linarith)
    calc ‖h x - h y‖ / ‖x - y‖ ^ α
        ≤ (L * ‖x - y‖) / ‖x - y‖ ^ α :=
          div_le_div_of_nonneg_right (hlip x y) (Real.rpow_nonneg hrle α)
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

theorem holderNorm_univ_ne_top_of_hasCompactSupport {k : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {g : ℂ → ℂ} (hg : ContDiff ℝ (k+1) g) (hgs : HasCompactSupport g) :
    Work.CR.Flat.holderNorm k α g Set.univ ≠ ⊤ := by
  -- each iterated derivative up to order `k + 1` is bounded, being continuous with compact support
  have hbdd : ∀ i ≤ k + 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    intro i hik
    have hcont : Continuous (iteratedFDeriv ℝ i g) :=
      hg.continuous_iteratedFDeriv (m := i) (by exact_mod_cast hik)
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hgs.iteratedFDeriv i)
    exact ⟨C, le_trans (norm_nonneg _) (hC 0), hC⟩
  rw [Work.CR.Flat.holderNorm, ENNReal.sum_ne_top]
  intro i hi
  rw [Finset.mem_range] at hi
  have hik : i ≤ k := Nat.lt_succ_iff.mp hi
  rw [ENNReal.add_ne_top]
  constructor
  · obtain ⟨C, _, hC⟩ := hbdd i (by omega)
    exact iterDerivNorm_univ_ne_top_of_bound hC
  · obtain ⟨C, hC0, hC⟩ := hbdd i (by omega)
    obtain ⟨L, hL0, hL⟩ := hbdd (i + 1) (by omega)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i g) :=
      hg.differentiable_iteratedFDeriv (m := i) (by
        exact_mod_cast (show i < k + 1 by omega))
    have hlip : ∀ x y, ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ L * ‖x - y‖ := by
      intro x y
      have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := iteratedFDeriv ℝ i g)
        (s := Set.univ) (C := L) (fun z _ => hdiff z)
        (fun z _ => by rw [norm_fderiv_iteratedFDeriv]; exact hL z)
        convex_univ (Set.mem_univ x) (Set.mem_univ y)
      simpa only [norm_sub_rev] using h
    refine holderSeminorm_univ_ne_top_of_bound (B := max L (2 * C)) (fun x y hxy => ?_)
    exact norm_sub_div_rpow_le_max hC0 hL0 hC hlip hα0 hα1 hxy

end Work.CR.Flat.Holder
