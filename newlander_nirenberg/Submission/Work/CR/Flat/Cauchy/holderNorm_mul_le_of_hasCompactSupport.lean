import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open Set

/-! ## Auxiliary facts about the `C^{k,α}` norm of a compactly supported smooth function -/

/-- The elementary Hölder bound: a function which is bounded by `C` and `L`-Lipschitz has
divided differences of order `α ∈ [0,1]` bounded by `max L (2 C)`.  Small distances are
handled by the Lipschitz bound (`‖x - y‖ ^ (1 - α) ≤ 1`) and large ones by the sup bound
(`‖x - y‖ ^ (-α) ≤ 1`). -/
private lemma norm_sub_div_rpow_le_max_aux {X V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
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

/-- A compactly supported `C^{k+1}` function has finite `C^{k,α}` norm on all of `X`,
for an arbitrary real normed space `X`.  This is the generalisation of
`Work.CR.Flat.Holder.holderNorm_univ_ne_top_of_hasCompactSupport` from `ℂ` to `X`
needed in the proof of `holderNorm_mul_le_of_hasCompactSupport`. -/
theorem holderNorm_univ_ne_top_of_hasCompactSupport' {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {g : X → ℂ} (hg : ContDiff ℝ (k + 1) g) (hgs : HasCompactSupport g) :
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
    have hle : Work.CR.Flat.iterDerivNorm i g Set.univ ≤ ENNReal.ofReal C := by
      simp only [Work.CR.Flat.iterDerivNorm]
      rw [iteratedFDerivWithin_univ]
      exact iSup₂_le fun x _ => ENNReal.ofReal_le_ofReal (hC x)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
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
    have hle : Work.CR.Flat.holderSeminorm i α g Set.univ
        ≤ ENNReal.ofReal (max L (2 * C)) := by
      simp only [Work.CR.Flat.holderSeminorm]
      rw [iteratedFDerivWithin_univ]
      refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
      exact ENNReal.ofReal_le_ofReal (norm_sub_div_rpow_le_max_aux hC0 hL0 hC hlip hα0 hα1 hxy)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- If `g` is `C^k` on all of `X` then its `C^{k,α}` norm on an arbitrary subset `Ω`
(which need not be open) is bounded by its `C^{k,α}` norm on all of `X`:  at a point
`x ∈ Ω` the within derivatives of a function that is differentiable up to order `k` at
`x` coincide with the global iterated derivatives. -/
lemma holderNorm_le_univ_of_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} (hΩ : UniqueDiffOn ℝ Ω) {k : ℕ} {α : ℝ} {g : X → ℂ}
    (hg : ContDiff ℝ (k : ℕ) g) :
    Work.CR.Flat.holderNorm k α g Ω ≤ Work.CR.Flat.holderNorm k α g Set.univ := by
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hderiv : ∀ x ∈ Ω,
      iteratedFDerivWithin ℝ i g Ω x = iteratedFDerivWithin ℝ i g Set.univ x := by
    intro x hx
    rw [iteratedFDerivWithin_univ]
    exact iteratedFDerivWithin_eq_iteratedFDeriv hΩ
      (hg.contDiffAt.of_le (by exact_mod_cast hik)) hx
  refine add_le_add ?_ ?_
  · rw [Work.CR.Flat.iterDerivNorm, Work.CR.Flat.iterDerivNorm]
    refine iSup₂_le fun x hx => ?_
    exact le_iSup₂_of_le x (Set.mem_univ x) (by rw [hderiv x hx])
  · rw [Work.CR.Flat.holderSeminorm, Work.CR.Flat.holderSeminorm]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    exact le_iSup₂_of_le x (Set.mem_univ x)
      (le_iSup₂_of_le y (Set.mem_univ y) (le_iSup_of_le hxy (by rw [hderiv x hx, hderiv y hy])))

/-- **Multiplication by a fixed compactly supported smooth function is bounded on `C^{k,α}(Ω)`.**

If `ζ : ℂⁿ → ℂ` is `C^{k+1}` with compact support and `0 ≤ α ≤ 1`, then there is `C > 0` with
`‖ζ · f‖_{C^{k,α}(Ω)} ≤ C ‖f‖_{C^{k,α}(Ω)}` for every `f` that is `C^k` on `Ω` (`Ω` satisfying
`UniqueDiffOn ℝ Ω`).  If `‖f‖_{k,α}(Ω) = ⊤` the inequality is trivial; otherwise apply
`Work.CR.Flat.Holder.holderNorm_mul_le` with `(f, g) = (ζ, f)`, for which one needs
`holderNorm k α ζ Ω ≠ ⊤`: that follows from `hζ`, `hζs`, `0 ≤ α ≤ 1` and
`holderNorm_mono_set` from the finiteness of `holderNorm k α ζ Set.univ`, which is proved by the
same argument as the existing `Work.CR.Flat.Holder.holderNorm_univ_ne_top_of_hasCompactSupport`
(generalised from `ℂ → ℂ` to an arbitrary real normed space `X`): a compactly supported `C^{k+1}`
function has bounded iterated derivatives up to order `k+1`, and the `k`-th derivative is
Lipschitz, whence the order-`i` Hölder seminorms are finite. -/
theorem holderNorm_mul_le_of_hasCompactSupport {n : ℕ} {Ω : Set (Fin n → ℂ)}
    (hΩ : UniqueDiffOn ℝ Ω) {k : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {ζ : (Fin n → ℂ) → ℂ} (hζ : ContDiff ℝ (k + 1) ζ) (hζs : HasCompactSupport ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (Fin n → ℂ) → ℂ, ContDiffOn ℝ (k : ℕ∞) f Ω →
      Work.CR.Flat.holderNorm k α (fun z => ζ z * f z) Ω
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm k α f Ω := by
  -- `ζ` has finite `C^{k,α}` norm on `Ω`
  have hζfin : Work.CR.Flat.holderNorm k α ζ Ω ≠ ⊤ :=
    ne_top_of_le_ne_top
      (holderNorm_univ_ne_top_of_hasCompactSupport' (X := Fin n → ℂ) hα0 hα1 hζ hζs)
      (holderNorm_le_univ_of_contDiff hΩ (hζ.of_le (by exact_mod_cast Nat.le_succ k)))
  -- the constant carried by the Leibniz bound
  set A : ℝ≥0∞ := ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * Work.CR.Flat.holderNorm k α ζ Ω with hA
  have hAne : A ≠ ⊤ := by
    rw [hA]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by norm_num))) hζfin
  refine ⟨A.toReal + 1, by linarith [ENNReal.toReal_nonneg (a := A)], fun f hf => ?_⟩
  have hAle : A ≤ ENNReal.ofReal (A.toReal + 1) := by
    calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hAne).symm
      _ ≤ ENNReal.ofReal (A.toReal + 1) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  by_cases hfin : Work.CR.Flat.holderNorm k α f Ω = ⊤
  · have hne : ENNReal.ofReal (A.toReal + 1) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by linarith [ENNReal.toReal_nonneg (a := A)])
    rw [hfin, ENNReal.mul_top hne]
    exact le_top
  · have hb := Work.CR.Flat.Holder.holderNorm_mul_le (f := ζ) (g := f) (Ω := Ω)
      ((hζ.contDiffOn).of_le (by exact_mod_cast Nat.le_succ k)) hf hΩ hζfin hfin
    calc Work.CR.Flat.holderNorm k α (fun z => ζ z * f z) Ω
        ≤ A * Work.CR.Flat.holderNorm k α f Ω := by rw [hA]; exact hb
      _ ≤ ENNReal.ofReal (A.toReal + 1) * Work.CR.Flat.holderNorm k α f Ω :=
          mul_le_mul_left hAle _

end Work.CR.Flat.Cauchy
