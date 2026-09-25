import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSquareLp

/-!
# The annulus square-function `L^p` bound with explicit Mikhlin data

`annulusSquareLp` (`Submission/Work/BourgainPlan/Maximal/annulusSquareLp.lean`) proves the
Littlewood--Paley square-function bound

  `∫⁻ x, (∑'_n ‖(K_{j+n} * f)(x)‖²)^{p/2} ≤ C ∫⁻ x, ‖f x‖^p`

for a symbol family `b` satisfying `AnnulusSymbolSmooth b` (which requires a *uniform in `m`* bound
on **every** iterated derivative) and each `b m` of class `C^∞`.  The constant it produces,
however, is read off from the existential constants of `AnnulusSymbolSmooth b` and therefore
depends on `b`.

This module re-proves the same bound with the Mikhlin data as *explicit parameters*, so that the
constant is uniform over the entire family of symbol families whose first three derivatives obey
the stated bounds.  This is exactly what the *shifted* family `m ↦ d (m - j) · φ m` of MST's
`(eq:52)` needs: its annulus support, its `C₀` bound and its `C₁`, `C₂` derivative bounds are
uniform in `j`, even though `AnnulusSymbolSmooth` of the shifted family may fail uniformly in `j`.

Only three properties of `b` are ever used:

* the **annulus support** `2⁻¹ < |2^m ξ| < 2` off the zero set (`AnnulusSupp`);
* the **`C^∞` smoothness** of each `b m` (for the integrability of the kernels and symbols);
* the three **Mikhlin bounds** `‖b m ξ‖ ≤ C₀`, `‖deriv (b m) ξ‖ ≤ C₁ 2^m`,
  `‖iteratedDeriv 2 (b m) ξ‖ ≤ C₂ 2^{2m}`.

The uniform Mikhlin constant of the signed sums is `A = max (5 C₀) (max (10 C₁) (20 C₂))`, coming
from the `5`-fold bounded overlap of the annuli.  The rest of the chain is repeated verbatim from
`annulusSymbolSum_mikhlin`, `annulusSqfun_finsetMikhlin` and `annulusSquareLp_finset`, with `hb`
replaced by `AnnulusSupp b` and the constants kept explicit.

A small simplification is used throughout: instead of restating the kernel decay estimate
`annulusKernel_size`, we observe that `b m` has compact support and is `C^∞`, hence is a Schwartz
function, so that `annulusK b m = 𝓕⁻ (b m)` is Schwartz (`SchwartzMap.fourierInv_coe` +
`SchwartzMap.memLp`) and therefore lies in **every** `L^p`.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Work.BourgainPlan.Maximal

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-! ## 0. The support predicate -/

/-- **The annulus support condition**, as a standalone predicate: it is precisely the first
conjunct of `AnnulusSymbolSmooth`. -/
abbrev AnnulusSupp (b : ℤ → ℝ → ℂ) : Prop :=
  ∀ m ξ, b m ξ ≠ 0 → (2 : ℝ)⁻¹ < |(2 : ℝ) ^ m * ξ| ∧ |(2 : ℝ) ^ m * ξ| < 2

/-- The explicit Mikhlin constant of the signed annulus symbol sums, from the `5`-fold bounded
overlap of the annuli: `max (5 C₀) (max (10 C₁) (20 C₂))`. -/
noncomputable def annulusMikhlinConst (C₀ C₁ C₂ : ℝ) : ℝ :=
  max (5 * (2 : ℝ) ^ (0 : ℕ) * C₀)
    (max (5 * (2 : ℝ) ^ (1 : ℕ) * C₁) (5 * (2 : ℝ) ^ (2 : ℕ) * C₂))

/-! ## 1. The support condition alone: vanishing off the annuli and compact support -/

/-- If `b` is supported in the annuli, then `b m` vanishes for `|ξ| > 2^{1-m}`. -/
lemma annulusSupp_eq_zero (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b) (m : ℤ) :
    ∀ ξ, (2 : ℝ) ^ (1 - m) < |ξ| → b m ξ = 0 := by
  intro ξ hξ
  by_contra hne
  have hlt : |(2 : ℝ) ^ m * ξ| < 2 := (hsupp m ξ hne).2
  rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) m)] at hlt
  have h2 : (2 : ℝ) ^ m * (2 : ℝ) ^ (1 - m) = 2 := by
    rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),
        show m + (1 - m) = (1 : ℤ) by ring, zpow_one]
  have hlt' : (2 : ℝ) ^ m * |ξ| < (2 : ℝ) ^ m * (2 : ℝ) ^ (1 - m) := by
    rw [h2]; exact hlt
  exact absurd (lt_of_mul_lt_mul_left hlt' (le_of_lt (zpow_pos (by norm_num : (0:ℝ) < 2) m)))
    (not_lt.mpr hξ.le)

/-- Every iterated derivative of `b m` vanishes for `|ξ| > 2^{1-m}`. -/
lemma annulusSupp_iteratedDeriv_eq_zero (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (m : ℤ) (k : ℕ) :
    ∀ ξ, (2 : ℝ) ^ (1 - m) < |ξ| → iteratedDeriv k (b m) ξ = 0 := by
  induction k with
  | zero => intro ξ hξ; simpa using annulusSupp_eq_zero b hsupp m ξ hξ
  | succ k ih =>
      intro ξ hξ
      rw [iteratedDeriv_succ]
      exact annulusK_deriv_eq_zero_of_eq_zero_on_open
        (isOpen_lt continuous_const continuous_abs) (fun x hx => ih x hx) ξ hξ

/-- `b m` has compact support (it is supported in `[-2^{1-m}, 2^{1-m}]`). -/
lemma annulusSupp_hasCompactSupport (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b) (m : ℤ) :
    HasCompactSupport (b m) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (-((2 : ℝ) ^ (1 - m))) ((2 : ℝ) ^ (1 - m))) isCompact_Icc ?_
  intro x hx
  have hle : |x| ≤ (2 : ℝ) ^ (1 - m) := by
    by_contra hcon
    exact hx (annulusSupp_eq_zero b hsupp m x (not_le.mp hcon))
  rw [abs_le] at hle
  exact hle

/-- So does every iterated derivative. -/
lemma annulusSupp_hasCompactSupport_iteratedDeriv (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (m : ℤ) (k : ℕ) : HasCompactSupport (iteratedDeriv k (b m)) := by
  induction k with
  | zero => simpa using annulusSupp_hasCompactSupport b hsupp m
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- Hence every iterated derivative is integrable. -/
lemma annulusSupp_integrable (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) (k : ℕ) :
    Integrable (iteratedDeriv k (b m)) volume :=
  (ContDiff.continuous_iteratedDeriv k (hsmooth m) (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
    (annulusSupp_hasCompactSupport_iteratedDeriv b hsupp m k)

/-- **The topological support of `b m` lies in the closed annulus `2⁻¹ ≤ |2^m ξ| ≤ 2`.** -/
lemma annulusSupp_tsupport_abs_bounds (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b) (m : ℤ) {ξ : ℝ}
    (hξ : ξ ∈ tsupport (b m)) :
    (2 : ℝ)⁻¹ ≤ |(2 : ℝ) ^ m * ξ| ∧ |(2 : ℝ) ^ m * ξ| ≤ 2 := by
  have hcont : Continuous fun y : ℝ => |(2 : ℝ) ^ m * y| :=
    continuous_abs.comp (continuous_const.mul continuous_id)
  have hclosed : IsClosed ((fun y : ℝ => |(2 : ℝ) ^ m * y|) ⁻¹' Set.Icc (2 : ℝ)⁻¹ 2) :=
    isClosed_Icc.preimage hcont
  have hsub : Function.support (b m) ⊆
      (fun y : ℝ => |(2 : ℝ) ^ m * y|) ⁻¹' Set.Icc (2 : ℝ)⁻¹ 2 := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsupp m y (Function.mem_support.mp hy)
    exact ⟨le_of_lt h1, le_of_lt h2⟩
  have := (IsClosed.closure_subset_iff hclosed).mpr hsub hξ
  simpa [Set.mem_Icc] using this

/-! ## 2. The uniform Mikhlin bound for the signed sums -/

/-- **At most five levels carry a non-zero `k`-th derivative.** -/
lemma annulusSupp_card_filter_iteratedDeriv_le (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (j : ℤ) (ξ : ℝ) (F : Finset ℤ) (k : ℕ) :
    (F.filter (fun n => iteratedDeriv k (b (j + n)) ξ ≠ 0)).card ≤ 5 := by
  by_cases hex : ∃ n ∈ F, iteratedDeriv k (b (j + n)) ξ ≠ 0
  · obtain ⟨n₀, hn₀F, hn₀⟩ := hex
    have hts₀ : ξ ∈ tsupport (b (j + n₀)) := by
      by_contra hmem
      exact hn₀ (iteratedDeriv_eq_zero_of_notMem_tsupport hmem)
    obtain ⟨hlo₀, hhi₀⟩ := annulusSupp_tsupport_abs_bounds b hsupp (j + n₀) hts₀
    have hbound : ∀ n ∈ F, iteratedDeriv k (b (j + n)) ξ ≠ 0 →
        n ∈ Finset.Icc (n₀ - 2) (n₀ + 2) := by
      intro n hnF hn
      have hts : ξ ∈ tsupport (b (j + n)) := by
        by_contra hmem
        exact hn (iteratedDeriv_eq_zero_of_notMem_tsupport hmem)
      obtain ⟨hlo, hhi⟩ := annulusSupp_tsupport_abs_bounds b hsupp (j + n) hts
      have hle : (j + n) - (j + n₀) ≤ 2 := zpow_sub_le_two hlo₀ hhi
      have hle' : (j + n₀) - (j + n) ≤ 2 := zpow_sub_le_two hlo hhi₀
      simp only [Finset.mem_Icc]
      omega
    calc (F.filter (fun n => iteratedDeriv k (b (j + n)) ξ ≠ 0)).card
        ≤ (Finset.Icc (n₀ - 2) (n₀ + 2)).card :=
          Finset.card_le_card (fun n hn => by
            rw [Finset.mem_filter] at hn
            exact hbound n hn.1 hn.2)
      _ = 5 := by
        rw [Int.card_Icc]
        have h5 : (n₀ + 2 + 1 - (n₀ - 2) : ℤ) = 5 := by ring
        rw [h5]; decide
  · have hempty : F.filter (fun n => iteratedDeriv k (b (j + n)) ξ ≠ 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro n hn hnz
      exact hex ⟨n, hn, hnz⟩
    rw [hempty]; simp

/-- **The `k`-th Mikhlin bound with an explicit derivative constant.**  If the `k`-th derivative of
each `b m` is bounded by `C · (2^m)^k`, then the same bound holds for the signed sum, with the extra
factor `5 · 2^k` coming from the `5`-fold bounded overlap of the annuli. -/
lemma annulusSupp_iteratedDeriv_bound (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) (hε : ∀ n, ‖ε n‖ ≤ 1)
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hCb : ∀ (m : ℤ) (ξ : ℝ), ‖iteratedDeriv k (b m) ξ‖ ≤ C * ((2 : ℝ) ^ m) ^ k)
    (ξ : ℝ) :
    |ξ| ^ k * ‖iteratedDeriv k (annulusSymbolSum b j F ε) ξ‖ ≤ 5 * (2 : ℝ) ^ k * C := by
  classical
  set S : Finset ℤ := F.filter (fun n => iteratedDeriv k (b (j + n)) ξ ≠ 0) with hSdef
  have hcard : S.card ≤ 5 := annulusSupp_card_filter_iteratedDeriv_le b hsupp j ξ F k
  have hsub : S ⊆ F := Finset.filter_subset _ _
  have hzero : ∀ n ∈ F, n ∉ S → ε n * iteratedDeriv k (b (j + n)) ξ = 0 := by
    intro n hnF hnS
    have hz : iteratedDeriv k (b (j + n)) ξ = 0 := by
      by_contra hne
      exact hnS (by rw [hSdef, Finset.mem_filter]; exact ⟨hnF, hne⟩)
    rw [hz, mul_zero]
  have hsum_eq : (∑ n ∈ S, ε n * iteratedDeriv k (b (j + n)) ξ)
      = ∑ n ∈ F, ε n * iteratedDeriv k (b (j + n)) ξ :=
    Finset.sum_subset hsub hzero
  have hterm : ∀ n ∈ S, |ξ| ^ k * ‖ε n * iteratedDeriv k (b (j + n)) ξ‖ ≤ C * (2 : ℝ) ^ k := by
    intro n hn
    rw [hSdef, Finset.mem_filter] at hn
    obtain ⟨hnF, hnz⟩ := hn
    have hts : ξ ∈ tsupport (b (j + n)) := by
      by_contra hmem
      exact hnz (iteratedDeriv_eq_zero_of_notMem_tsupport hmem)
    obtain ⟨hlo, hhi⟩ := annulusSupp_tsupport_abs_bounds b hsupp (j + n) hts
    calc |ξ| ^ k * ‖ε n * iteratedDeriv k (b (j + n)) ξ‖
        ≤ |ξ| ^ k * ‖iteratedDeriv k (b (j + n)) ξ‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ‖ε n * iteratedDeriv k (b (j + n)) ξ‖
              = ‖ε n‖ * ‖iteratedDeriv k (b (j + n)) ξ‖ := norm_mul _ _
            _ ≤ 1 * ‖iteratedDeriv k (b (j + n)) ξ‖ :=
                mul_le_mul_of_nonneg_right (hε n) (norm_nonneg _)
            _ = ‖iteratedDeriv k (b (j + n)) ξ‖ := one_mul _
      _ ≤ |ξ| ^ k * (C * ((2 : ℝ) ^ (j + n)) ^ k) :=
          mul_le_mul_of_nonneg_left (hCb (j + n) ξ) (by positivity)
      _ = C * (|ξ| * (2 : ℝ) ^ (j + n)) ^ k := by rw [mul_pow]; ring
      _ = C * |(2 : ℝ) ^ (j + n) * ξ| ^ k := by
          have hc : |ξ| * (2 : ℝ) ^ (j + n) = |(2 : ℝ) ^ (j + n) * ξ| := by
            rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) (j + n)), mul_comm]
          rw [hc]
      _ ≤ C * (2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hhi k) hC
  have hrew : iteratedDeriv k (annulusSymbolSum b j F ε) ξ
      = ∑ n ∈ F, ε n * iteratedDeriv k (b (j + n)) ξ :=
    annulusSymbolSum_iteratedDeriv b hsmooth j F ε k ξ
  calc |ξ| ^ k * ‖iteratedDeriv k (annulusSymbolSum b j F ε) ξ‖
      = |ξ| ^ k * ‖∑ n ∈ S, ε n * iteratedDeriv k (b (j + n)) ξ‖ := by
        rw [hrew, ← hsum_eq]
    _ ≤ |ξ| ^ k * ∑ n ∈ S, ‖ε n * iteratedDeriv k (b (j + n)) ξ‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le S _) (by positivity)
    _ = ∑ n ∈ S, |ξ| ^ k * ‖ε n * iteratedDeriv k (b (j + n)) ξ‖ := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _n ∈ S, C * (2 : ℝ) ^ k := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (C * (2 : ℝ) ^ k) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 5 * (C * (2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = 5 * (2 : ℝ) ^ k * C := by ring

/-- **The three Mikhlin bounds for the signed annulus symbol sums with explicit constants.** -/
theorem annulusSymbolSum_mikhlin_explicit (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    {C₀ C₁ C₂ : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂)
    (hD0 : ∀ m ξ, ‖b m ξ‖ ≤ C₀)
    (hD1 : ∀ m ξ, ‖deriv (b m) ξ‖ ≤ C₁ * (2 : ℝ) ^ m)
    (hD2 : ∀ m ξ, ‖iteratedDeriv 2 (b m) ξ‖ ≤ C₂ * (2 : ℝ) ^ (2 * m)) :
    ∀ (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ), (∀ n, ‖ε n‖ ≤ 1) →
      (∀ ξ : ℝ, ‖annulusSymbolSum b j F ε ξ‖ ≤ annulusMikhlinConst C₀ C₁ C₂) ∧
      (∀ ξ : ℝ, |ξ| * ‖deriv (annulusSymbolSum b j F ε) ξ‖
        ≤ annulusMikhlinConst C₀ C₁ C₂) ∧
      (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 (annulusSymbolSum b j F ε) ξ‖
        ≤ annulusMikhlinConst C₀ C₁ C₂) := by
  intro j F ε hε
  refine ⟨?_, ?_, ?_⟩
  · intro ξ
    have hkey := annulusSupp_iteratedDeriv_bound b hsupp hsmooth j F ε hε 0 C₀ h₀
      (fun m ξ => by simpa using hD0 m ξ) ξ
    refine le_trans ?_ (le_max_left _ _)
    simpa [annulusMikhlinConst] using hkey
  · intro ξ
    have hCb : ∀ (m : ℤ) (ξ : ℝ), ‖iteratedDeriv 1 (b m) ξ‖ ≤ C₁ * ((2 : ℝ) ^ m) ^ 1 := by
      intro m ξ
      simpa [iteratedDeriv_one, pow_one] using hD1 m ξ
    have hkey := annulusSupp_iteratedDeriv_bound b hsupp hsmooth j F ε hε 1 C₁ h₁ hCb ξ
    refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_right _ _))
    simpa [iteratedDeriv_one, pow_one, annulusMikhlinConst] using hkey
  · intro ξ
    have hCb : ∀ (m : ℤ) (ξ : ℝ), ‖iteratedDeriv 2 (b m) ξ‖ ≤ C₂ * ((2 : ℝ) ^ m) ^ 2 := by
      intro m ξ
      have h : ((2 : ℝ) ^ m) ^ 2 = (2 : ℝ) ^ (2 * m) := by
        rw [pow_two, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), show m + m = 2 * m by ring]
      rw [h]; exact hD2 m ξ
    have hkey := annulusSupp_iteratedDeriv_bound b hsupp hsmooth j F ε hε 2 C₂ h₂ hCb ξ
    refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_right _ _))
    simpa [annulusMikhlinConst] using hkey

/-! ## 3. Integrability of the signed symbols (support + smoothness alone) -/

/-- The signed symbol sum has compact support. -/
lemma annulusSupp_hasCompactSupport_annulusSymbolSum (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) : HasCompactSupport (annulusSymbolSum b j F ε) := by
  rw [show annulusSymbolSum b j F ε = fun ξ : ℝ => ∑ n ∈ F, ε n * b (j + n) ξ from rfl]
  refine HasCompactSupport.of_support_subset_isCompact
    (K := ⋃ n ∈ (F : Set ℤ), Set.Icc (-((2:ℝ)^(1-(j+n)))) ((2:ℝ)^(1-(j+n)))) ?_ ?_
  · exact Set.Finite.isCompact_biUnion F.finite_toSet (fun n _ => isCompact_Icc)
  · intro ξ hξ
    simp only [Function.mem_support] at hξ
    have hex : ∃ n ∈ F, b (j + n) ξ ≠ 0 := by
      by_contra h
      push Not at h
      exact hξ (Finset.sum_eq_zero (fun n hn => by rw [h n hn, mul_zero]))
    obtain ⟨n, hnF, hbn⟩ := hex
    refine Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · simpa using hnF
    · have hle : |ξ| ≤ (2:ℝ)^(1-(j+n)) := by
        by_contra hcon
        exact hbn (annulusSupp_eq_zero b hsupp (j + n) ξ (not_le.mp hcon))
      exact abs_le.mp hle

/-- The signed symbol sum is integrable. -/
lemma annulusSupp_integrable_annulusSymbolSum (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) : Integrable (annulusSymbolSum b j F ε) volume :=
  ((contDiff_annulusSymbolSum b hsmooth j F ε).continuous).integrable_of_hasCompactSupport
    (annulusSupp_hasCompactSupport_annulusSymbolSum b hsupp j F ε)

/-- The inverse Fourier transform of the signed symbol sum is integrable. -/
lemma annulusSupp_integrable_fourierInv_annulusSymbolSum (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) :
    Integrable (FourierTransformInv.fourierInv (annulusSymbolSum b j F ε)) volume :=
  Commons.Analysis.Fourier.integrable_fourierInv_of_contDiff_hasCompactSupport
    (annulusSupp_hasCompactSupport_annulusSymbolSum b hsupp j F ε)
    ((contDiff_annulusSymbolSum b hsmooth j F ε).of_le (by exact_mod_cast le_top))

/-! ## 4. The Mikhlin step with an explicit constant -/

/-- **The Mikhlin multiplier bound for a signed annulus symbol sum, with the constant explicit in
the data `C₀, C₁, C₂`.** -/
theorem annulusSymbolSum_convolution_le_explicit {C₀ C₁ C₂ : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁)
    (h₂ : 0 ≤ C₂) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
      (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
      (hD0 : ∀ m ξ, ‖b m ξ‖ ≤ C₀)
      (hD1 : ∀ m ξ, ‖deriv (b m) ξ‖ ≤ C₁ * (2 : ℝ) ^ m)
      (hD2 : ∀ m ξ, ‖iteratedDeriv 2 (b m) ξ‖ ≤ C₂ * (2 : ℝ) ^ (2 * m))
      (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ), (∀ n, ‖ε n‖ ≤ 1) →
      ∀ f : ℝ → ℂ, MemLp f (ENNReal.ofReal p) volume →
      ∫⁻ x, ‖∫ y : ℝ,
          FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y‖ₑ ^ p
        ≤ ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ ^ p := by
  obtain ⟨Cm, hCm, hmik⟩ := mikhlinConvolutionLp p hp
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  set A : ℝ := annulusMikhlinConst C₀ C₁ C₂ with hA
  have hA0 : 0 ≤ A := by
    rw [hA, annulusMikhlinConst]
    refine le_trans (by positivity : (0:ℝ) ≤ 5 * (2:ℝ)^(0:ℕ) * C₀) (le_max_left _ _)
  have hA1 : 0 < A + 1 := by linarith
  refine ⟨(Cm * (A + 1)) ^ p, Real.rpow_pos_of_pos (mul_pos hCm hA1) p,
    fun b hsupp hsmooth hD0 hD1 hD2 j F ε hε f hf => ?_⟩
  obtain ⟨h1, h2, h3⟩ := annulusSymbolSum_mikhlin_explicit b hsupp hsmooth h₀ h₁ h₂ hD0 hD1 hD2
    j F ε hε
  have h1' : ∀ ξ : ℝ, ‖annulusSymbolSum b j F ε ξ‖ ≤ A + 1 := fun ξ => le_trans (h1 ξ) (by linarith)
  have h2' : ∀ ξ : ℝ, |ξ| * ‖deriv (annulusSymbolSum b j F ε) ξ‖ ≤ A + 1 :=
    fun ξ => le_trans (h2 ξ) (by linarith)
  have h3' : ∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 (annulusSymbolSum b j F ε) ξ‖ ≤ A + 1 :=
    fun ξ => le_trans (h3 ξ) (by linarith)
  have hbnd := hmik (annulusSymbolSum b j F ε) (A + 1) (by linarith)
    (annulusSupp_integrable_annulusSymbolSum b hsupp hsmooth j F ε)
    ((annulusSymbolSum_contDiff b hsmooth j F ε))
    h1' h2' h3'
    (annulusSupp_integrable_fourierInv_annulusSymbolSum b hsupp hsmooth j F ε) f hf
  have hconvm : AEStronglyMeasurable (fun x : ℝ => ∫ y : ℝ,
      FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y) volume := by
    have hJ : AEStronglyMeasurable (fun z : ℝ × ℝ =>
        FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (z.1 - z.2) * f z.2)
        ((volume : Measure ℝ).prod volume) :=
      ((annulusSupp_integrable_fourierInv_annulusSymbolSum b hsupp hsmooth j F ε).aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul
        hf.aestronglyMeasurable.comp_snd
    exact hJ.integral_prod_right'
  calc ∫⁻ x, ‖∫ y : ℝ,
        FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y‖ₑ ^ p
      = (MeasureTheory.eLpNorm (fun x : ℝ => ∫ y : ℝ,
          FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y)
          (ENNReal.ofReal p) volume) ^ p := (annulusELpNorm_rpow_eq_lintegral hp0 hconvm).symm
    _ ≤ (ENNReal.ofReal (Cm * (A + 1)) * MeasureTheory.eLpNorm f (ENNReal.ofReal p) volume) ^ p :=
        ENNReal.rpow_le_rpow hbnd hp0.le
    _ = ENNReal.ofReal ((Cm * (A + 1)) ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCm.le (by linarith)) hp0.le,
          annulusELpNorm_rpow_eq_lintegral hp0 hf.aestronglyMeasurable]

/-! ## 5. The annulus kernels lie in every `L^p` (Schwartz shortcut) -/

/-- **`annulusK b m` lies in every `L^p`.**  `b m` has compact support and is `C^∞`, hence is a
Schwartz function, so `𝓕⁻ (b m)` is Schwartz and Schwartz functions are in every `L^p`. -/
lemma annulusSupp_memLp_annulusK (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ)
    (p : ℝ≥0∞) : MemLp (annulusK b m) p volume := by
  have hc : HasCompactSupport (b m) := annulusSupp_hasCompactSupport b hsupp m
  have hcoe : ((hc.toSchwartzMap (hsmooth m) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = b m := by
    funext x
    rw [HasCompactSupport.toSchwartzMap_toFun]
  rw [show annulusK b m
      = ⇑(FourierTransformInv.fourierInv (hc.toSchwartzMap (hsmooth m) : SchwartzMap ℝ ℂ)) from by
    rw [SchwartzMap.fourierInv_coe, hcoe]
    simp only [annulusK]]
  exact SchwartzMap.memLp _ p volume

/-- The reflected annulus kernel `y ↦ K_m (x - y)` lies in every `L^p`. -/
lemma annulusSupp_memLp_shifted_annulusK (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) (m : ℤ) (x : ℝ)
    (p : ℝ≥0∞) : MemLp (fun y : ℝ => annulusK b m (x - y)) p volume :=
  (annulusSupp_memLp_annulusK b hsupp hsmooth m p).comp_measurePreserving
    (measurePreserving_annulusSub x)

/-! ## 6. The signed sum of the annulus convolutions is a convolution -/

/-- **The signed sum of the annulus convolutions is the convolution with the signed symbol sum**
(under the support + smoothness hypotheses alone). -/
theorem annulusSupp_conv_finsetSum_eq (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    {p : ℝ} (hp : 1 ≤ p) (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) (f : ℝ → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) volume) (x : ℝ) :
    (∑ n ∈ F, ε n * annulusConv b (j + n) f x)
      = ∫ y : ℝ,
          FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y := by
  have hbint : ∀ n : ℤ, Integrable (b n) volume := fun n => by
    simpa only [iteratedDeriv_zero] using annulusSupp_integrable b hsupp hsmooth n 0
  have hlin : ∀ z : ℝ, FourierTransform.fourierInv (annulusSymbolSum b j F ε) z
      = ∑ n ∈ F, ε n * annulusK b (j + n) z := fun z =>
    fourierInv_annulusSymbolSum_apply b hbint j F ε z
  have hInt : ∀ n : ℤ, Integrable (fun y : ℝ => (ε n * annulusK b (j + n) (x - y)) * f y) := by
    intro n
    by_cases hp1 : p = 1
    · have hf1 : MemLp f 1 volume := by
        rw [hp1, ENNReal.ofReal_one] at hf
        exact hf
      have hφ : MemLp (fun y : ℝ => ε n * annulusK b (j + n) (x - y)) ⊤ volume :=
        (annulusSupp_memLp_shifted_annulusK b hsupp hsmooth (j + n) x ⊤).const_mul (ε n)
      exact (memLp_one_iff_integrable.mp hf1).mul_of_top_right hφ
    · have hp1' : 1 < p := lt_of_le_of_ne hp (Ne.symm hp1)
      have hppos : 0 < p := lt_trans zero_lt_one hp1'
      have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1'
      have hqpos : 0 < p.conjExponent := by
        rw [Real.conjExponent]; exact div_pos hppos (by linarith)
      have hk : MemLp (fun y : ℝ => annulusK b (j + n) (x - y))
          (ENNReal.ofReal p.conjExponent) volume :=
        annulusSupp_memLp_shifted_annulusK b hsupp hsmooth (j + n) x _
      have hεk : MemLp (fun y : ℝ => ε n * annulusK b (j + n) (x - y))
          (ENNReal.ofReal p.conjExponent) volume := hk.const_mul (ε n)
      haveI : (ENNReal.ofReal p.conjExponent).HolderTriple (ENNReal.ofReal p) 1 := by
        refine (ENNReal.holderTriple_iff _ _ 1).mpr ?_
        simp only [inv_one]
        rw [← ENNReal.ofReal_inv_of_pos hqpos, ← ENNReal.ofReal_inv_of_pos hppos,
          ← ENNReal.ofReal_add (inv_nonneg.mpr hqpos.le) (inv_nonneg.mpr hppos.le),
          add_comm p.conjExponent⁻¹ p⁻¹, (Real.holderConjugate_iff.mp hpq).2, ENNReal.ofReal_one]
      exact hεk.integrable_mul hf
  have hcongr : (fun y : ℝ =>
        FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y)
      = fun y : ℝ => ∑ n ∈ F, (ε n * annulusK b (j + n) (x - y)) * f y := by
    funext y
    rw [hlin (x - y), Finset.sum_mul]
  have key : (∫ y : ℝ,
        FourierTransformInv.fourierInv (annulusSymbolSum b j F ε) (x - y) * f y)
      = ∑ n ∈ F, ε n * annulusConv b (j + n) f x := by
    rw [hcongr, MeasureTheory.integral_finsetSum F (fun n _ => hInt n)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (fun y : ℝ => (ε n * annulusK b (j + n) (x - y)) * f y)
          = fun y : ℝ => ε n * (annulusK b (j + n) (x - y) * f y) by funext y; ring]
    rw [MeasureTheory.integral_const_mul]
    rfl
  exact key.symm

/-! ## 7. The finite-index-set bound with explicit constants -/

/-- **The `L^p` bound of the annulus square function on finite index sets, with the Mikhlin data
explicit.** -/
theorem annulusSquareLp_finset_explicit {C₀ C₁ C₂ : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂)
    {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℤ → ℝ → ℂ) (hsupp : AnnulusSupp b)
      (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
      (hD0 : ∀ m ξ, ‖b m ξ‖ ≤ C₀)
      (hD1 : ∀ m ξ, ‖deriv (b m) ξ‖ ≤ C₁ * (2 : ℝ) ^ m)
      (hD2 : ∀ m ξ, ‖iteratedDeriv 2 (b m) ξ‖ ≤ C₂ * (2 : ℝ) ^ (2 * m))
      (j : ℤ) (F : Finset ℤ) (f : ℝ → ℂ), MemLp f (ENNReal.ofReal p) volume →
      ∫⁻ x : ℝ, (∑ n ∈ F, ‖annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ≤ ENNReal.ofReal C * ∫⁻ x : ℝ, ‖f x‖ₑ ^ p := by
  obtain ⟨c, hc, hrad⟩ := rademacher_lower_uniform p (le_of_lt hp)
  obtain ⟨Cm, hCm, hmik⟩ := annulusSymbolSum_convolution_le_explicit h₀ h₁ h₂ hp
  refine ⟨c⁻¹ * Cm, mul_pos (inv_pos.mpr hc) hCm, fun b hsupp hsmooth hD0 hD1 hD2 j F f hf => ?_⟩
  classical
  set J : ℝ≥0∞ := ∫⁻ x : ℝ, ‖f x‖ₑ ^ p with hJ
  set coeff : (↥F → Bool) → ℤ → ℂ :=
    fun ε n => if h : n ∈ F then (if ε ⟨n, h⟩ then (1 : ℂ) else -1) else 1 with hcoeff
  have hcoeff_le : ∀ (ε : ↥F → Bool) (n : ℤ), ‖coeff ε n‖ ≤ 1 := by
    intro ε n
    simp only [hcoeff]
    split_ifs <;> simp
  have hpt : ∀ x : ℝ,
      ENNReal.ofReal c * (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ≤ (∑ ε : ↥F → Bool, ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
              * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p)
            * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹ :=
    fun x => hrad (u := fun i : ↥F => annulusConv b (j + (i : ℤ)) f x)
  have hattach : ∀ (ε : ↥F → Bool) (x : ℝ),
      (∑ i : ↥F, (if ε i then (1 : ℂ) else -1) * annulusConv b (j + (i : ℤ)) f x)
        = ∑ n ∈ F, coeff ε n * annulusConv b (j + n) f x := by
    intro ε x
    rw [Finset.univ_eq_attach]
    rw [← Finset.sum_attach F (fun n : ℤ => coeff ε n * annulusConv b (j + n) f x)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [hcoeff]
  have hident : ∀ (ε : ↥F → Bool) (x : ℝ),
      (∑ i : ↥F, (if ε i then (1 : ℂ) else -1) * annulusConv b (j + (i : ℤ)) f x)
        = ∫ y : ℝ,
            FourierTransformInv.fourierInv (annulusSymbolSum b j F (coeff ε)) (x - y) * f y :=
    fun ε x => (hattach ε x).trans
      (annulusSupp_conv_finsetSum_eq b hsupp hsmooth hp.le j F (coeff ε) f hf x)
  have hbound : ∀ ε : ↥F → Bool,
      ∫⁻ x : ℝ, ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
          * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p
        ≤ ENNReal.ofReal Cm * J := by
    intro ε
    calc ∫⁻ x : ℝ, ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
            * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p
        = ∫⁻ x : ℝ, ‖∫ y : ℝ,
              FourierTransformInv.fourierInv (annulusSymbolSum b j F (coeff ε)) (x - y)
                * f y‖ₑ ^ p :=
          lintegral_congr (fun x => by rw [hident ε x])
      _ ≤ ENNReal.ofReal Cm * ∫⁻ x : ℝ, ‖f x‖ₑ ^ p :=
          hmik b hsupp hsmooth hD0 hD1 hD2 j F (coeff ε) (hcoeff_le ε) f hf
      _ = ENNReal.ofReal Cm * J := by rw [hJ]
  have hmeas : ∀ ε : ↥F → Bool, AEMeasurable (fun x : ℝ =>
      ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1) * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p)
      (volume : Measure ℝ) := by
    intro ε
    refine (AEMeasurable.enorm ?_).pow_const p
    refine Finset.aemeasurable_fun_sum (Finset.univ : Finset (↥F)) (fun i _ => ?_)
    exact (aemeasurable_annulusConv b (j + (i : ℤ)) hf.aestronglyMeasurable.aemeasurable
      (aemeasurable_annulusK b (j + (i : ℤ)))).const_mul (if ε i then (1 : ℂ) else -1)
  have hkey : ENNReal.ofReal c * (∫⁻ x : ℝ,
      (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2))
        ≤ ENNReal.ofReal Cm * J := by
    have hD0' : (Fintype.card (↥F → Bool) : ℝ≥0∞) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Fintype.card_ne_zero
    have hDtop : (Fintype.card (↥F → Bool) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [← lintegral_const_mul' (ENNReal.ofReal c) (fun x : ℝ =>
      (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2))
      ENNReal.ofReal_ne_top]
    calc ∫⁻ x : ℝ, ENNReal.ofReal c
          * (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
        ≤ ∫⁻ x : ℝ, (∑ ε : ↥F → Bool, ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
              * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p)
            * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹ :=
          lintegral_mono hpt
      _ = (∑ ε : ↥F → Bool, ∫⁻ x : ℝ, ‖∑ i : ↥F, (if ε i then (1 : ℂ) else -1)
              * annulusConv b (j + (i : ℤ)) f x‖ₑ ^ p)
            * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹ := by
          rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hD0')]
          congr 1
          rw [lintegral_finsetSum' (Finset.univ : Finset (↥F → Bool)) (fun ε _ => hmeas ε)]
      _ ≤ (∑ ε : ↥F → Bool, ENNReal.ofReal Cm * J)
            * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹ :=
          mul_le_mul_left (Finset.sum_le_sum (fun ε _ => hbound ε)) _
      _ = ((Fintype.card (↥F → Bool) : ℝ≥0∞) * (ENNReal.ofReal Cm * J))
            * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ENNReal.ofReal Cm * J := by
          rw [show ((Fintype.card (↥F → Bool) : ℝ≥0∞) * (ENNReal.ofReal Cm * J))
                * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹
              = ((Fintype.card (↥F → Bool) : ℝ≥0∞) * (Fintype.card (↥F → Bool) : ℝ≥0∞)⁻¹)
                * (ENNReal.ofReal Cm * J) by ring,
            ENNReal.mul_inv_cancel hD0' hDtop, one_mul]
  have hI : (∫⁻ x : ℝ,
      (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2))
        ≤ ENNReal.ofReal (c⁻¹ * Cm) * J := by
    have hcne : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc
    have hctop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
    calc (∫⁻ x : ℝ, (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2))
        = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * (∫⁻ x : ℝ,
            (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hcne hctop, one_mul]
      _ ≤ (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal Cm * J) := mul_le_mul_right hkey _
      _ = ENNReal.ofReal (c⁻¹ * Cm) * J := by
          rw [← ENNReal.ofReal_inv_of_pos hc, ← mul_assoc,
            ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc))]
  calc ∫⁻ x : ℝ, (∑ n ∈ F, ‖annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2)
      = ∫⁻ x : ℝ, (∑ i : ↥F, ‖annulusConv b (j + (i : ℤ)) f x‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
        refine lintegral_congr (fun x => ?_)
        congr 1
        exact (Finset.sum_attach F (fun n : ℤ => ‖annulusConv b (j + n) f x‖ₑ ^ (2 : ℝ))).symm
    _ ≤ ENNReal.ofReal (c⁻¹ * Cm) * J := hI
    _ = ENNReal.ofReal (c⁻¹ * Cm) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ p := by rw [hJ]

/-! ## 8. The main uniform statement -/

/-- **`annulusSquareLp` with the Mikhlin data as explicit parameters**, so that the constant is
uniform over the whole family of symbol families satisfying the stated bounds.  This is what the
*shifted* family `m ↦ d (m−j)·φ m` of MST's `(eq:52)` needs: its annulus support, its `C₀` bound and
its `C₁`, `C₂` derivative bounds are uniform in `j` even though `AnnulusSymbolSmooth` of the family
may fail uniformly in `j`.

The hypotheses are the three Mikhlin conditions actually used by `annulusSymbolSum_mikhlin` (only
`k ≤ 2` enters; every other step of the existing chain uses only the annulus support `hb.1` and
`ContDiff ⊤`), in the exact normalisation of `AnnulusSymbolSmooth`: `‖b m ξ‖ ≤ C₀`,
`‖deriv (b m) ξ‖ ≤ C₁ 2^m`, `‖iteratedDeriv 2 (b m) ξ‖ ≤ C₂ 2^{2m}`.  A possible route: restate
`annulusSymbolSum_mikhlin` with the three constants as explicit parameters (its constant is
`A = max (5 C₀) (max (10 C₁) (20 C₂))`, from the 5-fold bounded overlap of the annuli) and restate
`annulusKernel_size`/`annulusSymbolSum_convolution_le` accordingly, then repeat
`annulusSquareLp_finset` with `rademacher_lower_uniform` (Khintchine, uniform in the index type)
and `mikhlinConvolutionLp`, and finish with `annulusSquareLp_of_finset` (monotone convergence along
`[-N,N]`); none of the constants then depends on `b`, `j`, `F` or the signs. -/
theorem annulusSquareLpUniform {C₀ C₁ C₂ : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂)
    {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : ℤ → ℝ → ℂ)
      (hsupp : ∀ m ξ, b m ξ ≠ 0 → (2 : ℝ)⁻¹ < |(2 : ℝ) ^ m * ξ| ∧ |(2 : ℝ) ^ m * ξ| < 2)
      (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
      (hD0 : ∀ m ξ, ‖b m ξ‖ ≤ C₀)
      (hD1 : ∀ m ξ, ‖deriv (b m) ξ‖ ≤ C₁ * (2 : ℝ) ^ m)
      (hD2 : ∀ m ξ, ‖iteratedDeriv 2 (b m) ξ‖ ≤ C₂ * (2 : ℝ) ^ (2 * m))
      (j : ℤ) (f : ℝ → ℂ), MeasureTheory.MemLp f (ENNReal.ofReal p)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ∫⁻ x, (annulusSqfun b j f x) ^ p
        ≤ ENNReal.ofReal C * ∫⁻ x, ‖f x‖ₑ ^ p := by
  obtain ⟨C, hC, hfin⟩ := annulusSquareLp_finset_explicit h₀ h₁ h₂ hp
  refine ⟨C, hC, fun b hsupp hsmooth hD0 hD1 hD2 j f hf => ?_⟩
  exact annulusSquareLp_of_finset (lt_trans zero_lt_one hp)
    (fun j F f hf => hfin b hsupp hsmooth hD0 hD1 hD2 j F f hf) j f hf

end Work.BourgainPlan.Maximal
