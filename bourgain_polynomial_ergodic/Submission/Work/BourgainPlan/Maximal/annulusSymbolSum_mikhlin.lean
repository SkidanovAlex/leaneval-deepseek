import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSymbol_tsum_sq_le

/-!
# The Mikhlin constants of the signed annulus symbol sums

This module isolates the two structural properties of the annulus symbol family `b`
(`AnnulusSymbolSmooth b`, plus `C^∞` smoothness of each member) that make the *signed sums*

  `annulusSymbolSum b j F ε = ∑_{n ∈ F} ε n · b (j + n)`

Mikhlin symbols with a constant **uniform in `j`, in the finite index set `F` and in the
coefficients `ε n` with `‖ε n‖ ≤ 1`**:

* the annuli are `2⁻¹ < |2^m ξ| < 2`, so at a fixed frequency `ξ` at most boundedly many levels
  `m = j + n` carry a non-zero *value or derivative*: the derivative `iteratedDeriv k (b m)`
  vanishes outside the (topological) support of `b m`, which lies in the closed annulus
  `2⁻¹ ≤ |2^m ξ| ≤ 2`, and those annuli have overlap at most `5` (two levels that both meet `ξ`
  differ by at most `2`).  Hence the three Mikhlin bounds

  `‖Θ ξ‖ ≤ A`,  `|ξ| ‖deriv Θ ξ‖ ≤ A`,  `|ξ|² ‖iteratedDeriv 2 Θ ξ‖ ≤ A`

  hold with `A = max (5 C₀) (max (10 C₁) (20 C₂))`, where `C_k` is the `k`-th derivative constant
  of `AnnulusSymbolSmooth`.

This is the pointwise input of the randomisation proof of the `L^p` bound for the annulus square
function: the signed sum `∑_{n∈F} ε n · K_{j+n}` is the convolution kernel of a Mikhlin multiplier
with the *same* constant for every sign vector, so Khintchine/Marcinkiewicz–Zygmund transfers the
uniform-in-signs `L^p` bound to the square function with a constant independent of the number of
scales.

## Contents

* `annulusSymbolSum` — the signed symbol sum, as a `Finset`-sum of functions (so that
  `ContDiff.sum` and `iteratedDeriv_sum` apply syntactically);
* `iteratedDeriv_eq_zero_of_notMem_tsupport` — every iterated derivative vanishes off the
  topological support;
* `tsupport_abs_bounds` — the topological support of `b m` lies in the closed annulus;
* `zpow_sub_le_two` — two levels meeting `ξ` differ by at most `2`;
* `card_filter_iteratedDeriv_le` — at most `5` levels carry a non-zero `k`-th derivative;
* `annulusSymbolSum_iteratedDeriv` / `annulusSymbolSum_contDiff` — differentiation and smoothness;
* `annulusSymbolSum_iteratedDeriv_bound` — the `k`-th Mikhlin bound with constant `5 · 2^k · C_k`;
* **`annulusSymbolSum_mikhlin`** — the three Mikhlin bounds with the uniform constant.
-/

open scoped BigOperators

namespace Work.BourgainPlan.Maximal

/-- The signed sum of the annulus symbols at the levels `j + n` for `n ∈ F`. -/
noncomputable def annulusSymbolSum (b : ℤ → ℝ → ℂ) (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) :
    ℝ → ℂ :=
  fun ξ => ∑ n ∈ F, ε n * b (j + n) ξ

/-- The pointwise form of `annulusSymbolSum`. -/
lemma annulusSymbolSum_apply (b : ℤ → ℝ → ℂ) (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) (ξ : ℝ) :
    annulusSymbolSum b j F ε ξ = ∑ n ∈ F, ε n * b (j + n) ξ := rfl

/-- `annulusSymbolSum` as a `Finset`-sum *of functions* (the form in which
`iteratedDeriv_sum` applies). -/
lemma annulusSymbolSum_eq_sum_functions (b : ℤ → ℝ → ℂ) (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) :
    annulusSymbolSum b j F ε = ∑ n ∈ F, fun ξ : ℝ => ε n * b (j + n) ξ := by
  funext ξ
  rw [Finset.sum_apply]
  rfl

/-- **Off the topological support every iterated derivative vanishes.** -/
lemma iteratedDeriv_eq_zero_of_notMem_tsupport {f : ℝ → ℂ} {k : ℕ} {x : ℝ}
    (h : x ∉ tsupport f) : iteratedDeriv k f x = 0 := by
  have hcl : ((closure (Function.support f))ᶜ : Set ℝ) ∈ nhds x :=
    isClosed_closure.isOpen_compl.mem_nhds h
  have hev : f =ᶠ[nhds x] (0 : ℝ → ℂ) := by
    filter_upwards [hcl] with y hy
    by_contra hfy
    exact hy (subset_closure (Function.mem_support.mpr hfy))
  rw [hev.iteratedDeriv_eq k]
  rw [show (0 : ℝ → ℂ) = fun _ : ℝ => (0 : ℂ) from rfl, iteratedDeriv_const]
  split_ifs <;> rfl

/-- **The topological support of `b m` lies in the closed annulus `2⁻¹ ≤ |2^m ξ| ≤ 2`.** -/
lemma tsupport_abs_bounds (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b) (m : ℤ) {ξ : ℝ}
    (hξ : ξ ∈ tsupport (b m)) :
    (2 : ℝ)⁻¹ ≤ |(2 : ℝ) ^ m * ξ| ∧ |(2 : ℝ) ^ m * ξ| ≤ 2 := by
  have hcont : Continuous fun y : ℝ => |(2 : ℝ) ^ m * y| :=
    continuous_abs.comp (continuous_const.mul continuous_id)
  have hclosed : IsClosed ((fun y : ℝ => |(2 : ℝ) ^ m * y|) ⁻¹' Set.Icc (2 : ℝ)⁻¹ 2) :=
    isClosed_Icc.preimage hcont
  have hsub : Function.support (b m) ⊆
      (fun y : ℝ => |(2 : ℝ) ^ m * y|) ⁻¹' Set.Icc (2 : ℝ)⁻¹ 2 := by
    intro y hy
    obtain ⟨h1, h2⟩ := hb.1 m y (Function.mem_support.mp hy)
    exact ⟨le_of_lt h1, le_of_lt h2⟩
  have := (IsClosed.closure_subset_iff hclosed).mpr hsub hξ
  simpa [Set.mem_Icc] using this

/-- **Two levels meeting `ξ` differ by at most `2`:** `2^{m'-m} = |2^{m'}ξ| / |2^mξ| ≤ 2/(1/2) = 4`. -/
lemma zpow_sub_le_two {m m' : ℤ} {v : ℝ} (hm : (2 : ℝ)⁻¹ ≤ |(2 : ℝ) ^ m * v|)
    (hm' : |(2 : ℝ) ^ m' * v| ≤ 2) : m' - m ≤ 2 := by
  have hpow : (2 : ℝ) ^ (m' - m) * (2 : ℝ) ^ m = (2 : ℝ) ^ m' := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), sub_add_cancel]
  have hkey : (2 : ℝ) ^ (m' - m) * |(2 : ℝ) ^ m * v| = |(2 : ℝ) ^ m' * v| := by
    rw [← abs_of_pos (zpow_pos (by norm_num : (0:ℝ) < 2) (m' - m)), ← abs_mul, ← mul_assoc, hpow]
  have h4 : (2 : ℝ) ^ (m' - m) * (2 : ℝ)⁻¹ ≤ 2 := by
    calc (2 : ℝ) ^ (m' - m) * (2 : ℝ)⁻¹
        ≤ (2 : ℝ) ^ (m' - m) * |(2 : ℝ) ^ m * v| :=
          mul_le_mul_of_nonneg_left hm (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
      _ = |(2 : ℝ) ^ m' * v| := hkey
      _ ≤ 2 := hm'
  by_contra hcon
  push Not at hcon
  have h3 : (3 : ℤ) ≤ m' - m := by omega
  have hpow : (2 : ℝ) ^ (3 : ℤ) ≤ (2 : ℝ) ^ (m' - m) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h3
  have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (m' - m) := by
    have h83 : ((2 : ℝ) ^ (3 : ℤ)) = 8 := by norm_num
    linarith [hpow, h83.le, h83.ge]
  nlinarith [h4, h8]

/-- **At most five levels carry a non-zero `k`-th derivative.** -/
lemma card_filter_iteratedDeriv_le (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (j : ℤ) (ξ : ℝ) (F : Finset ℤ) (k : ℕ) :
    (F.filter (fun n => iteratedDeriv k (b (j + n)) ξ ≠ 0)).card ≤ 5 := by
  by_cases hex : ∃ n ∈ F, iteratedDeriv k (b (j + n)) ξ ≠ 0
  · obtain ⟨n₀, hn₀F, hn₀⟩ := hex
    have hts₀ : ξ ∈ tsupport (b (j + n₀)) := by
      by_contra hmem
      exact hn₀ (iteratedDeriv_eq_zero_of_notMem_tsupport hmem)
    obtain ⟨hlo₀, hhi₀⟩ := tsupport_abs_bounds b hb (j + n₀) hts₀
    have hbound : ∀ n ∈ F, iteratedDeriv k (b (j + n)) ξ ≠ 0 →
        n ∈ Finset.Icc (n₀ - 2) (n₀ + 2) := by
      intro n hnF hn
      have hts : ξ ∈ tsupport (b (j + n)) := by
        by_contra hmem
        exact hn (iteratedDeriv_eq_zero_of_notMem_tsupport hmem)
      obtain ⟨hlo, hhi⟩ := tsupport_abs_bounds b hb (j + n) hts
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

/-- **The `k`-th derivative of a signed sum is the signed sum of the `k`-th derivatives.** -/
lemma annulusSymbolSum_iteratedDeriv (b : ℤ → ℝ → ℂ)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) (k : ℕ) (ξ : ℝ) :
    iteratedDeriv k (annulusSymbolSum b j F ε) ξ
      = ∑ n ∈ F, ε n * iteratedDeriv k (b (j + n)) ξ := by
  have hcd : ∀ n ∈ F, ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun ξ : ℝ => ε n * b (j + n) ξ) ξ := by
    intro n hn
    exact contDiffAt_const.mul (((hsmooth (j + n)).contDiffAt).of_le
      (WithTop.coe_le_coe.mpr le_top))
  have hsum := iteratedDeriv_sum (𝕜 := ℝ) (x := ξ) (I := F)
    (f := fun n : ℤ => fun ξ : ℝ => ε n * b (j + n) ξ) hcd
  rw [annulusSymbolSum_eq_sum_functions b j F ε, hsum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  exact iteratedDeriv_const_mul (ε n) (((hsmooth (j + n)).contDiffAt).of_le
    (WithTop.coe_le_coe.mpr le_top))

/-- **The signed symbol sum is `C²`.** -/
lemma annulusSymbolSum_contDiff (b : ℤ → ℝ → ℂ)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) : ContDiff ℝ 2 (annulusSymbolSum b j F ε) := by
  unfold annulusSymbolSum
  refine ContDiff.sum (f := fun n : ℤ => fun ξ : ℝ => ε n * b (j + n) ξ) (fun n hn => ?_)
  have h1 : ContDiff ℝ ((2:ℕ∞):WithTop ℕ∞) (fun _ : ℝ => ε n) := contDiff_const
  have h2 : ContDiff ℝ ((2:ℕ∞):WithTop ℕ∞) (b (j + n)) :=
    (hsmooth (j + n)).of_le (WithTop.coe_le_coe.mpr le_top)
  exact h1.mul h2

/-- **The `k`-th Mikhlin bound.**  If the `k`-th derivative of each `b m` is bounded by
`C · (2^m)^k`, then the same bound holds for the signed sum, with the extra factor `5 · 2^k`
coming from the bounded overlap of the annuli (at most five levels, each contributing at most
`C · 2^k`). -/
lemma annulusSymbolSum_iteratedDeriv_bound (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m))
    (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ) (hε : ∀ n, ‖ε n‖ ≤ 1)
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hCb : ∀ (m : ℤ) (ξ : ℝ), ‖iteratedDeriv k (b m) ξ‖ ≤ C * ((2 : ℝ) ^ m) ^ k)
    (ξ : ℝ) :
    |ξ| ^ k * ‖iteratedDeriv k (annulusSymbolSum b j F ε) ξ‖ ≤ 5 * (2 : ℝ) ^ k * C := by
  classical
  set S : Finset ℤ := F.filter (fun n => iteratedDeriv k (b (j + n)) ξ ≠ 0) with hSdef
  have hcard : S.card ≤ 5 := card_filter_iteratedDeriv_le b hb j ξ F k
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
    obtain ⟨hlo, hhi⟩ := tsupport_abs_bounds b hb (j + n) hts
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

/-- **The three Mikhlin bounds for the signed annulus symbol sums, uniformly in the signs, in the
finite index set and in the base scale.** -/
theorem annulusSymbolSum_mikhlin (b : ℤ → ℝ → ℂ) (hb : AnnulusSymbolSmooth b)
    (hsmooth : ∀ m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b m)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (j : ℤ) (F : Finset ℤ) (ε : ℤ → ℂ), (∀ n, ‖ε n‖ ≤ 1) →
      (∀ ξ : ℝ, ‖annulusSymbolSum b j F ε ξ‖ ≤ A) ∧
      (∀ ξ : ℝ, |ξ| * ‖deriv (annulusSymbolSum b j F ε) ξ‖ ≤ A) ∧
      (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 (annulusSymbolSum b j F ε) ξ‖ ≤ A) := by
  obtain ⟨C₀, hC₀, hb₀⟩ := hb.2 0
  obtain ⟨C₁, hC₁, hb₁⟩ := hb.2 1
  obtain ⟨C₂, hC₂, hb₂⟩ := hb.2 2
  refine ⟨max (5 * (2 : ℝ) ^ 0 * C₀) (max (5 * (2 : ℝ) ^ 1 * C₁) (5 * (2 : ℝ) ^ 2 * C₂)),
    ?_, fun j F ε hε => ⟨?_, ?_, ?_⟩⟩
  · refine le_trans ?_ (le_max_left _ _)
    have h : (2 : ℝ) ^ 0 = 1 := pow_zero 2
    rw [h]; nlinarith [hC₀]
  · intro ξ
    have hkey := annulusSymbolSum_iteratedDeriv_bound b hb hsmooth j F ε hε 0 C₀ hC₀
      (fun m ξ => by simpa using hb₀ m ξ) ξ
    refine le_trans ?_ (le_max_left _ _)
    simpa using hkey
  · intro ξ
    have hkey := annulusSymbolSum_iteratedDeriv_bound b hb hsmooth j F ε hε 1 C₁ hC₁
      (fun m ξ => by simpa [mul_one, pow_one] using hb₁ m ξ) ξ
    refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_right _ _))
    simpa [iteratedDeriv_one, pow_one] using hkey
  · intro ξ
    have hkey := annulusSymbolSum_iteratedDeriv_bound b hb hsmooth j F ε hε 2 C₂ hC₂
      (fun m ξ => by simpa [zpow_mul, zpow_natCast] using hb₂ m ξ) ξ
    refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_right _ _))
    simpa using hkey

end Work.BourgainPlan.Maximal
