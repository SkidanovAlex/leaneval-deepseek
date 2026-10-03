/-
  Companion paper ("Asymptotic sieve for primes"), §7 (`S₂`): the assembly of (7.1)–(7.2).

  This file combines the pointwise expansion `Ksum_abs_le_merge` (S7b) with the smoothed
  dyadic estimate `smAvg_Bint_le` (S7d) to bound the *averaged* sum

      `∫_Y^{eY} (∑_{k ≤ N} |Ksum_k(y)|) dy/y`

  by the bilinear hypothesis (B′).  The smoothing over `y ∈ [Y,eY]` (total mass `1`) is what
  allows the divisor `ν₁ ≤ Δ` to be removed from the range of the inner `b`-sum: after the
  substitution `y = ν₁ u` the window becomes `[Y/ν₁, eY/ν₁] ⊆ [Y/Δ, eY]`, and the triples
  `(ν₁,k,ν₂)` are merged along `ℓ = ν₁k` with multiplicity `≤ τ(ℓ)² ≤ w(ℓ)`.
-/
import Mathlib
import Submission.ASP.S7d
import Submission.ASP.S7b

namespace Submission.ASP

open Finset MeasureTheory
open scoped Interval

noncomputable section

/-! ### The objects -/

/-- The `ν₁`-fibre of the merged sum: `∑_k ∑_{ν₂ | k} |λ_{ν₁ν₂}|·|Xsum (ν₁k) w (s w)|`. -/
def Kfac (a lam : ℕ → ℝ) (N : ℕ) (s : ℝ) (ν₁ : ℕ) (w : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
    |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) w (s * w)|

/-- The merged sum at the scale `w`. -/
def Kmerge (a lam : ℕ → ℝ) (N : ℕ) (s : ℝ) (Δ : ℕ) (w : ℝ) : ℝ :=
  ∑ ν₁ ∈ Finset.Icc 1 Δ, Kfac a lam N s ν₁ w

/-- The same, with the fibre scaled: `y ↦ Kfac ν₁ (y/ν₁)` (the range after the substitution). -/
def KmergeD (a lam : ℕ → ℝ) (N : ℕ) (s : ℝ) (Δ : ℕ) (y : ℝ) : ℝ :=
  ∑ ν₁ ∈ Finset.Icc 1 Δ, Kfac a lam N s ν₁ (y / ν₁)

/-! ### Measurability and integrability -/

lemma measurable_Kfac (a lam : ℕ → ℝ) (N : ℕ) {s : ℝ} (hs : 0 < s) (ν₁ : ℕ) :
    Measurable (Kfac a lam N s ν₁) := by
  have h : Kfac a lam N s ν₁
      = fun w => ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
          |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) w (s * w)| := rfl
  rw [h]
  refine Finset.measurable_sum _ (fun k _ => Finset.measurable_sum _ (fun ν₂ _ => ?_))
  exact (measurable_Xsum a N (ν₁ * k) hs).abs.const_mul _

lemma measurable_KmergeD (a lam : ℕ → ℝ) (N : ℕ) {s : ℝ} (hs : 0 < s) (Δ : ℕ) :
    Measurable (KmergeD a lam N s Δ) := by
  have h : KmergeD a lam N s Δ = fun y => ∑ ν₁ ∈ Finset.Icc 1 Δ,
      Kfac a lam N s ν₁ (y / ν₁) := rfl
  rw [h]
  refine Finset.measurable_sum _ (fun ν₁ _ => ?_)
  exact (measurable_Kfac a lam N hs ν₁).comp (measurable_id.div_const _)

/-- A uniform bound for the `ν₁`-fibre. -/
def KfacBound (a : ℕ → ℝ) (N : ℕ) (ν₁ : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, ∑ _ν₂ ∈ k.divisors, ∑ b ∈ Finset.Icc 1 N, |a (b * (ν₁ * k))|

lemma abs_Kfac_le (a lam : ℕ → ℝ) (N : ℕ) (s : ℝ) (ν₁ : ℕ) (w : ℝ)
    (hlam_le1 : ∀ ν, |lam ν| ≤ 1) :
    |Kfac a lam N s ν₁ w| ≤ KfacBound a N ν₁ := by
  rw [Kfac, KfacBound]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ν₂ _ => ?_))
  rw [abs_mul, abs_abs, abs_abs]
  calc |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) w (s * w)|
      ≤ 1 * |Xsum a N (ν₁ * k) w (s * w)| :=
        mul_le_mul_of_nonneg_right (hlam_le1 _) (abs_nonneg _)
    _ = |Xsum a N (ν₁ * k) w (s * w)| := one_mul _
    _ ≤ ∑ b ∈ Finset.Icc 1 N, |a (b * (ν₁ * k))| := abs_Xsum_le a N (ν₁ * k) w (s * w)

lemma abs_KmergeD_le (a lam : ℕ → ℝ) (N : ℕ) (s : ℝ) (Δ : ℕ) (y : ℝ)
    (hlam_le1 : ∀ ν, |lam ν| ≤ 1) :
    |KmergeD a lam N s Δ y| ≤ ∑ ν₁ ∈ Finset.Icc 1 Δ, KfacBound a N ν₁ := by
  simp only [KmergeD]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ν₁ _ => ?_))
  exact abs_Kfac_le a lam N s ν₁ (y / ν₁) hlam_le1

lemma intervalIntegrable_KmergeD_div (a lam : ℕ → ℝ) (N : ℕ) {s : ℝ} (hs : 0 < s) (Δ : ℕ)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hlam_le1 : ∀ ν, |lam ν| ≤ 1) :
    IntervalIntegrable (fun y => KmergeD a lam N s Δ y / y) volume p q :=
  intervalIntegrable_div_of_bound hp hpq (measurable_KmergeD a lam N hs Δ) _
    (fun y => abs_KmergeD_le a lam N s Δ y hlam_le1)

lemma intervalIntegrable_Kfac_div (a lam : ℕ → ℝ) (N : ℕ) {s : ℝ} (hs : 0 < s) (ν₁ : ℕ)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hlam_le1 : ∀ ν, |lam ν| ≤ 1) :
    IntervalIntegrable (fun y => Kfac a lam N s ν₁ y / y) volume p q :=
  intervalIntegrable_div_of_bound hp hpq (measurable_Kfac a lam N hs ν₁) _
    (fun y => abs_Kfac_le a lam N s ν₁ y hlam_le1)

lemma intervalIntegrable_Kfac_div_div (a lam : ℕ → ℝ) (N : ℕ) {s : ℝ} (hs : 0 < s) (ν₁ : ℕ)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hlam_le1 : ∀ ν, |lam ν| ≤ 1) :
    IntervalIntegrable (fun y => Kfac a lam N s ν₁ (y / ν₁) / y) volume p q :=
  intervalIntegrable_div_of_bound hp hpq
    ((measurable_Kfac a lam N hs ν₁).comp (measurable_id.div_const _)) _
    (fun y => abs_Kfac_le a lam N s ν₁ (y / ν₁) hlam_le1)

/-! ### Nonnegativity -/

lemma Kfac_nonneg (a lam : ℕ → ℝ) (N : ℕ) (s : ℝ) (ν₁ : ℕ) (w : ℝ) :
    0 ≤ Kfac a lam N s ν₁ w :=
  Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))

lemma KmergeD_nonneg (a lam : ℕ → ℝ) (N : ℕ) (s : ℝ) (Δ : ℕ) (y : ℝ) :
    0 ≤ KmergeD a lam N s Δ y :=
  Finset.sum_nonneg (fun _ _ => Kfac_nonneg a lam N s _ _)

/-- `Ksum` vanishes when the upper end of the `b`-range is nonpositive. -/
lemma Ksum_eq_zero_of_sy_nonpos (a lam : ℕ → ℝ) (N k : ℕ) (y sy : ℝ) (hsy : sy ≤ 0) :
    Ksum a lam N y sy k = 0 := by
  rw [Ksum, Krange]
  refine Finset.sum_eq_zero (fun b hb => ?_)
  obtain ⟨hb1, -⟩ := Finset.mem_filter.mp hb
  have hbge : (1 : ℝ) ≤ (b : ℝ) := by
    have h := (Finset.mem_Icc.mp hb1).1
    exact_mod_cast h
  have hbsy : ((b : ℕ) : ℝ) ≤ sy := (Finset.mem_filter.mp hb).2.2.1
  linarith

/-! ### §7 (7.1)–(7.2) -/

/-- **§7, the smoothed estimate**: the `y`-average of `∑_k |Ksum_k(y)|` is bounded by (B′).

Hypotheses: `s = 2^J`; `λ` is supported on `[1,Δ]` with `|λ| ≤ 1`; `a` is supported on the
squarefree integers; `w(ℓ) ≥ τ(ℓ)²`; and (B′) holds on the window `[Y/Δ, s·e·Y]`.
The conclusion carries the factor `1 + log Δ` coming from extending the windows
`[Y/ν₁, e·Y/ν₁] ⊆ [Y/Δ, e·Y]`. -/
theorem smAvg_abs_Ksum_le (a lam : ℕ → ℝ) (N : ℕ) {w : ℕ → ℝ} {s E Y : ℝ} {J : ℕ} {Δ : ℕ}
    (hs : s = (2 : ℝ) ^ J) (hY : 0 < Y) (hΔ : 1 ≤ Δ) (_hw0 : ∀ ℓ, 0 ≤ w ℓ) (hE : 0 ≤ E)
    (hw : ∀ ℓ, 1 ≤ ℓ → ((ℓ.divisors.card : ℝ)) ^ 2 ≤ w ℓ)
    (hlam_supp : ∀ ν, Δ < ν → lam ν = 0)
    (hlam_le1 : ∀ ν, |lam ν| ≤ 1)
    (ha : ∀ n, ¬ Squarefree n → a n = 0)
    (hB : BprimeWindow a N w E (Y / (Δ : ℝ)) (s * (Real.exp 1 * Y))) :
    (∫ y in Y..(Real.exp 1 * Y), (∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k|) / y)
      ≤ (J : ℝ) * (E * (1 + Real.log (Δ : ℝ))) := by
  have hspos : 0 < s := by rw [hs]; positivity
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hApos : 0 < Y / (Δ : ℝ) := div_pos hY hΔpos
  have heY : 0 < Real.exp 1 * Y := mul_pos (Real.exp_pos 1) hY
  have hYle : Y ≤ Real.exp 1 * Y := by
    simpa using mul_le_mul_of_nonneg_right
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) hY.le
  have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)
  have hAeY : Y / (Δ : ℝ) ≤ Real.exp 1 * Y :=
    le_trans (by rw [div_le_iff₀ hΔpos]; nlinarith [hY.le, hΔ1, he1]) hYle
  have hB' : BprimeWindow a N w E (Y / (Δ : ℝ)) ((2 : ℝ) ^ J * (Real.exp 1 * Y)) := by
    rwa [hs] at hB
  have htw : ∀ (j : ℕ) (u : ℝ), (2 : ℝ) ^ (j + 1) * u = 2 * ((2 : ℝ) ^ j * u) := by
    intro j u; rw [pow_succ]; ring
  -- ## the pointwise bound `∑_k |Ksum_k| ≤ KmergeD`
  have hpt : ∀ y : ℝ,
      (∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k|) ≤ KmergeD a lam N s Δ y := by
    intro y
    by_cases hy : 0 < y
    · have h1 : (∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k|)
          ≤ ∑ k ∈ Finset.Icc 1 N, ∑ ν₁ ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
              |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) (y / ν₁) (s * y / ν₁)| :=
        Finset.sum_le_sum (fun k hk => Ksum_abs_le_merge a lam N k y (s * y) hy
          (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2 ha)
      rw [Finset.sum_comm] at h1
      have hGzero : ∀ x : ℕ, Δ < x → (∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
            |lam (x * ν₂)| * |Xsum a N (x * k) (y / x) (s * y / x)|) = 0 := by
        intro x hx
        refine Finset.sum_eq_zero (fun k hk => Finset.sum_eq_zero (fun ν₂ hν₂ => ?_))
        have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
        have hν₂1 : 1 ≤ ν₂ :=
          Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hν₂).1 (Nat.pos_of_ne_zero hk0)
        have hlt : Δ < x * ν₂ :=
          calc Δ < x := hx
            _ = x * 1 := (mul_one _).symm
            _ ≤ x * ν₂ := Nat.mul_le_mul_left x hν₂1
        rw [hlam_supp (x * ν₂) hlt, abs_zero, zero_mul]
      have hsub1 : Finset.Icc 1 (min N Δ) ⊆ Finset.Icc 1 N := fun x hx => by
        rw [Finset.mem_Icc] at hx ⊢
        exact ⟨hx.1, le_trans hx.2 (min_le_left _ _)⟩
      have hsub2 : Finset.Icc 1 (min N Δ) ⊆ Finset.Icc 1 Δ := fun x hx => by
        rw [Finset.mem_Icc] at hx ⊢
        exact ⟨hx.1, le_trans hx.2 (min_le_right _ _)⟩
      have hzero' : ∀ x ∈ Finset.Icc 1 N, x ∉ Finset.Icc 1 (min N Δ) →
          (∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
            |lam (x * ν₂)| * |Xsum a N (x * k) (y / x) (s * y / x)|) = 0 := by
        intro x hx hxs
        rw [Finset.mem_Icc] at hx
        refine hGzero x ?_
        by_contra hcon
        rw [not_lt] at hcon
        exact hxs (Finset.mem_Icc.mpr ⟨hx.1, le_min hx.2 hcon⟩)
      have h2 : (∑ ν₁ ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
              |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) (y / ν₁) (s * y / ν₁)|)
          ≤ ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
              |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) (y / ν₁) (s * y / ν₁)| := by
        have heq : (∑ ν₁ ∈ Finset.Icc 1 (min N Δ), ∑ k ∈ Finset.Icc 1 N,
              ∑ ν₂ ∈ k.divisors,
              |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) (y / ν₁) (s * y / ν₁)|)
            = ∑ ν₁ ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
              |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) (y / ν₁) (s * y / ν₁)| :=
          Finset.sum_subset hsub1 hzero'
        rw [← heq]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun x _ _ =>
          Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _))))
      refine h1.trans (h2.trans ?_)
      simp only [KmergeD, Kfac]
      refine Finset.sum_le_sum (fun ν₁ _ => Finset.sum_le_sum (fun k _ =>
        Finset.sum_le_sum (fun ν₂ _ => ?_)))
      rw [mul_div_assoc]
    · have hy' : y ≤ 0 := not_lt.mp hy
      have hzero : ∀ k, Ksum a lam N y (s * y) k = 0 := fun k =>
        Ksum_eq_zero_of_sy_nonpos a lam N k y (s * y)
          (mul_nonpos_of_nonneg_of_nonpos hspos.le hy')
      rw [Finset.sum_eq_zero (fun k _ => by rw [hzero k, abs_zero])]
      exact KmergeD_nonneg a lam N s Δ y
  -- ## Step A: integrate the pointwise bound
  have stepA : (∫ y in Y..(Real.exp 1 * Y),
        (∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k|) / y)
      ≤ ∫ y in Y..(Real.exp 1 * Y), KmergeD a lam N s Δ y / y := by
    rw [intervalIntegral.integral_of_le hYle, intervalIntegral.integral_of_le hYle]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · change ∀ᵐ y ∂(volume.restrict (Set.Ioc Y (Real.exp 1 * Y))),
          (0 : ℝ) ≤ (∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k|) / y
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun y hy =>
        div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
          (le_of_lt (lt_trans hY hy.1)))
    · exact (intervalIntegrable_KmergeD_div a lam N hspos Δ hY hYle hlam_le1).1
    · change ∀ᵐ y ∂(volume.restrict (Set.Ioc Y (Real.exp 1 * Y))),
          (∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k|) / y
            ≤ KmergeD a lam N s Δ y / y
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun y hy =>
        div_le_div_of_nonneg_right (hpt y) (le_of_lt (lt_trans hY hy.1)))
  -- ## Step B: pull out `ν₁`, substitute, extend, pull back
  have stepB : (∫ y in Y..(Real.exp 1 * Y), KmergeD a lam N s Δ y / y)
      ≤ ∫ w in Y / (Δ : ℝ)..(Real.exp 1 * Y), Kmerge a lam N s Δ w / w := by
    have h1 : (∫ y in Y..(Real.exp 1 * Y), KmergeD a lam N s Δ y / y)
        = ∑ ν₁ ∈ Finset.Icc 1 Δ,
            ∫ y in Y..(Real.exp 1 * Y), Kfac a lam N s ν₁ (y / ν₁) / y := by
      rw [show (∫ y in Y..(Real.exp 1 * Y), KmergeD a lam N s Δ y / y)
          = ∫ y in Y..(Real.exp 1 * Y),
              ∑ ν₁ ∈ Finset.Icc 1 Δ, Kfac a lam N s ν₁ (y / ν₁) / y from
        intervalIntegral.integral_congr (fun y _ => by
          simp only [KmergeD, Finset.sum_div])]
      exact intervalIntegral.integral_finsetSum
        (fun ν₁ _ => intervalIntegrable_Kfac_div_div a lam N hspos ν₁ hY hYle hlam_le1)
    rw [h1]
    have h2 : ∀ ν₁ ∈ Finset.Icc 1 Δ,
        (∫ y in Y..(Real.exp 1 * Y), Kfac a lam N s ν₁ (y / ν₁) / y)
          ≤ ∫ w in Y / (Δ : ℝ)..(Real.exp 1 * Y), Kfac a lam N s ν₁ w / w := by
      intro ν₁ hν₁
      obtain ⟨hν₁1, hν₁Δ⟩ := Finset.mem_Icc.mp hν₁
      have hν₁pos : (0 : ℝ) < (ν₁ : ℝ) := by exact_mod_cast (by omega : 0 < ν₁)
      have hν₁1' : (1 : ℝ) ≤ (ν₁ : ℝ) := by exact_mod_cast hν₁1
      have hν₁Δ' : (ν₁ : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hν₁Δ
      rw [integral_comp_div_div_div (Φ := Kfac a lam N s ν₁) hν₁pos Y (Real.exp 1 * Y)]
      refine intervalIntegral.integral_mono_interval ?_ ?_ ?_ ?_ ?_
      · rw [div_le_div_iff₀ hΔpos hν₁pos]; nlinarith [hY.le, hν₁Δ']
      · exact div_le_div_of_nonneg_right hYle hν₁pos.le
      · rw [div_le_iff₀ hν₁pos]; nlinarith [heY.le, hν₁1']
      · change ∀ᵐ w ∂(volume.restrict (Set.Ioc (Y / (Δ : ℝ)) (Real.exp 1 * Y))),
            (0 : ℝ) ≤ Kfac a lam N s ν₁ w / w
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall (fun w hw =>
          div_nonneg (Kfac_nonneg a lam N s ν₁ w) (le_of_lt (lt_trans hApos hw.1)))
      · exact intervalIntegrable_Kfac_div a lam N hspos ν₁ hApos hAeY hlam_le1
    refine (Finset.sum_le_sum h2).trans (le_of_eq ?_)
    rw [show (∫ w in Y / (Δ : ℝ)..(Real.exp 1 * Y), Kmerge a lam N s Δ w / w)
        = ∫ w in Y / (Δ : ℝ)..(Real.exp 1 * Y),
            ∑ ν₁ ∈ Finset.Icc 1 Δ, Kfac a lam N s ν₁ w / w from
      intervalIntegral.integral_congr (fun w _ => by
        simp only [Kmerge, Finset.sum_div])]
    exact (intervalIntegral.integral_finsetSum
      (fun ν₁ _ => intervalIntegrable_Kfac_div a lam N hspos ν₁ hApos hAeY hlam_le1)).symm
  -- ## Step C: the dyadic split and (B′)
  have hKmerge : ∀ z : ℝ, Kmerge a lam N s Δ z
      ≤ ∑ j ∈ Finset.range J, Bint a N w ((2 : ℝ) ^ j * z) := by
    intro z
    rw [hs]
    simp only [Kmerge, Kfac, Bint]
    have hperm1 : (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
          ∑ j ∈ Finset.range J,
            |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|)
        = ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range J,
          ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| :=
      Finset.sum_congr rfl (fun ν₁ _ => Finset.sum_congr rfl (fun k _ => Finset.sum_comm))
    have hperm2 : (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range J,
          ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|)
        = ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.Icc 1 N,
          ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| :=
      Finset.sum_congr rfl (fun ν₁ _ => Finset.sum_comm)
    have hperm3 : (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.Icc 1 N,
          ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)|)
        = ∑ j ∈ Finset.range J, ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N,
          ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| :=
      Finset.sum_comm
    calc ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) z ((2 : ℝ) ^ J * z)|
        ≤ ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
            |lam (ν₁ * ν₂)| * ∑ j ∈ Finset.range J,
              |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| :=
          Finset.sum_le_sum (fun ν₁ _ => Finset.sum_le_sum (fun k _ =>
            Finset.sum_le_sum (fun ν₂ _ => mul_le_mul_of_nonneg_left
              (Xsum_abs_dyadic_le a N (ν₁ * k) J z) (abs_nonneg _))))
      _ = ∑ j ∈ Finset.range J, ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N,
            ∑ ν₂ ∈ k.divisors,
              |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) ((2 : ℝ) ^ j * z) ((2 : ℝ) ^ (j + 1) * z)| := by
          simp_rw [Finset.mul_sum]
          exact hperm1.trans (hperm2.trans hperm3)
      _ ≤ ∑ j ∈ Finset.range J, ∑ ℓ ∈ Finset.Icc 1 N,
            w ℓ * |Xsum a N ℓ ((2 : ℝ) ^ j * z) (2 * ((2 : ℝ) ^ j * z))| := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          refine (le_of_eq ?_).trans
            (sum_merge_le_Icc a lam w N Δ ((2 : ℝ) ^ j * z) hΔ hlam_le1 hw)
          refine Finset.sum_congr rfl (fun ν₁ _ => Finset.sum_congr rfl (fun k _ =>
            Finset.sum_congr rfl (fun ν₂ _ => ?_)))
          rw [htw j z]
  have stepC : (∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y), Kmerge a lam N s Δ u / u)
      ≤ (J : ℝ) * (E * (1 + Real.log (Δ : ℝ))) := by
    have stepC1 : (∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y), Kmerge a lam N s Δ u / u)
        ≤ ∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y),
            (∑ j ∈ Finset.range J, Bint a N w ((2 : ℝ) ^ j * u)) / u := by
      rw [intervalIntegral.integral_of_le hAeY, intervalIntegral.integral_of_le hAeY]
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · change ∀ᵐ u ∂(volume.restrict (Set.Ioc (Y / (Δ : ℝ)) (Real.exp 1 * Y))),
            (0 : ℝ) ≤ Kmerge a lam N s Δ u / u
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall (fun u hu => div_nonneg
          (Finset.sum_nonneg (fun _ _ => Kfac_nonneg a lam N s _ _))
          (le_of_lt (lt_trans hApos hu.1)))
      · have hsum := IntervalIntegrable.sum (Finset.range J) (fun j _ =>
          intervalIntegrable_Bint_div (a := a) (N := N) (w := w) (c := (2 : ℝ) ^ j)
            hApos hAeY)
        simpa only [IntegrableOn, Finset.sum_fn, Finset.sum_div] using hsum.1
      · change ∀ᵐ u ∂(volume.restrict (Set.Ioc (Y / (Δ : ℝ)) (Real.exp 1 * Y))),
            Kmerge a lam N s Δ u / u
              ≤ (∑ j ∈ Finset.range J, Bint a N w ((2 : ℝ) ^ j * u)) / u
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall (fun u hu =>
          div_le_div_of_nonneg_right (hKmerge u) (le_of_lt (lt_trans hApos hu.1)))
    refine stepC1.trans ?_
    calc (∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y),
            (∑ j ∈ Finset.range J, Bint a N w ((2 : ℝ) ^ j * u)) / u)
        = ∑ j ∈ Finset.range J,
            ∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y), Bint a N w ((2 : ℝ) ^ j * u) / u := by
          rw [show (∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y),
                (∑ j ∈ Finset.range J, Bint a N w ((2 : ℝ) ^ j * u)) / u)
              = ∫ u in Y / (Δ : ℝ)..(Real.exp 1 * Y),
                  ∑ j ∈ Finset.range J, Bint a N w ((2 : ℝ) ^ j * u) / u from
            intervalIntegral.integral_congr (fun u _ => by rw [Finset.sum_div])]
          exact intervalIntegral.integral_finsetSum (fun j _ =>
            intervalIntegrable_Bint_div (a := a) (N := N) (w := w) (c := (2 : ℝ) ^ j)
              hApos hAeY)
      _ ≤ ∑ _j ∈ Finset.range J, E * (1 + Real.log (Δ : ℝ)) :=
          Finset.sum_le_sum (fun j hj =>
            smAvg_Bint_le a N w (Finset.mem_range.mp hj) hY hΔ hE hB')
      _ = (J : ℝ) * (E * (1 + Real.log (Δ : ℝ))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact stepA.trans (stepB.trans stepC)

/-! ### Measurability and boundedness of `Ksum` (as a function of `y`) -/

lemma Ksum_eq_ite (a lam : ℕ → ℝ) (N k : ℕ) (y sy : ℝ) :
    Ksum a lam N y sy k = ∑ b ∈ Finset.Icc 1 N,
      (if y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ sy ∧ b * k ≤ N
        then (ArithmeticFunction.moebius b : ℝ) * (a (b * k) * rhoOf lam (b * k)) else 0) := by
  rw [Ksum, Krange, Finset.sum_filter]

lemma measurable_Ksum (a lam : ℕ → ℝ) (N k : ℕ) {s : ℝ} (hs : 0 < s) :
    Measurable (fun y : ℝ => Ksum a lam N y (s * y) k) := by
  have h : (fun y : ℝ => Ksum a lam N y (s * y) k)
      = fun y => ∑ b ∈ Finset.Icc 1 N,
          (if y < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ s * y ∧ b * k ≤ N
            then (ArithmeticFunction.moebius b : ℝ) * (a (b * k) * rhoOf lam (b * k))
            else 0) := by
    funext y; rw [Ksum_eq_ite]
  rw [h]
  exact Finset.measurable_sum _ (fun b _ =>
    measurable_ite_mul _ b hs (b * k ≤ N))

lemma abs_Ksum_le (a lam : ℕ → ℝ) (N k : ℕ) (y sy : ℝ) :
    |Ksum a lam N y sy k| ≤ ∑ b ∈ Finset.Icc 1 N, |a (b * k) * rhoOf lam (b * k)| := by
  rw [Ksum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun b _ => ?_)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => abs_nonneg _))
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_cast_le_one b)

lemma intervalIntegrable_Ksum_div (a lam : ℕ → ℝ) (N k : ℕ) {s : ℝ} (hs : 0 < s)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    IntervalIntegrable (fun y => |Ksum a lam N y (s * y) k| / y) volume p q :=
  intervalIntegrable_div_of_bound hp hpq (measurable_Ksum a lam N k hs).abs _
    (fun y => by rw [abs_abs]; exact abs_Ksum_le a lam N k y (s * y))

/-! ### The smoothed `S₂` bound (7.2) -/

/-- **§7, the smoothed bound on `S₂`**: the `y`-average of `S₂` is bounded by `(log N)` times the
(B′)-bound of `smAvg_abs_Ksum_le`.  This is the form in which §7 is used in the companion's
Theorem 1 (the smoothing over `z` does nothing, since the bound is independent of `z`). -/
theorem abs_smAvg_S2_le (a lam : ℕ → ℝ) (N : ℕ) {w : ℕ → ℝ} {s E Y : ℝ} {J : ℕ} {Δ : ℕ}
    {z : ℝ} (hs : s = (2 : ℝ) ^ J) (hY : 0 < Y) (hΔ : 1 ≤ Δ) (hw0 : ∀ ℓ, 0 ≤ w ℓ)
    (hE : 0 ≤ E) (hN : 1 ≤ N)
    (hw : ∀ ℓ, 1 ≤ ℓ → ((ℓ.divisors.card : ℝ)) ^ 2 ≤ w ℓ)
    (hlam_supp : ∀ ν, Δ < ν → lam ν = 0)
    (hlam_le1 : ∀ ν, |lam ν| ≤ 1)
    (ha : ∀ n, ¬ Squarefree n → a n = 0)
    (hB : BprimeWindow a N w E (Y / (Δ : ℝ)) (s * (Real.exp 1 * Y))) :
    (∫ y in Y..(Real.exp 1 * Y), |S2 a lam N y z (s * y)| / y)
      ≤ Real.log (N : ℝ) * ((J : ℝ) * (E * (1 + Real.log (Δ : ℝ)))) := by
  have hspos : 0 < s := by rw [hs]; positivity
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNpos
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hApos : 0 < Y / (Δ : ℝ) := div_pos hY hΔpos
  have hYle : Y ≤ Real.exp 1 * Y :=
    le_mul_of_one_le_left hY.le (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1))
  have hcongr : (∫ y in Y..(Real.exp 1 * Y), |S2 a lam N y z (s * y)| / y)
      = ∫ y in Y..(Real.exp 1 * Y), |S2 a lam N y z (s * y) / y| := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    have hy0 : (0 : ℝ) ≤ y := by
      have h1 := hy.1
      rw [min_eq_left hYle] at h1
      linarith [hY]
    rw [abs_div, abs_of_nonneg hy0]
  rw [hcongr]
  have hstep : (∫ y in Y..(Real.exp 1 * Y), |S2 a lam N y z (s * y) / y|)
      ≤ ∫ y in Y..(Real.exp 1 * Y),
          Real.log (N : ℝ) *
            ∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k| / y := by
    rw [intervalIntegral.integral_of_le hYle, intervalIntegral.integral_of_le hYle]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · change ∀ᵐ y ∂(volume.restrict (Set.Ioc Y (Real.exp 1 * Y))),
          (0 : ℝ) ≤ |S2 a lam N y z (s * y) / y|
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun y _ => abs_nonneg _)
    · have hsum := IntervalIntegrable.sum (Finset.Icc 1 N) (fun k _ =>
        intervalIntegrable_Ksum_div a lam N k hspos (p := Y)
          (q := Real.exp 1 * Y) hY hYle)
      have h2 := hsum.const_mul (Real.log (N : ℝ))
      simpa only [IntegrableOn, Finset.sum_fn, Finset.mul_sum] using h2.1
    · change ∀ᵐ y ∂(volume.restrict (Set.Ioc Y (Real.exp 1 * Y))),
          |S2 a lam N y z (s * y) / y|
            ≤ Real.log (N : ℝ) *
                ∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k| / y
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      have hy0 : 0 < y := lt_trans hY hy.1
      rw [abs_div, abs_of_pos hy0]
      calc |S2 a lam N y z (s * y)| / y
          ≤ (Real.log (N : ℝ) *
              ∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k|) / y :=
            div_le_div_of_nonneg_right (abs_S2_le_log_Ksum a lam N y z (s * y)) hy0.le
        _ = Real.log (N : ℝ) *
              ∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k| / y := by
            simp only [Finset.sum_div, mul_div_assoc]
  refine hstep.trans ?_
  have hstep2 : (∫ y in Y..(Real.exp 1 * Y),
        Real.log (N : ℝ) *
          ∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k| / y)
      = Real.log (N : ℝ) *
        ∫ y in Y..(Real.exp 1 * Y),
          (∑ k ∈ Finset.Icc 1 N, |Ksum a lam N y (s * y) k|) / y := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [Finset.sum_div]
  rw [hstep2]
  exact mul_le_mul_of_nonneg_left
    (smAvg_abs_Ksum_le a lam N hs hY hΔ hw0 hE hw hlam_supp hlam_le1 ha hB) hlogN

end

end Submission.ASP
