/-
  Companion paper ("Asymptotic sieve for primes"), §7 (`S₂`): the *integrated* estimate.

  This file contains the analytic core of §7: the smoothing operator `∫_Y^{eY} dy/y`
  (of total mass `1`) is used to remove the dependence of the inner range on the divisor
  `ν₁` of `b`, after which the `(ν₁, ν₂, k)`-triples can be merged along `ℓ = ν₁k`
  (multiplicity at most `τ(ℓ)²`) and the bilinear hypothesis (B′) — in the form
  `∑_m w(m)|∑_{t < n ≤ 2t} μ(n)a(mn)| ≤ E` — can be applied at each dyadic scale.
-/
import Mathlib
import Submission.ASP.S7b
import Submission.Commons.Analysis.Asymptotics.integral_one_div_Ioc_exp_mul

namespace Submission.ASP

open Finset MeasureTheory
open scoped Interval

noncomputable section

/-! ### Measurability of `Xsum` -/

/-- `|μ b| ≤ 1` (as a real number). -/
lemma abs_moebius_cast_le_one (b : ℕ) :
    |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
  have h := ArithmeticFunction.abs_moebius_le_one (n := b)
  exact_mod_cast h

/-- An `if`-expression whose condition is a pair of linear inequalities in `u` is measurable. -/
lemma measurable_ite_mul (c : ℝ) (b : ℕ) {s : ℝ} (hs : 0 < s) (P : Prop) [Decidable P] :
    Measurable (fun u : ℝ => if u < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ s * u ∧ P then c else 0) := by
  have hEq : (fun u : ℝ =>
        if u < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ s * u ∧ P then c else 0)
      = fun u => (Set.Iio (((b : ℕ) : ℝ)) ∩ Set.Ici (((b : ℕ) : ℝ) / s)).indicator
          (fun _ => (if P then c else 0)) u := by
    funext u
    rw [Set.indicator_apply]
    by_cases hmem : u ∈ Set.Iio (((b : ℕ) : ℝ)) ∩ Set.Ici (((b : ℕ) : ℝ) / s)
    · rw [if_pos hmem]
      obtain ⟨h1, h2⟩ := hmem
      rw [Set.mem_Iio] at h1
      rw [Set.mem_Ici, div_le_iff₀ hs] at h2
      have h2' : ((b : ℕ) : ℝ) ≤ s * u := by linarith
      by_cases hP : P
      · rw [if_pos hP, if_pos ⟨h1, h2', hP⟩]
      · rw [if_neg hP, if_neg (fun h => hP h.2.2)]
    · rw [if_neg hmem]
      exact if_neg (fun h => hmem ⟨h.1, (div_le_iff₀ hs).mpr (by linarith [h.2.1])⟩)
  rw [hEq]
  exact Measurable.indicator measurable_const (measurableSet_Iio.inter measurableSet_Ici)

/-- `u ↦ Xsum a N ℓ u (s·u)` is measurable (write the filter as a finite sum of indicators). -/
lemma measurable_Xsum (a : ℕ → ℝ) (N ℓ : ℕ) {s : ℝ} (hs : 0 < s) :
    Measurable (fun u : ℝ => Xsum a N ℓ u (s * u)) := by
  have h : (fun u : ℝ => Xsum a N ℓ u (s * u))
      = fun u => ∑ b ∈ Finset.Icc 1 N,
          (if u < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ s * u ∧ b * ℓ ≤ N
            then (ArithmeticFunction.moebius b : ℝ) * a (b * ℓ) else 0) := by
    funext u
    rw [Xsum, Finset.sum_filter]
  rw [h]
  exact Finset.measurable_sum _ (fun b _ => measurable_ite_mul _ b hs _)

/-! ### Integrability of the (B′)-integrand -/

/-- A measurable function divided by `u` is interval-integrable on `[p,q]`, `0 < p ≤ q`,
as soon as it is bounded there. -/
lemma intervalIntegrable_div_Ioc {G : ℝ → ℝ} (hG : Measurable G) {p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) (C : ℝ) (hC : ∀ u ∈ Set.Icc p q, |G u| ≤ C) :
    IntervalIntegrable (fun u => G u / u) volume p q := by
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (C / p) ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact (hG.div measurable_id).aestronglyMeasurable
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun u hu => ?_
      have hu0 : 0 < u := lt_trans hp hu.1
      have hCu : |G u| ≤ C := hC u (Set.mem_Icc.mpr ⟨le_of_lt hu.1, hu.2⟩)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hu0]
      refine (div_le_div_of_nonneg_left (abs_nonneg _) hp (le_of_lt hu.1)).trans ?_
      rw [div_le_iff₀ hp, div_mul_cancel₀ _ hp.ne']
      exact hCu
  · rw [Set.Ioc_eq_empty_of_le hpq]
    exact integrableOn_empty

/-- A measurable function that is bounded everywhere is interval-integrable (both orientations of
the interval, since `IntervalIntegrable` is a conjunction over `Ioc p q` and `Ioc q p`). -/
lemma intervalIntegrable_of_bound {f : ℝ → ℝ} {p q : ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ t, |f t| ≤ C) : IntervalIntegrable f volume p q := by
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.IntegrableOn.of_bound ?_ hf.aestronglyMeasurable C ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact Filter.Eventually.of_forall fun t => by
        simpa only [Real.norm_eq_abs] using hC t
  · refine MeasureTheory.IntegrableOn.of_bound ?_ hf.aestronglyMeasurable C ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact Filter.Eventually.of_forall fun t => by
        simpa only [Real.norm_eq_abs] using hC t

/-- The (B′)-integrand `u ↦ |Xsum a N ℓ u (s·u)|/u` is interval-integrable on `[p,q]`. -/
lemma intervalIntegrable_Xsum_div (a : ℕ → ℝ) (N ℓ : ℕ) {s : ℝ} (hs : 0 < s) {p q : ℝ}
    (hp : 0 < p) (hpq : p ≤ q) :
    IntervalIntegrable (fun u => |Xsum a N ℓ u (s * u)| / u) volume p q := by
  refine intervalIntegrable_div_Ioc (measurable_Xsum a N ℓ hs).abs hp hpq
    (∑ b ∈ Finset.Icc 1 N, |a (b * ℓ)|) (fun u _ => ?_)
  rw [abs_of_nonneg (abs_nonneg _)]
  simp only [Xsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun b _ => ?_)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => abs_nonneg _))
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_cast_le_one b)

/-! ### The change of variables `y ↦ y/c` -/

/-- `∫_a^b Φ(y/c)/c dy = ∫_{a/c}^{b/c} Φ(u) du`. -/
lemma integral_comp_div_div {Φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (a b : ℝ) :
    (∫ y in a..b, Φ (y / c) / c) = ∫ u in a / c..b / c, Φ u := by
  have h : (fun y => Φ (y / c) / c) = fun y => (1 / c) * Φ (y / c) := by
    funext y; ring
  rw [h, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div Φ hc.ne']
  rw [smul_eq_mul, ← mul_assoc, one_div, inv_mul_cancel₀ hc.ne', one_mul]

/-! ### The merge step: grouping `(ν₁,k,ν₂)` by `ℓ = ν₁k` -/

/-- **The merge step of §7**: for fixed `u` the summand depends on the triple `(ν₁,k,ν₂)` only
through `ℓ = ν₁k`, and each fibre has multiplicity at most `τ(ℓ)² ≤ w ℓ`. -/
lemma sum_merge_le (a : ℕ → ℝ) (lam : ℕ → ℝ) (N Δ : ℕ) (w : ℕ → ℝ) (u : ℝ)
    (hlam_le1 : ∀ ν, |lam ν| ≤ 1)
    (hw : ∀ ℓ, 1 ≤ ℓ → ((ℓ.divisors.card : ℝ)) ^ 2 ≤ w ℓ) :
    (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
        |lam (ν₁ * ν₂)| * |Xsum a N (ν₁ * k) u (2 * u)|)
      ≤ ∑ ℓ ∈ Finset.Icc 1 (Δ * N), w ℓ * |Xsum a N ℓ u (2 * u)| := by
  classical
  set XX : ℕ → ℝ := fun ℓ => |Xsum a N ℓ u (2 * u)| with hXX
  have hXX0 : ∀ ℓ, 0 ≤ XX ℓ := fun ℓ => abs_nonneg _
  -- ## Step 1: collapse to a single sum over pairs `(ν₁,k)`
  have step1 : (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
        |lam (ν₁ * ν₂)| * XX (ν₁ * k))
      = ∑ p ∈ (Finset.Icc 1 Δ).product (Finset.Icc 1 N),
          (∑ ν₂ ∈ p.2.divisors, |lam (p.1 * ν₂)|) * XX (p.1 * p.2) := by
    have h1 : (∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N, ∑ ν₂ ∈ k.divisors,
          |lam (ν₁ * ν₂)| * XX (ν₁ * k))
        = ∑ ν₁ ∈ Finset.Icc 1 Δ, ∑ k ∈ Finset.Icc 1 N,
            (∑ ν₂ ∈ k.divisors, |lam (ν₁ * ν₂)|) * XX (ν₁ * k) := by
      refine Finset.sum_congr rfl (fun ν₁ _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [Finset.sum_mul]
    rw [h1, Finset.product_eq_sprod, Finset.sum_product]
  -- ## Step 2: bound the inner `ν₂`-sum by `τ(p.1 p.2)`
  have step2 : (∑ p ∈ (Finset.Icc 1 Δ).product (Finset.Icc 1 N),
          (∑ ν₂ ∈ p.2.divisors, |lam (p.1 * ν₂)|) * XX (p.1 * p.2))
      ≤ ∑ p ∈ (Finset.Icc 1 Δ).product (Finset.Icc 1 N),
          ((p.1 * p.2).divisors.card : ℝ) * XX (p.1 * p.2) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    refine mul_le_mul_of_nonneg_right ?_ (hXX0 _)
    calc ∑ ν₂ ∈ p.2.divisors, |lam (p.1 * ν₂)| ≤ ∑ _ν₂ ∈ p.2.divisors, (1 : ℝ) :=
          Finset.sum_le_sum (fun ν₂ _ => hlam_le1 _)
      _ = (p.2.divisors.card : ℝ) := by simp
      _ ≤ ((p.1 * p.2).divisors.card : ℝ) := by
          have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
          have hp2 : 1 ≤ p.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).2).1
          have hne : p.1 * p.2 ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
          have hsub := Nat.divisors_subset_of_dvd hne (Nat.dvd_mul_left p.2 p.1)
          exact_mod_cast Finset.card_le_card hsub
  -- ## Step 3: regroup along `ℓ = p.1 p.2`
  have step3 : (∑ p ∈ (Finset.Icc 1 Δ).product (Finset.Icc 1 N),
          ((p.1 * p.2).divisors.card : ℝ) * XX (p.1 * p.2))
      ≤ ∑ ℓ ∈ Finset.Icc 1 (Δ * N), w ℓ * XX ℓ := by
    have hmap : ∀ p ∈ (Finset.Icc 1 Δ).product (Finset.Icc 1 N),
        p.1 * p.2 ∈ Finset.Icc 1 (Δ * N) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.mp hp1
      obtain ⟨h2a, h2b⟩ := Finset.mem_Icc.mp hp2
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
        Nat.mul_le_mul h1b h2b⟩
    have hff : ∀ ℓ ∈ Finset.Icc 1 (Δ * N),
        (∑ p ∈ ((Finset.Icc 1 Δ).product (Finset.Icc 1 N)).filter
            (fun p => p.1 * p.2 = ℓ),
          ((p.1 * p.2).divisors.card : ℝ) * XX (p.1 * p.2))
          ≤ ((ℓ.divisors.card : ℝ)) ^ 2 * XX ℓ := by
      intro ℓ hℓ
      have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
      have hcard : ((((Finset.Icc 1 Δ).product (Finset.Icc 1 N)).filter
            (fun p => p.1 * p.2 = ℓ)).card : ℝ) ≤ (ℓ.divisors.card : ℝ) := by
        have hmaps : Set.MapsTo (fun p : ℕ × ℕ => p.1)
            ↑(((Finset.Icc 1 Δ).product (Finset.Icc 1 N)).filter (fun p => p.1 * p.2 = ℓ))
            ↑ℓ.divisors := by
          intro p hp
          obtain ⟨hpm, heq⟩ := Finset.mem_filter.mp hp
          exact Nat.mem_divisors.mpr ⟨⟨p.2, heq.symm⟩, by omega⟩
        have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1)
            ↑(((Finset.Icc 1 Δ).product (Finset.Icc 1 N)).filter (fun p => p.1 * p.2 = ℓ)) := by
          rintro p hp q hq hpq
          obtain ⟨hpm, heq⟩ := Finset.mem_filter.mp hp
          obtain ⟨hqm, heq'⟩ := Finset.mem_filter.mp hq
          have h1 : p.1 = q.1 := hpq
          have h2 : p.2 = q.2 := by
            have hpos : 0 < q.1 :=
              (Finset.mem_Icc.mp (Finset.mem_product.mp hqm).1).1
            refine Nat.mul_left_cancel hpos ?_
            calc q.1 * p.2 = p.1 * p.2 := by rw [h1]
              _ = q.1 * q.2 := by rw [heq, ← heq']
          exact Prod.ext h1 h2
        exact_mod_cast Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1) hmaps hinj
      have hsum : (∑ p ∈ ((Finset.Icc 1 Δ).product (Finset.Icc 1 N)).filter
            (fun p => p.1 * p.2 = ℓ),
          ((p.1 * p.2).divisors.card : ℝ) * XX (p.1 * p.2))
          = ((((Finset.Icc 1 Δ).product (Finset.Icc 1 N)).filter
              (fun p => p.1 * p.2 = ℓ)).card : ℝ) * (((ℓ.divisors.card : ℝ)) * XX ℓ) := by
        rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]),
          Finset.sum_const, nsmul_eq_mul]
      rw [hsum]
      have hT0 : (0 : ℝ) ≤ (ℓ.divisors.card : ℝ) := by positivity
      calc ((((Finset.Icc 1 Δ).product (Finset.Icc 1 N)).filter
              (fun p => p.1 * p.2 = ℓ)).card : ℝ) * (((ℓ.divisors.card : ℝ)) * XX ℓ)
          ≤ (ℓ.divisors.card : ℝ) * (((ℓ.divisors.card : ℝ)) * XX ℓ) :=
            mul_le_mul_of_nonneg_right hcard (mul_nonneg hT0 (hXX0 ℓ))
        _ = ((ℓ.divisors.card : ℝ)) ^ 2 * XX ℓ := by ring
    calc (∑ p ∈ (Finset.Icc 1 Δ).product (Finset.Icc 1 N),
            ((p.1 * p.2).divisors.card : ℝ) * XX (p.1 * p.2))
        = ∑ ℓ ∈ Finset.Icc 1 (Δ * N),
            ∑ p ∈ ((Finset.Icc 1 Δ).product (Finset.Icc 1 N)).filter
              (fun p => p.1 * p.2 = ℓ),
            ((ℓ.divisors.card : ℝ)) * XX ℓ := by
          rw [Finset.sum_fiberwise_of_maps_to' (g := fun p : ℕ × ℕ => p.1 * p.2) hmap
            (fun ℓ => ((ℓ.divisors.card : ℝ)) * XX ℓ)]
      _ = ∑ ℓ ∈ Finset.Icc 1 (Δ * N),
            ∑ p ∈ ((Finset.Icc 1 Δ).product (Finset.Icc 1 N)).filter
              (fun p => p.1 * p.2 = ℓ),
            ((p.1 * p.2).divisors.card : ℝ) * XX (p.1 * p.2) := by
          refine Finset.sum_congr rfl (fun ℓ _ => Finset.sum_congr rfl (fun p hp => ?_))
          rw [(Finset.mem_filter.mp hp).2]
      _ ≤ ∑ ℓ ∈ Finset.Icc 1 (Δ * N), w ℓ * XX ℓ :=
          Finset.sum_le_sum (fun ℓ hℓ => (hff ℓ hℓ).trans
            (mul_le_mul_of_nonneg_right (hw ℓ (Finset.mem_Icc.mp hℓ).1) (hXX0 ℓ)))
  calc _ ≤ _ := le_of_eq step1
    _ ≤ _ := step2
    _ ≤ _ := step3

/-! ### The (B′)-hypothesis, and the additivity of `Xsum` over adjacent intervals -/

/-- The companion's hypothesis (B′) on a window: `∑_m w(m)|Xsum a N m t (2t)| ≤ E` for every
`t ∈ [lo,hi]` (the bilinear form with `γ ≡ 1`, cf. (B2) with `C = 1`). -/
def BprimeWindow (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (E lo hi : ℝ) : Prop :=
  ∀ t : ℝ, lo ≤ t → t ≤ hi → (∑ m ∈ Finset.Icc 1 N, w m * |Xsum a N m t (2 * t)|) ≤ E

/-- `Xsum` written as a sum over a fixed index set with `u`-dependent `if`-factors. -/
lemma Xsum_eq_ite (a : ℕ → ℝ) (N ℓ : ℕ) (t u : ℝ) :
    Xsum a N ℓ t u = ∑ b ∈ (Finset.Icc 1 N).filter (fun b => b * ℓ ≤ N),
      (if t < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ u
        then (ArithmeticFunction.moebius b : ℝ) * a (b * ℓ) else 0) := by
  rw [Xsum]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun b _ => ?_)
  · ext b
    simp only [Finset.mem_filter]
    tauto
  · by_cases h : t < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ u <;> simp [h]

/-- `Xsum` is additive over adjacent intervals: `∫_t^w = ∫_t^v + ∫_v^w` at the level of the sums. -/
lemma Xsum_add_adjacent (a : ℕ → ℝ) (N ℓ : ℕ) {t v w : ℝ} (htv : t ≤ v) (hvw : v ≤ w) :
    Xsum a N ℓ t w = Xsum a N ℓ t v + Xsum a N ℓ v w := by
  rw [Xsum_eq_ite, Xsum_eq_ite, Xsum_eq_ite, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases h1 : ((b : ℕ) : ℝ) ≤ t
  · have h2 : ¬ (t < ((b : ℕ) : ℝ)) := not_lt.mpr h1
    have h3 : ¬ (v < ((b : ℕ) : ℝ)) := not_lt.mpr (le_trans h1 htv)
    have h4 : ¬ (t < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ w) := fun h => h2 h.1
    have h5 : ¬ (v < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ w) := fun h => h3 h.1
    simp [h4, h2, h5]
  · rw [not_le] at h1
    by_cases h2 : ((b : ℕ) : ℝ) ≤ v
    · have h3 : ¬ (v < ((b : ℕ) : ℝ)) := not_lt.mpr h2
      have h4 : t < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ w := ⟨h1, le_trans h2 hvw⟩
      have h5 : ¬ (v < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ w) := fun h => h3 h.1
      simp [h4, h1, h2, h5]
    · rw [not_le] at h2
      by_cases h3 : ((b : ℕ) : ℝ) ≤ w
      · have h4 : t < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ w := ⟨h1, h3⟩
        have h5 : ¬ (((b : ℕ) : ℝ) ≤ v) := not_le.mpr h2
        have h6 : v < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ w := ⟨h2, h3⟩
        simp [h4, h5, h6]
      · rw [not_le] at h3
        have h4 : ¬ (t < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ w) := fun h => not_le.mpr h3 h.2
        have h5 : ¬ (((b : ℕ) : ℝ) ≤ v) := not_le.mpr h2
        have h6 : ¬ (v < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ w) := fun h => not_le.mpr h3 h.2
        simp [h4, h5, h6]
/-- The dyadic splitting of the `Xsum` range, by induction on `J` (the intervals
`(2^j u, 2^{j+1} u]`, `j < J`, partition `(u, 2^J u]`). -/
lemma Xsum_dyadic (a : ℕ → ℝ) (N ℓ : ℕ) {u : ℝ} (hu : 0 < u) (J : ℕ) :
    Xsum a N ℓ u ((2 : ℝ) ^ J * u)
      = ∑ j ∈ Finset.range J, Xsum a N ℓ ((2 : ℝ) ^ j * u) ((2 : ℝ) ^ (j + 1) * u) := by
  induction J with
  | zero =>
      rw [Xsum, pow_zero, one_mul]
      refine Finset.sum_eq_zero (fun b hb => ?_)
      obtain ⟨-, hlt, hle, -⟩ := Finset.mem_filter.mp hb
      exact absurd (not_le.mpr hlt) (not_not.mpr hle)
  | succ J ih =>
      have hpu : 0 < (2 : ℝ) ^ J := pow_pos (by norm_num) J
      have h1J : (1 : ℝ) ≤ (2 : ℝ) ^ J := one_le_pow₀ (by norm_num)
      have hle : u ≤ (2 : ℝ) ^ J * u := by nlinarith
      have hle2 : (2 : ℝ) ^ J * u ≤ (2 : ℝ) ^ (J + 1) * u := by
        have h2 : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + 1) := by
          have : (1 : ℝ) ≤ 2 := by norm_num
          calc (2 : ℝ) ^ J = (2 : ℝ) ^ J * 1 := (mul_one _).symm
            _ ≤ (2 : ℝ) ^ J * 2 := by nlinarith
            _ = (2 : ℝ) ^ (J + 1) := by ring
        nlinarith
      rw [Finset.sum_range_succ, ← ih,
        Xsum_add_adjacent (a := a) (N := N) (ℓ := ℓ) (t := u) (v := (2 : ℝ) ^ J * u)
          (w := (2 : ℝ) ^ (J + 1) * u) hle hle2]
end

end Submission.ASP
