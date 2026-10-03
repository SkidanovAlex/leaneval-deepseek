/-
# `Submission.Work.FIChain.RhoWin2Integrable`

Interval integrability of the `ρ`-window integrands `Wmain`, `Wtail` and `Wall` of
`Submission.Work.FIChain.RhoWin2Defs`.

All three integrands are finite sums of `|Xpg x Pz c' σ u|`.  The function `Xpg` is a finite sum
over `n ≤ x` of `μ(n)·γ_σ(n)·ã(c'n)`, so

* as a function of `σ` it is a finite linear combination of step functions
  `σ ↦ (if d·d₁ ≤ σ then 1 else 0)` (this is where the `1/σ` of the integration comes from);
* as a function of `u` it is a finite linear combination of the interval indicators of the windows
  `(u/n₁, 2u/n₁]`.

It is therefore measurable (jointly in `(σ,u)`), and uniformly bounded by the constant `Wmass`,
which is the sum of `τ(n)|ã(c'n)|` over the full range of indices.  A measurable function that is
bounded on the (locally finite) integration interval is interval integrable; the extra factor
`1/s` (resp. `1/t`) is harmless because the integration range stays to the right of `0`
(`1 ≤ C`, `0 < lo`).
-/
import Mathlib
import Submission.Work.FIChain.RhoWin2Defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Measurable and uniformly bounded implies interval integrable -/

theorem intervalIntegrable_of_measurable_of_le {f : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hf : Measurable f) (hb : ∀ x ∈ Set.Ioc a b, |f x| ≤ M) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (s_finite := (measure_Ioc_lt_top (a := a) (b := b)).ne)
    (f_mble := hf.aestronglyMeasurable) (M := M) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => by
    rw [Real.norm_eq_abs]; exact hb x hx)

/-! ## 2. Pointwise bounds for `Xpg` -/

/-- `|γ_σ(n)| ≤ τ(n)`. -/
theorem abs_gammaTrunc_le_card (σ : ℝ) (n : ℕ) :
    |Work.FIPlan.gammaTrunc σ n| ≤ (n.divisors.card : ℝ) := by
  rw [Work.FIPlan.gammaTrunc]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ σ),
      |(ArithmeticFunction.moebius d : ℝ)| ≤ (1 : ℝ) := fun d _ => by
    have := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast this
  calc ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ σ),
        |(ArithmeticFunction.moebius d : ℝ)|
      ≤ ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ σ), (1 : ℝ) :=
        Finset.sum_le_sum h1
    _ = (((n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ σ)).card : ℕ) : ℝ) := by simp
    _ ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- Uniform bound for the window sum: `|Xpg x Pz c σ u|` is at most the full unsigned mass
`∑_{n ≤ x} τ(n)|ã(cn)|`, independently of `σ` and `u`. -/
theorem abs_Xpg_le_K (x Pz c : ℕ) (σ u : ℝ) :
    |Xpg x Pz c σ u| ≤ ∑ n ∈ Finset.Icc 1 x,
      (n.divisors.card : ℝ) * |atilc (c * n)| := by
  rw [Xpg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun n _ => ?_)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)))
  rw [abs_mul, abs_mul]
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := n); exact_mod_cast this
  calc |(ArithmeticFunction.moebius n : ℝ)| * |Work.FIPlan.gammaTrunc σ n| * |atilc (c * n)|
      ≤ 1 * (n.divisors.card : ℝ) * |atilc (c * n)| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hμ (abs_gammaTrunc_le_card σ n) (abs_nonneg _) (by norm_num))
          (abs_nonneg _)
    _ = (n.divisors.card : ℝ) * |atilc (c * n)| := by ring

/-! ## 3. The uniform mass bound `Wmass` -/

/-- The uniform mass bound dominating `Wmain`, `Wtail` and `Wall`. -/
def Wmass (x Pz : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 x, (c.divisors.card : ℝ) ^ 2 *
    ∑ n₁ ∈ (ProdP Pz).divisors, ∑ d₁ ∈ n₁.divisors,
      ∑ n ∈ Finset.Icc 1 x, (n.divisors.card : ℝ) * |atilc ((c * n₁) * n)|

theorem Wmass_nonneg (x Pz : ℕ) : 0 ≤ Wmass x Pz := by
  rw [Wmass]
  refine Finset.sum_nonneg (fun c _ => mul_nonneg (by positivity) ?_)
  refine Finset.sum_nonneg (fun n₁ _ => Finset.sum_nonneg (fun d₁ _ => ?_))
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))

/-- The `c`-summand bound: the `n₁`-sum restricted to any sub-collection `S` of the divisors of
`Π` is dominated by the full mass term. -/
theorem Wcore_le (x Pz c : ℕ) (S : Finset ℕ) (hS : S ⊆ (ProdP Pz).divisors) (s t : ℝ) :
    ∑ n₁ ∈ S, ∑ d₁ ∈ n₁.divisors, |Xpg x Pz (c * n₁) (s / d₁) (t / n₁)|
      ≤ ∑ n₁ ∈ (ProdP Pz).divisors, ∑ d₁ ∈ n₁.divisors,
          ∑ n ∈ Finset.Icc 1 x, (n.divisors.card : ℝ) * |atilc ((c * n₁) * n)| := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg hS
    (fun i _ _ => Finset.sum_nonneg (fun d _ => abs_nonneg _))).trans ?_
  refine Finset.sum_le_sum (fun n₁ _ => ?_)
  exact Finset.sum_le_sum (fun d₁ _ => abs_Xpg_le_K x Pz (c * n₁) (s / d₁) (t / n₁))

theorem abs_Wmain_le_Wmass (x Pz : ℕ) (Δ s t : ℝ) : |Wmain x Pz Δ s t| ≤ Wmass x Pz := by
  rw [Wmain, Wmass]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun c _ => ?_))
  have hTnn : 0 ≤ ∑ n₁ ∈ (ProdP Pz).divisors.filter (fun n₁ : ℕ => (n₁ : ℝ) ≤ Δ),
      ∑ d₁ ∈ n₁.divisors, |Xpg x Pz (c * n₁) (s / d₁) (t / n₁)| :=
    Finset.sum_nonneg (fun n₁ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c.divisors.card : ℝ) ^ 2),
    abs_of_nonneg hTnn]
  exact mul_le_mul_of_nonneg_left
    (Wcore_le x Pz c _ (Finset.filter_subset _ _) s t) (by positivity)

theorem abs_Wtail_le_Wmass (x Pz : ℕ) (Δ s t : ℝ) : |Wtail x Pz Δ s t| ≤ Wmass x Pz := by
  rw [Wtail, Wmass]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun c _ => ?_))
  have hTnn : 0 ≤ ∑ n₁ ∈ (ProdP Pz).divisors.filter (fun n₁ : ℕ => Δ < (n₁ : ℝ)),
      ∑ d₁ ∈ n₁.divisors, |Xpg x Pz (c * n₁) (s / d₁) (t / n₁)| :=
    Finset.sum_nonneg (fun n₁ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c.divisors.card : ℝ) ^ 2),
    abs_of_nonneg hTnn]
  exact mul_le_mul_of_nonneg_left
    (Wcore_le x Pz c _ (Finset.filter_subset _ _) s t) (by positivity)

theorem abs_Wall_le_Wmass (x Pz : ℕ) (s t : ℝ) : |Wall x Pz s t| ≤ Wmass x Pz := by
  rw [Wall, Wmass]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun c _ => ?_))
  have hTnn : 0 ≤ ∑ n₁ ∈ (ProdP Pz).divisors,
      ∑ d₁ ∈ n₁.divisors, |Xpg x Pz (c * n₁) (s / d₁) (t / n₁)| :=
    Finset.sum_nonneg (fun n₁ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (c.divisors.card : ℝ) ^ 2),
    abs_of_nonneg hTnn]
  exact mul_le_mul_of_nonneg_left
    (Wcore_le x Pz c _ (Finset.Subset.refl _) s t) (by positivity)

/-! ## 4. Measurability -/

/-- Measurability of the reparametrised window sum `p ↦ Xpg x Pz c (p.1/d₁) (p.2/n₁)`. -/
theorem measurable_Xpg_div (x Pz : ℕ) (c₁ d₁ n₁ : ℕ) :
    Measurable (fun p : ℝ × ℝ => Xpg x Pz c₁ (p.1 / (d₁ : ℝ)) (p.2 / (n₁ : ℝ))) := by
  have h : Measurable ((fun q : ℝ × ℝ => Xpg x Pz c₁ q.1 q.2) ∘
      (fun p : ℝ × ℝ => (p.1 / (d₁ : ℝ), p.2 / (n₁ : ℝ)))) :=
    (measurable_Xpg_pair x Pz c₁).comp
      ((measurable_fst.div_const (d₁ : ℝ)).prodMk (measurable_snd.div_const (n₁ : ℝ)))
  convert h using 1
  ext p
  rfl

/-- Joint measurability in `(σ, u) = (p.1, p.2)` of the generic `Π`-split window sum. -/
theorem measurable_Wfg_joint (x Pz : ℕ) (Sel : ℕ → Finset ℕ) :
    Measurable (fun p : ℝ × ℝ =>
      ∑ c ∈ Finset.Icc 1 x, (c.divisors.card : ℝ) ^ 2 *
        ∑ n₁ ∈ Sel c, ∑ d₁ ∈ n₁.divisors,
          |Xpg x Pz (c * n₁) (p.1 / (d₁ : ℝ)) (p.2 / (n₁ : ℝ))|) := by
  refine Finset.measurable_sum _ (fun c _ => Measurable.const_mul ?_ _)
  refine Finset.measurable_sum _ (fun n₁ _ => ?_)
  refine Finset.measurable_sum _ (fun d₁ _ => ?_)
  exact (measurable_Xpg_div x Pz (c * n₁) d₁ n₁).abs

theorem measurable_Wmain_joint (x Pz : ℕ) (Δ : ℝ) :
    Measurable (fun p : ℝ × ℝ => Wmain x Pz Δ p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => Wmain x Pz Δ p.1 p.2) = fun p : ℝ × ℝ =>
      ∑ c ∈ Finset.Icc 1 x, (c.divisors.card : ℝ) ^ 2 *
        ∑ n₁ ∈ (ProdP Pz).divisors.filter (fun n₁ : ℕ => (n₁ : ℝ) ≤ Δ),
          ∑ d₁ ∈ n₁.divisors,
            |Xpg x Pz (c * n₁) (p.1 / (d₁ : ℝ)) (p.2 / (n₁ : ℝ))| := by
    funext p; rw [Wmain]
  rw [h]
  exact measurable_Wfg_joint x Pz _

theorem measurable_Wtail_joint (x Pz : ℕ) (Δ : ℝ) :
    Measurable (fun p : ℝ × ℝ => Wtail x Pz Δ p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => Wtail x Pz Δ p.1 p.2) = fun p : ℝ × ℝ =>
      ∑ c ∈ Finset.Icc 1 x, (c.divisors.card : ℝ) ^ 2 *
        ∑ n₁ ∈ (ProdP Pz).divisors.filter (fun n₁ : ℕ => Δ < (n₁ : ℝ)),
          ∑ d₁ ∈ n₁.divisors,
            |Xpg x Pz (c * n₁) (p.1 / (d₁ : ℝ)) (p.2 / (n₁ : ℝ))| := by
    funext p; rw [Wtail]
  rw [h]
  exact measurable_Wfg_joint x Pz _

theorem measurable_Wall_joint (x Pz : ℕ) :
    Measurable (fun p : ℝ × ℝ => Wall x Pz p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => Wall x Pz p.1 p.2) = fun p : ℝ × ℝ =>
      ∑ c ∈ Finset.Icc 1 x, (c.divisors.card : ℝ) ^ 2 *
        ∑ n₁ ∈ (ProdP Pz).divisors,
          ∑ d₁ ∈ n₁.divisors,
            |Xpg x Pz (c * n₁) (p.1 / (d₁ : ℝ)) (p.2 / (n₁ : ℝ))| := by
    funext p; rw [Wall]
  rw [h]
  exact measurable_Wfg_joint x Pz _

theorem measurable_Wmain_s (x Pz : ℕ) (Δ t : ℝ) :
    Measurable (fun s : ℝ => Wmain x Pz Δ s t) := by
  have h : Measurable ((fun p : ℝ × ℝ => Wmain x Pz Δ p.1 p.2) ∘ (fun s : ℝ => (s, t))) :=
    (measurable_Wmain_joint x Pz Δ).comp
      (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ => t)))
  convert h using 1
  ext s
  rfl

theorem measurable_Wtail_s (x Pz : ℕ) (Δ t : ℝ) :
    Measurable (fun s : ℝ => Wtail x Pz Δ s t) := by
  have h : Measurable ((fun p : ℝ × ℝ => Wtail x Pz Δ p.1 p.2) ∘ (fun s : ℝ => (s, t))) :=
    (measurable_Wtail_joint x Pz Δ).comp
      (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ => t)))
  convert h using 1
  ext s
  rfl

/-- Measurability of the `s`-integral as a function of `t`. -/
theorem measurable_integral_div_s (C : ℝ) (hC : 1 ≤ C) {g : ℝ → ℝ → ℝ}
    (hg : Measurable (fun p : ℝ × ℝ => g p.1 p.2)) :
    Measurable (fun t : ℝ => ∫ s in (1 : ℝ)..C, g s t / s) := by
  have hjoint : StronglyMeasurable (fun p : ℝ × ℝ => g p.2 p.1 / p.2) :=
    ((hg.comp measurable_swap).div measurable_snd).stronglyMeasurable
  have h := StronglyMeasurable.integral_prod_right
    (ν := (volume : Measure ℝ).restrict (Set.Ioc (1 : ℝ) C))
    (f := fun t s : ℝ => g s t / s) hjoint
  simpa only [intervalIntegral.integral_of_le hC] using h.measurable

theorem measurable_integral_Wmain (x Pz : ℕ) (Δ C : ℝ) (hC : 1 ≤ C) :
    Measurable (fun t : ℝ => ∫ s in (1 : ℝ)..C, Wmain x Pz Δ s t / s) :=
  measurable_integral_div_s C hC (measurable_Wmain_joint x Pz Δ)

theorem measurable_integral_Wtail (x Pz : ℕ) (Δ C : ℝ) (hC : 1 ≤ C) :
    Measurable (fun t : ℝ => ∫ s in (1 : ℝ)..C, Wtail x Pz Δ s t / s) :=
  measurable_integral_div_s C hC (measurable_Wtail_joint x Pz Δ)

theorem measurable_integral_Wall (x Pz : ℕ) (C : ℝ) (hC : 1 ≤ C) :
    Measurable (fun t : ℝ => ∫ s in (1 : ℝ)..C, Wall x Pz s t / s) :=
  measurable_integral_div_s C hC (measurable_Wall_joint x Pz)

/-! ## 5. The target -/

theorem RhoWin2Integrable (x Pz : ℕ) (Δ lo hi C : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi) (hC : 1 ≤ C) :
    (∀ t : ℝ, IntervalIntegrable (fun s : ℝ => Wmain x Pz Δ s t / s) volume 1 C) ∧
    (∀ t : ℝ, IntervalIntegrable (fun s : ℝ => Wtail x Pz Δ s t / s) volume 1 C) ∧
    IntervalIntegrable (fun t : ℝ => (∫ s in (1 : ℝ)..C, Wmain x Pz Δ s t / s) / t) volume lo hi ∧
    IntervalIntegrable (fun t : ℝ => (∫ s in (1 : ℝ)..C, Wtail x Pz Δ s t / s) / t) volume lo hi ∧
    IntervalIntegrable (fun t : ℝ => (∫ s in (1 : ℝ)..C, Wall x Pz s t / s) / t) volume lo hi := by
  have hWnn : 0 ≤ Wmass x Pz := Wmass_nonneg x Pz
  -- the `1/s` factor is harmless on `(1, C]`
  have hsbound : ∀ (f : ℝ → ℝ), (∀ s, |f s| ≤ Wmass x Pz) →
      ∀ s ∈ Set.Ioc (1 : ℝ) C, |f s / s| ≤ Wmass x Pz := by
    intro f hf s hs
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one (le_of_lt hs.1)
    rw [abs_div, abs_of_pos hs0]
    have h2 : Wmass x Pz / s ≤ Wmass x Pz := by
      rw [div_le_iff₀ hs0]
      nlinarith [hWnn, le_of_lt hs.1]
    exact (div_le_div_of_nonneg_right (hf s) (le_of_lt hs0)).trans h2
  -- bound on the inner `s`-integral
  have hintbound : ∀ (f : ℝ → ℝ), (∀ s, |f s| ≤ Wmass x Pz) →
      |∫ s in (1 : ℝ)..C, f s / s| ≤ Wmass x Pz * (C - 1) := by
    intro f hf
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 : ℝ)) (b := C) (C := Wmass x Pz) (f := fun s : ℝ => f s / s)
      (fun s hs => by
        rw [Set.uIoc_of_le hC] at hs
        rw [Real.norm_eq_abs]
        exact hsbound f hf s hs)
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ C - 1)] at h
  -- the `1/t` factor is harmless on `(lo, hi]`
  have htbound : ∀ (F : ℝ → ℝ), (∀ t, |F t| ≤ Wmass x Pz * (C - 1)) →
      ∀ t ∈ Set.Ioc lo hi, |F t / t| ≤ Wmass x Pz * (C - 1) / lo := by
    intro F hF t ht
    have ht0 : 0 < t := lt_of_lt_of_le hlo (le_of_lt ht.1)
    have hMnn : 0 ≤ Wmass x Pz * (C - 1) := mul_nonneg hWnn (by linarith)
    rw [abs_div, abs_of_pos ht0]
    exact (div_le_div_of_nonneg_right (hF t) (le_of_lt ht0)).trans
      (div_le_div_of_nonneg_left hMnn hlo (le_of_lt ht.1))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact intervalIntegrable_of_measurable_of_le hC
      ((measurable_Wmain_s x Pz Δ t).div measurable_id)
      (hsbound (fun s => Wmain x Pz Δ s t) (fun s => abs_Wmain_le_Wmass x Pz Δ s t))
  · intro t
    exact intervalIntegrable_of_measurable_of_le hC
      ((measurable_Wtail_s x Pz Δ t).div measurable_id)
      (hsbound (fun s => Wtail x Pz Δ s t) (fun s => abs_Wtail_le_Wmass x Pz Δ s t))
  · exact intervalIntegrable_of_measurable_of_le hlohi
      ((measurable_integral_Wmain x Pz Δ C hC).div measurable_id)
      (htbound (fun t => ∫ s in (1 : ℝ)..C, Wmain x Pz Δ s t / s)
        (fun t => hintbound (fun s => Wmain x Pz Δ s t)
          (fun s => abs_Wmain_le_Wmass x Pz Δ s t)))
  · exact intervalIntegrable_of_measurable_of_le hlohi
      ((measurable_integral_Wtail x Pz Δ C hC).div measurable_id)
      (htbound (fun t => ∫ s in (1 : ℝ)..C, Wtail x Pz Δ s t / s)
        (fun t => hintbound (fun s => Wtail x Pz Δ s t)
          (fun s => abs_Wtail_le_Wmass x Pz Δ s t)))
  · exact intervalIntegrable_of_measurable_of_le hlohi
      ((measurable_integral_Wall x Pz C hC).div measurable_id)
      (htbound (fun t => ∫ s in (1 : ℝ)..C, Wall x Pz s t / s)
        (fun t => hintbound (fun s => Wall x Pz s t)
          (fun s => abs_Wall_le_Wmass x Pz s t)))

end

end Work.FIChain
